/*
 * worker_sandbox.c — confinement of the safe-pdf document worker (trusted, hand-written,
 * unverified; task 12.2b, Plan.md §6 Phase 12 "Restricted, stoppable document worker").
 *
 * Linked only into the `worker` executable (and, compiled a second time with
 * -DSAFEPDF_WORKER_PROBE, into the test-only `worker-probe` executable); see `lakefile.lean`.
 * The Lean side is `SafePdf.Shell.Worker.Sandbox`; the design is in `docs/safety.md` §2.4.
 *
 *   safepdf_worker_env_count : IO UInt32   — number of entries in `environ`
 *   safepdf_worker_confine   : IO String   — drop privileges for good, or fail (IO error);
 *                                            returns a one-line description of the mechanism
 *   safepdf_worker_fence     : UInt64 → UInt32 → IO String — task 12.3: the worker's memory
 *                                            ceiling (bytes) and per-request CPU time (s),
 *                                            outside Lean's cost model; called before confine
 *   safepdf_worker_arm_cpu   : IO Unit      — re-arm the CPU fence before a request
 *   safepdf_probe_tcp, safepdf_probe_listen — test-only, compiled only with
 *                                            -DSAFEPDF_WORKER_PROBE (`worker-probe`)
 *
 * macOS: `sandbox_init` with the SBPL profile below: `(deny default)` and nothing allowed
 *   at all. Read/write on already-open descriptors
 *   (stdin/stdout/stderr) is not a sandbox operation, so the request loop keeps working;
 *   every file open, network operation, process spawn and IPC lookup is refused.
 *   `sandbox_init` is deprecated but still works (Chromium's macOS sandbox uses the same SPI).
 * Linux: `PR_SET_NO_NEW_PRIVS`, then a seccomp-bpf allowlist installed on every thread
 *   (`SECCOMP_FILTER_FLAG_TSYNC`; the Lean runtime already runs threads). Unlisted syscalls
 *   fail with EPERM; a foreign architecture or an x32 syscall kills the process. UNTESTED:
 *   written on macOS without a Linux machine (ledger 12.2b).
 * Elsewhere, or when the Linux headers are missing: confinement fails, so the worker
 *   refuses to serve.
 *
 * Lean calling conventions (Lean 4.36): the IO world token is erased, so an `IO α` extern
 * with no explicit arguments is `f(void)`; results are IO result objects; `UInt32`
 * arguments and results are unboxed `uint32_t` inside the IO result (boxed with
 * `lean_box_uint32`).
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

static lean_obj_res safepdf_io_fail(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Number of environment entries. The client starts the worker with an empty environment;
 * the worker refuses to serve with a non-empty one (`Sandbox.prepare`). */
lean_obj_res safepdf_worker_env_count(void) {
  uint32_t n = 0;
  if (environ != NULL)
    for (char **e = environ; *e != NULL && n < UINT32_MAX; e++) n++;
  return lean_io_result_mk_ok(lean_box_uint32(n));
}

/* ------------------------------------------------------------------------------------ */
/* Resource fences (task 12.3; docs/safety.md §5, docs/viewer.md "Budgets and ceilings").
 *
 * Lean's cost model (fuel, `Limits`, `Filter.Budget`) bounds the work of each call, but not
 * the real memory and time of the process: transient copies, allocator overhead, a bound that
 * is large in practice. These fences sit outside it, in the kernel where possible:
 *
 * Memory (`mem_bytes` > 0):
 *   Linux: RLIMIT_DATA = mem_bytes (since Linux 4.7 it counts every private writable mapping,
 *     so malloc's mmap'd blocks too) and RLIMIT_AS = 2 · mem_bytes (address space, with room
 *     for glibc's per-thread arena reservations and thread stacks); soft = hard, so the worker
 *     cannot raise them again. An allocation beyond them fails, and Lean's runtime ends the
 *     process on an allocation failure. UNTESTED here (written on macOS; CI runs it).
 *   macOS: setrlimit(RLIMIT_AS / RLIMIT_DATA) fails with EINVAL for every finite value
 *     (measured on macOS 26.6; the kernel enforces neither) and the jetsam limit
 *     (memorystatus_control) is refused to an unprivileged process. A watchdog thread
 *     therefore reads the task's phys_footprint (task_info TASK_VM_INFO, allowed under the
 *     seatbelt profile) every 10 ms and ends the process (_exit(6)) above mem_bytes. The
 *     overshoot is what the worker can allocate and touch in 10 ms. It is a fence against
 *     runaway inputs, not against a compromised worker, which could stop the thread; the
 *     client's deadline kill (20 s) does not depend on the worker.
 * CPU (`cpu_s` > 0): RLIMIT_CPU. The soft limit is re-armed before every request
 *   (`safepdf_worker_arm_cpu`) to the CPU time used so far + cpu_s + 1, so a long-lived
 *   worker is not ended by the CPU time of earlier requests; crossing it sends SIGXCPU, whose
 *   default action ends the process. The hard limit is left as it is (the worker has no
 *   privilege to raise it; a compromised worker could raise its own soft limit up to it,
 *   like it could ignore SIGXCPU: again the client's deadline is the fence for that case).
 */

static uint32_t safepdf_cpu_s = 0;

/* CPU time of the process so far, in whole seconds (rounded down). */
static uint64_t safepdf_cpu_used_s(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts) != 0) return 0;
  return (uint64_t)ts.tv_sec;
}

#if defined(__linux__)
#include <sys/syscall.h>
/* setrlimit through prlimit64 (the seccomp allowlist has prlimit64, not setrlimit). */
static int safepdf_set_rlimit(int res, const struct rlimit *r) {
  return (int)syscall(__NR_prlimit64, 0, res, r, NULL);
}
static int safepdf_get_rlimit(int res, struct rlimit *r) {
  return (int)syscall(__NR_prlimit64, 0, res, NULL, r);
}
#else
static int safepdf_set_rlimit(int res, const struct rlimit *r) { return setrlimit(res, r); }
static int safepdf_get_rlimit(int res, struct rlimit *r) { return getrlimit(res, r); }
#endif

static int safepdf_arm_cpu_now(void) {
  if (safepdf_cpu_s == 0) return 0;
  struct rlimit cur;
  if (safepdf_get_rlimit(RLIMIT_CPU, &cur) != 0) return -1;
  rlim_t soft = (rlim_t)(safepdf_cpu_used_s() + safepdf_cpu_s + 1);
  if (cur.rlim_max != RLIM_INFINITY && soft > cur.rlim_max) soft = cur.rlim_max;
  struct rlimit r = { soft, cur.rlim_max };
  return safepdf_set_rlimit(RLIMIT_CPU, &r);
}

lean_obj_res safepdf_worker_arm_cpu(void) {
  (void)safepdf_arm_cpu_now();
  return lean_io_result_mk_ok(lean_box(0));
}

#if defined(__APPLE__)
#include <mach/mach.h>
static uint64_t safepdf_mem_ceiling = 0;

static uint64_t safepdf_footprint(void) {
  task_vm_info_data_t info;
  mach_msg_type_number_t cnt = TASK_VM_INFO_COUNT;
  if (task_info(mach_task_self(), TASK_VM_INFO, (task_info_t)&info, &cnt) != KERN_SUCCESS)
    return 0;
  return info.phys_footprint;
}

static void *safepdf_watchdog(void *arg) {
  (void)arg;
  static const char msg[] = "safe-pdf worker: memory ceiling exceeded\n";
  for (;;) {
    if (safepdf_footprint() > safepdf_mem_ceiling) {
      ssize_t w = write(2, msg, sizeof msg - 1);
      (void)w;
      _exit(6);
    }
    struct timespec ts = { 0, 10 * 1000 * 1000 };
    nanosleep(&ts, NULL);
  }
  return NULL;
}
#endif

lean_obj_res safepdf_worker_fence(uint64_t mem_bytes, uint32_t cpu_s) {
  char buf[512];
  size_t n = 0;
  buf[0] = 0;
  if (mem_bytes > 0) {
#if defined(__APPLE__)
    struct rlimit r = { (rlim_t)mem_bytes, (rlim_t)mem_bytes };
    int as_rc = setrlimit(RLIMIT_AS, &r);
    int as_errno = errno;
    if (as_rc == 0) {
      n += (size_t)snprintf(buf + n, sizeof buf - n, "memory: RLIMIT_AS %llu MiB",
                            (unsigned long long)(mem_bytes >> 20));
    } else {
      safepdf_mem_ceiling = mem_bytes;
      pthread_attr_t a;
      pthread_t t;
      if (pthread_attr_init(&a) != 0 ||
          pthread_attr_setdetachstate(&a, PTHREAD_CREATE_DETACHED) != 0 ||
          pthread_create(&t, &a, safepdf_watchdog, NULL) != 0)
        return safepdf_io_fail("memory fence: cannot start the watchdog thread");
      pthread_attr_destroy(&a);
      n += (size_t)snprintf(buf + n, sizeof buf - n,
                            "memory: phys_footprint watchdog %llu MiB / 10 ms "
                            "(RLIMIT_AS refused: %s)",
                            (unsigned long long)(mem_bytes >> 20), strerror(as_errno));
    }
#elif defined(__linux__)
    struct rlimit d = { (rlim_t)mem_bytes, (rlim_t)mem_bytes };
    struct rlimit as = { (rlim_t)(2 * mem_bytes), (rlim_t)(2 * mem_bytes) };
    if (setrlimit(RLIMIT_DATA, &d) != 0) {
      snprintf(buf, sizeof buf, "memory fence: setrlimit(RLIMIT_DATA) failed: %s", strerror(errno));
      return safepdf_io_fail(buf);
    }
    if (setrlimit(RLIMIT_AS, &as) != 0) {
      snprintf(buf, sizeof buf, "memory fence: setrlimit(RLIMIT_AS) failed: %s", strerror(errno));
      return safepdf_io_fail(buf);
    }
    n += (size_t)snprintf(buf + n, sizeof buf - n, "memory: RLIMIT_DATA %llu MiB, RLIMIT_AS %llu MiB",
                          (unsigned long long)(mem_bytes >> 20),
                          (unsigned long long)((2 * mem_bytes) >> 20));
#else
    return safepdf_io_fail("memory fence: not available on this platform");
#endif
  }
  if (cpu_s > 0) {
    safepdf_cpu_s = cpu_s;
    if (safepdf_arm_cpu_now() != 0) {
      snprintf(buf, sizeof buf, "cpu fence: setrlimit(RLIMIT_CPU) failed: %s", strerror(errno));
      return safepdf_io_fail(buf);
    }
    if (n > 0 && n < sizeof buf) n += (size_t)snprintf(buf + n, sizeof buf - n, "; ");
    if (n < sizeof buf)
      n += (size_t)snprintf(buf + n, sizeof buf - n, "cpu: RLIMIT_CPU %u s per request", cpu_s);
  }
  if (n == 0) snprintf(buf, sizeof buf, "no resource fence");
  return lean_io_result_mk_ok(lean_mk_string(buf));
}

/* ------------------------------------------------------------------------------------ */
#if defined(__APPLE__)

#include <sandbox.h>

/* The worker's seatbelt profile: deny everything, allow nothing. No file-read*,
 * file-write*, network*, process-exec/fork, mach-lookup, ipc-posix*, iokit-open or
 * sysctl rule exists, so all of those are denied. Nothing more is needed: the request
 * loop only reads and writes descriptors it already holds, allocates memory and starts
 * threads, none of which is a sandbox operation (measured on macOS 26, task 12.2b: an
 * earlier draft allowed `sysctl-read`; removing it changed no probe or test result). */
static const char safepdf_worker_profile[] =
  "(version 1)\n"
  "(deny default)\n";

lean_obj_res safepdf_worker_confine(void) {
  char *err = NULL;
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
  int rc = sandbox_init(safepdf_worker_profile, 0, &err);
#pragma clang diagnostic pop
  if (rc != 0) {
    char buf[512];
    snprintf(buf, sizeof buf, "sandbox_init failed: %s", err != NULL ? err : "(no message)");
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
    if (err != NULL) sandbox_free_error(err);
#pragma clang diagnostic pop
    return safepdf_io_fail(buf);
  }
  return lean_io_result_mk_ok(lean_mk_string("macOS seatbelt: (deny default), nothing allowed"));
}

/* ------------------------------------------------------------------------------------ */
#elif defined(__linux__) && defined(__has_include) && \
  __has_include(<linux/seccomp.h>) && __has_include(<linux/filter.h>) && \
  __has_include(<linux/audit.h>) && (defined(__x86_64__) || defined(__aarch64__))

#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sched.h>
#include <stddef.h>
#include <sys/prctl.h>
#include <sys/syscall.h>

#if defined(__x86_64__)
#define SAFEPDF_AUDIT_ARCH AUDIT_ARCH_X86_64
#else
#define SAFEPDF_AUDIT_ARCH AUDIT_ARCH_AARCH64
#endif

#ifndef SECCOMP_RET_KILL_PROCESS
#define SECCOMP_RET_KILL_PROCESS SECCOMP_RET_KILL
#endif
#ifndef SECCOMP_FILTER_FLAG_TSYNC
#define SECCOMP_FILTER_FLAG_TSYNC 1
#endif
#ifndef CLONE_THREAD
#define CLONE_THREAD 0x00010000
#endif

#define SP_LD(off) BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (off))
#define SP_RET(v) BPF_STMT(BPF_RET | BPF_K, (v))
/* if A == nr then return ALLOW (2 instructions) */
#define SP_ALLOW(nr) BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (nr), 0, 1), SP_RET(SECCOMP_RET_ALLOW)

#define SP_MAX 160

lean_obj_res safepdf_worker_confine(void) {
  struct sock_filter f[SP_MAX];
  size_t n = 0;
#define EMIT(...) do { struct sock_filter t_[] = { __VA_ARGS__ }; \
    for (size_t i_ = 0; i_ < sizeof t_ / sizeof t_[0]; i_++) { \
      if (n >= SP_MAX) return safepdf_io_fail("seccomp filter too long"); f[n++] = t_[i_]; } } while (0)

  /* Architecture check: anything but the native ABI is killed. */
  EMIT(SP_LD(offsetof(struct seccomp_data, arch)));
  EMIT(BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SAFEPDF_AUDIT_ARCH, 1, 0));
  EMIT(SP_RET(SECCOMP_RET_KILL_PROCESS));
  EMIT(SP_LD(offsetof(struct seccomp_data, nr)));
#if defined(__x86_64__)
  /* x32 system calls (bit 30) share the x86-64 audit arch: kill. */
  EMIT(BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 0x40000000u, 0, 1));
  EMIT(SP_RET(SECCOMP_RET_KILL_PROCESS));
#endif

  /* I/O on descriptors the process already holds (no call below creates a descriptor). */
  EMIT(SP_ALLOW(__NR_read));
  EMIT(SP_ALLOW(__NR_write));
  EMIT(SP_ALLOW(__NR_readv));
  EMIT(SP_ALLOW(__NR_writev));
  EMIT(SP_ALLOW(__NR_close));
  EMIT(SP_ALLOW(__NR_lseek));
  EMIT(SP_ALLOW(__NR_fstat));
  /* glibc ≥ 2.33 implements fstat as newfstatat(fd, "", AT_EMPTY_PATH): allowing it also
   * allows stat() of a path (metadata only, never contents) — recorded in docs/safety.md. */
#ifdef __NR_newfstatat
  EMIT(SP_ALLOW(__NR_newfstatat));
#endif
#ifdef __NR_statx
  EMIT(SP_ALLOW(__NR_statx));
#endif
  /* Memory. */
  EMIT(SP_ALLOW(__NR_mmap));
  EMIT(SP_ALLOW(__NR_munmap));
  EMIT(SP_ALLOW(__NR_mremap));
  EMIT(SP_ALLOW(__NR_mprotect));
  EMIT(SP_ALLOW(__NR_madvise));
  EMIT(SP_ALLOW(__NR_brk));
  /* Threads and synchronisation (Lean's task manager). */
  EMIT(SP_ALLOW(__NR_futex));
  EMIT(SP_ALLOW(__NR_set_robust_list));
#ifdef __NR_rseq
  EMIT(SP_ALLOW(__NR_rseq));
#endif
  EMIT(SP_ALLOW(__NR_sched_yield));
  EMIT(SP_ALLOW(__NR_sched_getaffinity));
  EMIT(SP_ALLOW(__NR_gettid));
  EMIT(SP_ALLOW(__NR_getpid));
  EMIT(SP_ALLOW(__NR_rt_sigaction));
  EMIT(SP_ALLOW(__NR_rt_sigprocmask));
  EMIT(SP_ALLOW(__NR_rt_sigreturn));
  EMIT(SP_ALLOW(__NR_sigaltstack));
  EMIT(SP_ALLOW(__NR_prlimit64));
  /* Time and randomness. */
  EMIT(SP_ALLOW(__NR_clock_gettime));
  EMIT(SP_ALLOW(__NR_clock_getres));
  EMIT(SP_ALLOW(__NR_gettimeofday));
  EMIT(SP_ALLOW(__NR_clock_nanosleep));
  EMIT(SP_ALLOW(__NR_nanosleep));
  EMIT(SP_ALLOW(__NR_getrandom));
  /* Exit. */
  EMIT(SP_ALLOW(__NR_exit));
  EMIT(SP_ALLOW(__NR_exit_group));
  /* tgkill only to this process (abort, pthread_kill). */
  EMIT(BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_tgkill, 0, 4));
  EMIT(SP_LD(offsetof(struct seccomp_data, args[0])));
  EMIT(BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (uint32_t)getpid(), 0, 1));
  EMIT(SP_RET(SECCOMP_RET_ALLOW));
  EMIT(SP_RET(SECCOMP_RET_ERRNO | EPERM));
  /* clone only for threads (CLONE_THREAD set in the flags, argument 0 on both ABIs); no
   * fork. clone3 passes its flags in memory, which BPF cannot read: ENOSYS makes glibc fall
   * back to clone. */
#ifdef __NR_clone3
  EMIT(BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_clone3, 0, 1));
  EMIT(SP_RET(SECCOMP_RET_ERRNO | ENOSYS));
#endif
  EMIT(BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_clone, 0, 4));
  EMIT(SP_LD(offsetof(struct seccomp_data, args[0])));
  EMIT(BPF_JUMP(BPF_JMP | BPF_JSET | BPF_K, CLONE_THREAD, 0, 1));
  EMIT(SP_RET(SECCOMP_RET_ALLOW));
  EMIT(SP_RET(SECCOMP_RET_ERRNO | EPERM));
  /* Everything else (open/openat/openat2, socket/connect, execve/execveat, fork/vfork,
   * ptrace, kill, ioctl, pipe, mount, …): EPERM. */
  EMIT(SP_RET(SECCOMP_RET_ERRNO | EPERM));
#undef EMIT

  struct sock_fprog prog = { .len = (unsigned short)n, .filter = f };
  char buf[256];
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
    snprintf(buf, sizeof buf, "prctl(PR_SET_NO_NEW_PRIVS) failed: %s", strerror(errno));
    return safepdf_io_fail(buf);
  }
  long rc = syscall(__NR_seccomp, SECCOMP_SET_MODE_FILTER, SECCOMP_FILTER_FLAG_TSYNC, &prog);
  if (rc != 0) {
    if (rc > 0)
      snprintf(buf, sizeof buf, "seccomp: thread %ld could not be synchronised", rc);
    else
      snprintf(buf, sizeof buf, "seccomp(SET_MODE_FILTER, TSYNC) failed: %s", strerror(errno));
    return safepdf_io_fail(buf);
  }
  return lean_io_result_mk_ok(lean_mk_string("Linux seccomp-bpf allowlist + no_new_privs"));
}

/* ------------------------------------------------------------------------------------ */
#else

lean_obj_res safepdf_worker_confine(void) {
  return safepdf_io_fail("no worker sandbox on this platform (macOS seatbelt or Linux "
                         "seccomp with x86-64/arm64 and the kernel headers are required)");
}

#endif

/* ------------------------------------------------------------------------------------ */
#ifdef SAFEPDF_WORKER_PROBE
/* Test-only (the `worker-probe` executable, never `worker`): try to open a TCP connection
 * to 127.0.0.1:port. Returns "ok: connected" or "socket: <error>" / "connect: <error>". */
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>

lean_obj_res safepdf_probe_tcp(uint32_t port) {
  char buf[256];
  int s = socket(AF_INET, SOCK_STREAM, 0);
  if (s < 0) {
    snprintf(buf, sizeof buf, "socket: %s", strerror(errno));
    return lean_io_result_mk_ok(lean_mk_string(buf));
  }
  struct sockaddr_in a;
  memset(&a, 0, sizeof a);
  a.sin_family = AF_INET;
  a.sin_port = htons((uint16_t)port);
  a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  if (connect(s, (struct sockaddr *)&a, sizeof a) != 0) {
    snprintf(buf, sizeof buf, "connect: %s", strerror(errno));
    close(s);
    return lean_io_result_mk_ok(lean_mk_string(buf));
  }
  close(s);
  return lean_io_result_mk_ok(lean_mk_string("ok: connected"));
}

/* Test-only: a listening TCP socket on 127.0.0.1 (ephemeral port, close-on-exec, kept open
 * until the process exits; connections complete in the backlog without accept). Returns the
 * port, 0 on failure. */
#include <fcntl.h>
lean_obj_res safepdf_probe_listen(void) {
  int s = socket(AF_INET, SOCK_STREAM, 0);
  if (s < 0) return lean_io_result_mk_ok(lean_box_uint32(0));
  fcntl(s, F_SETFD, FD_CLOEXEC);
  struct sockaddr_in a;
  memset(&a, 0, sizeof a);
  a.sin_family = AF_INET;
  a.sin_port = 0;
  a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  socklen_t len = sizeof a;
  if (bind(s, (struct sockaddr *)&a, sizeof a) != 0 || listen(s, 16) != 0 ||
      getsockname(s, (struct sockaddr *)&a, &len) != 0) {
    close(s);
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }
  return lean_io_result_mk_ok(lean_box_uint32(ntohs(a.sin_port)));
}
#endif
