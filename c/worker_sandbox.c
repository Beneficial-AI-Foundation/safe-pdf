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
 *   fail with EPERM; a foreign architecture or an x32 syscall kills the process. Before
 *   the filter: RLIMIT_CORE 0, PR_SET_DUMPABLE 0, and SIGXCPU/SIGABRT handlers that leave
 *   one line on stderr (task 12.c1). Written on macOS; exercised only by Linux CI.
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
/* Resource fences (task 12.3, fixed for Linux in 12.c1; docs/safety.md §2.4 and §5 item 0c,
 * docs/viewer.md "Budgets and ceilings").
 *
 * Lean's cost model (fuel, `Limits`, `Filter.Budget`) bounds the work of each call, but not
 * the real memory and time of the process: transient copies, allocator overhead, a bound that
 * is large in practice. These fences sit outside it:
 *
 * Memory (`mem_bytes` > 0): a watchdog thread reads the process's own private resident memory
 *   every 10 ms and ends the process (_exit(6), one line on stderr) above mem_bytes. The
 *   overshoot is what the worker can allocate and touch in 10 ms. It is a fence against
 *   runaway inputs, not against a compromised worker, which could stop the thread; the
 *   client's deadline kill (20 s) does not depend on the worker.
 *   macOS: the task's phys_footprint (task_info TASK_VM_INFO, allowed under the seatbelt
 *     profile). setrlimit(RLIMIT_AS / RLIMIT_DATA) fails with EINVAL for every finite value
 *     (measured on macOS 26.6; the kernel enforces neither), and the jetsam limit
 *     (memorystatus_control) is refused to an unprivileged process; RLIMIT_AS is still tried
 *     first.
 *   Linux: resident − shared pages of /proc/self/statm, read through a descriptor opened
 *     before confinement (lseek + read are in the seccomp allowlist; the descriptor shows the
 *     worker its own memory counters and nothing else). Kernel backstop: RLIMIT_DATA =
 *     the private writable mappings at fence time + 2 · mem_bytes and RLIMIT_AS = the address
 *     space at fence time + 4 · mem_bytes, soft = hard. They are relative to the baseline
 *     because the Lean runtime's allocator (mimalloc 3, `arena_eager_commit` on overcommit
 *     systems) reserves 1 GiB arenas as committed read-write mappings: a fresh worker
 *     already maps more than a small absolute ceiling, and absolute limits (12.3: DATA =
 *     mem_bytes, AS = 2 · mem_bytes) made every later mapping fail (CI run 45303741160: the
 *     confined probe aborted, a 2048 MiB worker died on a 124 MB render). Reserved but
 *     untouched arena pages are not resident, so the watchdog measures what is used.
 * CPU (`cpu_s` > 0): RLIMIT_CPU. The soft limit is re-armed before every request
 *   (`safepdf_worker_arm_cpu`) to the CPU time used so far + cpu_s + 1, so a long-lived
 *   worker is not ended by the CPU time of earlier requests; crossing it sends SIGXCPU, whose
 *   default action ends the process. The hard limit is left as it is (the worker has no
 *   privilege to raise it; a compromised worker could raise its own soft limit up to it,
 *   like it could ignore SIGXCPU: again the client's deadline is the fence for that case).
 *   SIGXCPU and SIGABRT dump core by default; on Linux `confine` makes the worker
 *   non-dumpable with RLIMIT_CORE = 0, because a pipe `core_pattern` (apport,
 *   systemd-coredump) otherwise streams gigabytes of reserved arena to the helper and the
 *   dying worker lingers past the client's deadline (CI run 45303741160: the 1 s CPU fence
 *   "timed out" at 20 s and the client's SIGKILL ended the dump).
 */

static uint32_t safepdf_cpu_s = 0;
static uint64_t safepdf_mem_ceiling = 0;

/* CPU time of the process so far, in whole seconds (rounded down). */
static uint64_t safepdf_cpu_used_s(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts) != 0) return 0;
  return (uint64_t)ts.tv_sec;
}

/* One line on stderr (also from a signal handler or the watchdog: write(2) only). */
static void safepdf_say(const char *m) {
  ssize_t w = write(2, m, strlen(m));
  (void)w;
}

#if defined(__linux__)
/* a + k · b, saturating at UINT64_MAX (= RLIM_INFINITY on Linux). */
static uint64_t safepdf_sat_add_mul(uint64_t a, uint64_t k, uint64_t b) {
  if (b != 0 && k > (UINT64_MAX - a) / b) return UINT64_MAX;
  return a + k * b;
}

#include <fcntl.h>
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
  if (safepdf_arm_cpu_now() != 0) {
    /* Not fatal by itself (the client's deadline still holds), but visible. */
    char buf[160];
    snprintf(buf, sizeof buf, "safe-pdf worker: cpu fence: re-arming RLIMIT_CPU failed: %s\n",
             strerror(errno));
    safepdf_say(buf);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* The process's private resident memory in bytes (0: ok, -1: cannot be read). */
#if defined(__APPLE__)
#include <mach/mach.h>
#define SAFEPDF_HAS_WATCHDOG 1
static int safepdf_footprint(uint64_t *out) {
  task_vm_info_data_t info;
  mach_msg_type_number_t cnt = TASK_VM_INFO_COUNT;
  if (task_info(mach_task_self(), TASK_VM_INFO, (task_info_t)&info, &cnt) != KERN_SUCCESS)
    return -1;
  *out = info.phys_footprint;
  return 0;
}
#elif defined(__linux__)
#define SAFEPDF_HAS_WATCHDOG 1
static int safepdf_statm_fd = -1;
static uint64_t safepdf_page_size = 4096;

/* The first six fields of /proc/self/statm (pages): size resident shared text lib data. */
static int safepdf_statm(uint64_t f[6]) {
  char b[256];
  if (safepdf_statm_fd < 0 || lseek(safepdf_statm_fd, 0, SEEK_SET) != 0) return -1;
  ssize_t k = read(safepdf_statm_fd, b, sizeof b - 1);
  if (k <= 0) return -1;
  b[k] = 0;
  size_t i = 0;
  for (int nf = 0; nf < 6; nf++) {
    while (b[i] == ' ') i++;
    if (b[i] < '0' || b[i] > '9') return -1;
    uint64_t v = 0;
    while (b[i] >= '0' && b[i] <= '9') {
      if (v > (UINT64_MAX - 9) / 10) return -1;
      v = v * 10 + (uint64_t)(b[i] - '0');
      i++;
    }
    f[nf] = v;
  }
  return 0;
}

static int safepdf_footprint(uint64_t *out) {
  uint64_t f[6];
  if (safepdf_statm(f) != 0) return -1;
  uint64_t priv = f[1] > f[2] ? f[1] - f[2] : 0;
  *out = safepdf_sat_add_mul(0, priv, safepdf_page_size);
  return 0;
}
#endif

#ifdef SAFEPDF_HAS_WATCHDOG
static void *safepdf_watchdog(void *arg) {
  (void)arg;
  for (;;) {
    uint64_t used = 0;
    if (safepdf_footprint(&used) != 0) {
      safepdf_say("safe-pdf worker: memory fence: the watchdog cannot read the footprint\n");
      _exit(6);
    }
    if (used > safepdf_mem_ceiling) {
      char buf[160];
      snprintf(buf, sizeof buf,
               "safe-pdf worker: memory ceiling exceeded (%llu MiB > %llu MiB)\n",
               (unsigned long long)(used >> 20), (unsigned long long)(safepdf_mem_ceiling >> 20));
      safepdf_say(buf);
      _exit(6);
    }
    struct timespec ts = { 0, 10 * 1000 * 1000 };
    nanosleep(&ts, NULL);
  }
  return NULL;
}

static int safepdf_start_watchdog(void) {
  pthread_attr_t a;
  pthread_t t;
  if (pthread_attr_init(&a) != 0) return -1;
  int rc = pthread_attr_setdetachstate(&a, PTHREAD_CREATE_DETACHED);
  if (rc == 0) rc = pthread_create(&t, &a, safepdf_watchdog, NULL);
  pthread_attr_destroy(&a);
  return rc;
}
#endif

lean_obj_res safepdf_worker_fence(uint64_t mem_bytes, uint32_t cpu_s) {
  char buf[640];
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
      if (safepdf_start_watchdog() != 0)
        return safepdf_io_fail("memory fence: cannot start the watchdog thread");
      n += (size_t)snprintf(buf + n, sizeof buf - n,
                            "memory: phys_footprint watchdog %llu MiB / 10 ms "
                            "(RLIMIT_AS refused: %s)",
                            (unsigned long long)(mem_bytes >> 20), strerror(as_errno));
    }
#elif defined(__linux__)
    long ps = sysconf(_SC_PAGESIZE);
    if (ps > 0) safepdf_page_size = (uint64_t)ps;
    if (safepdf_statm_fd < 0) safepdf_statm_fd = open("/proc/self/statm", O_RDONLY | O_CLOEXEC);
    if (safepdf_statm_fd < 0) {
      snprintf(buf, sizeof buf, "memory fence: open(/proc/self/statm) failed: %s",
               strerror(errno));
      return safepdf_io_fail(buf);
    }
    uint64_t f[6];
    if (safepdf_statm(f) != 0)
      return safepdf_io_fail("memory fence: cannot read /proc/self/statm");
    uint64_t vsz = safepdf_sat_add_mul(0, f[0], safepdf_page_size);
    uint64_t data = safepdf_sat_add_mul(0, f[5], safepdf_page_size);
    uint64_t priv = safepdf_sat_add_mul(0, f[1] > f[2] ? f[1] - f[2] : 0, safepdf_page_size);
    uint64_t data_lim = safepdf_sat_add_mul(data, 2, mem_bytes);
    uint64_t as_lim = safepdf_sat_add_mul(vsz, 4, mem_bytes);
    if (priv > mem_bytes) {
      snprintf(buf, sizeof buf, "memory fence: the worker already holds %llu MiB, above its "
               "ceiling of %llu MiB", (unsigned long long)(priv >> 20),
               (unsigned long long)(mem_bytes >> 20));
      return safepdf_io_fail(buf);
    }
    struct rlimit d = { (rlim_t)data_lim, (rlim_t)data_lim };
    struct rlimit as = { (rlim_t)as_lim, (rlim_t)as_lim };
    if (safepdf_set_rlimit(RLIMIT_DATA, &d) != 0) {
      snprintf(buf, sizeof buf, "memory fence: setrlimit(RLIMIT_DATA, %llu MiB) failed: %s",
               (unsigned long long)(data_lim >> 20), strerror(errno));
      return safepdf_io_fail(buf);
    }
    if (safepdf_set_rlimit(RLIMIT_AS, &as) != 0) {
      snprintf(buf, sizeof buf, "memory fence: setrlimit(RLIMIT_AS, %llu MiB) failed: %s",
               (unsigned long long)(as_lim >> 20), strerror(errno));
      return safepdf_io_fail(buf);
    }
    safepdf_mem_ceiling = mem_bytes;
    int wrc = safepdf_start_watchdog();
    if (wrc != 0) {
      snprintf(buf, sizeof buf, "memory fence: cannot start the watchdog thread: %s",
               strerror(wrc));
      return safepdf_io_fail(buf);
    }
    n += (size_t)snprintf(buf + n, sizeof buf - n,
                          "memory: private resident watchdog %llu MiB / 10 ms (at start %llu "
                          "MiB); backstop RLIMIT_DATA %llu MiB (at start %llu MiB + 2x), "
                          "RLIMIT_AS %llu MiB (at start %llu MiB + 4x)",
                          (unsigned long long)(mem_bytes >> 20), (unsigned long long)(priv >> 20),
                          (unsigned long long)(data_lim >> 20), (unsigned long long)(data >> 20),
                          (unsigned long long)(as_lim >> 20), (unsigned long long)(vsz >> 20));
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

#include <signal.h>

/* Task 12.c1 diagnostics: SIGXCPU (the CPU fence) and SIGABRT (an allocation or thread
 * failure inside the runtime ends in abort) leave one line on stderr, then end the process
 * with the same signal (SA_RESETHAND: the default action; the re-raised signal stays pending
 * while the handler runs and is delivered when it returns). write, rt_sigprocmask and
 * tgkill-to-self are in the allowlist. */
static void safepdf_fatal_signal(int sig) {
  safepdf_say(sig == SIGXCPU ? "safe-pdf worker: SIGXCPU: the CPU time fence ended the request\n"
                             : "safe-pdf worker: SIGABRT: the runtime aborted\n");
  raise(sig);
}

static int safepdf_install_fatal_handlers(void) {
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = safepdf_fatal_signal;
  sa.sa_flags = SA_RESETHAND;
  sigemptyset(&sa.sa_mask);
  if (sigaction(SIGXCPU, &sa, NULL) != 0) return -1;
  if (sigaction(SIGABRT, &sa, NULL) != 0) return -1;
  /* An inherited blocked SIGXCPU would switch the CPU fence off: unblock both in this
   * thread (threads started later inherit its mask). */
  sigset_t un;
  sigemptyset(&un);
  sigaddset(&un, SIGXCPU);
  sigaddset(&un, SIGABRT);
  return pthread_sigmask(SIG_UNBLOCK, &un, NULL) == 0 ? 0 : -1;
}

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
  /* No core dumps (task 12.c1): with a pipe core_pattern the kernel streams the whole
   * worker, gigabytes of reserved allocator arena included, to the helper, and the dying
   * worker outlives the client's deadline. Non-dumpable also keeps other processes of the
   * same user from attaching to it (ptrace) or reading /proc/<pid>/mem. */
  struct rlimit nocore = { 0, 0 };
  if (safepdf_set_rlimit(RLIMIT_CORE, &nocore) != 0) {
    snprintf(buf, sizeof buf, "setrlimit(RLIMIT_CORE, 0) failed: %s", strerror(errno));
    return safepdf_io_fail(buf);
  }
  if (prctl(PR_SET_DUMPABLE, 0, 0, 0, 0) != 0) {
    snprintf(buf, sizeof buf, "prctl(PR_SET_DUMPABLE, 0) failed: %s", strerror(errno));
    return safepdf_io_fail(buf);
  }
  if (safepdf_install_fatal_handlers() != 0) {
    snprintf(buf, sizeof buf, "sigaction(SIGXCPU/SIGABRT) failed: %s", strerror(errno));
    return safepdf_io_fail(buf);
  }
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
  return lean_io_result_mk_ok(lean_mk_string("Linux seccomp-bpf allowlist + no_new_privs, "
                                                 "not dumpable, RLIMIT_CORE 0"));
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
