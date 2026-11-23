# safe-pdf — cryptography review package

Preparation for an external review of the cryptography in safe-pdf (Plan.md §6 Phase 12
"Writer confidentiality", task 12.4; `docs/safety.md` §5 item 9, independent review). This
page says what to review, what we claim and do not claim, and how to reproduce every test
vector. Everything here is pure Lean 4 (toolchain `leanprover/lean4:v4.36.0`, no
dependencies) unless stated otherwise.

## 1. Scope

| Component | File | What it is |
|---|---|---|
| MD5 | `SafePdf/Core/Crypt/Md5.lean` | RFC 1321; key derivation (Algorithms 1–5), `/ID` update |
| SHA-256/384/512 | `SafePdf/Core/Crypt/Sha2.lean` | FIPS 180-4; `/R 5`, `/R 6` key derivation (Algorithm 2.B), writer IVs |
| RC4 | `SafePdf/Core/Crypt/Rc4.lean` | ARCFOUR; `/V 1`, `/V 2`, `/CFM /V2` |
| AES | `SafePdf/Core/Crypt/Aes.lean` | FIPS 197 AES-128/192/256; ECB block ops, CBC encrypt (no padding) and decrypt (strict PKCS#7) |
| Security handler | `SafePdf/Core/Crypt.lean` | ISO 32000-2 §7.6: `/Encrypt` parsing (rules C1–C3), file key for the **empty user password** (C4: Algorithms 2, 2.A, 2.B, 4, 5), per-object key (C5, Algorithm 1), what is decrypted (C6–C7''), `/Perms` check (advisory) |
| Writer encryption | `SafePdf/Core/Write/Encrypt.lean` | Encrypting the objects of an incremental update with the document's own handler (rules E1–E7, E3'): RC4, AES-CBC with PKCS#7 padding (`pkcs7Pad`) and the IV prepended; IV derivation (`ivInput`, `deriveIv`) |
| IV seed (shell) | `SafePdf/Shell/App/Save.lean` | `freshSeed`, `seedFor`: OS randomness for the writer; the RC4 / signed-input policy (`protection`, `notes`, `refusal`) |
| Writer self-check | `SafePdf/Core/Write/Incremental.lean` (W8, W10) | Re-opens every written file with the strict parser and checks each written object decrypts to its plaintext and the decryption state equals the original's |

Out of scope: password entry and owner-password authentication (not supported: files that do
not open with the empty user password are refused, rule C4), public-key security handlers,
digital-signature *verification* (signatures are never checked, only detected for the save
policy), and the unverified Tk shell other than the two functions above.

## 2. Threat model

* **Reading.** The input file is hostile. Decryption must never crash, loop or read out of
  bounds (all code is total, bounded by `Limits`, no `!` indexing; see `docs/safety.md`), and
  a failure to decrypt must fail visibly (strict error) rather than show undecrypted or
  partially decrypted content (rule C7'' decision, task 4.6). Encryption on input is *not*
  a security boundary for us: we only open files whose user password is empty, so anyone
  holding the file can decrypt it; `/P` permissions are advisory (C8, S8).
* **Writing** (annotations saved as an incremental update, Plan.md C7/S8). The original
  bytes are kept as a prefix; new objects are encrypted with the document's own handler and
  file key so that every reader decrypts them like the original. The writer must not make
  the file *less* confidential than its handler implies:
  - AES IVs are unpredictable and never reused across saves (E3', task 12.4): every save
    draws a fresh 64-byte seed from the OS (`/dev/urandom` ‖ `IO.getRandomBytes`, which is
    libuv's `uv_random` — `getentropy` on macOS, `getrandom` on Linux; Lean documents it as
    "not guaranteed to be cryptographically secure", hence the `/dev/urandom` read in front).
    The pure core has no randomness: the IV is `SHA-256(ivDomainSeeded ‖ |seed| ‖ seed ‖ file
    key ‖ num ‖ gen ‖ counter ‖ kind ‖ plaintext)[0..16)`. The seed is never written.
  - The plaintext of a new annotation never appears in the clear in the update (tested).
  - The writer never downgrades: it cannot switch handler (an incremental update shares one
    `/Encrypt`), and it does not offer an unencrypted copy.
* **Attacker capabilities considered**: holds the written file (and every earlier version of
  it); chooses the input file. Not considered: local attackers on the machine (timing, cache
  or power side channels — the implementations are not constant-time), and a compromised OS
  RNG.

## 3. Claims and their evidence

| Claim | Evidence |
|---|---|
| MD5, SHA-2, RC4, AES match their standards | Build-time `#guard` vectors in each file: RFC 1321 A.5 (MD5), FIPS 180-4 / NIST examples (SHA-256/384/512), RFC 6229 (RC4, 40- and 128-bit keys), FIPS 197 App. C and SP 800-38A F.2 (AES ECB/CBC). A correctness *proof* is out of scope (Plan.md §6 Phase 4). |
| Key derivation matches ISO 32000-2 / qpdf | `Tests/Crypt.lean` on `Tests/adversarial/encrypted/` (written by an independent stdlib-only Python RC4/AES in `generate.py`) and the qpdf-made fixtures under `Tests/golden/text/enc-*.pdf`, `Tests/fixtures-write/encrypted/`; `#guard`s for Algorithm 2.B in `Core/Crypt.lean`. |
| Writer encryption inverts decryption | `#guard`s in `Core/Write/Encrypt.lean` (every method, lengths 0–40, three seeds); `Tests/WriteIncremental.lean` `runEncryptUnit`; and the writer's self-check W8 on every write (a failing write returns an error, never bytes). Not proved: it rests on the vector-tested primitives (E7). |
| The IV leads the ciphertext; distinct IVs give distinct ciphertexts | Theorems `Write.Encrypt.aesEncrypt_prefix`, `aesEncrypt_extract`, `aesEncrypt_iv_ne` (standard axioms only). |
| Fresh IVs per save | `Tests/WriteConfidentiality.lean`: AES-128, AES-256, AES-256 with object streams — two saves with fresh seeds differ, the same seed reproduces the bytes, both reopen strictly with the marks read back; fresh seeds are 64 bytes and differ. |
| The empty seed is the old deterministic IV (task 9.5f) | `#guard` in `Core/Write/Encrypt.lean`. |
| C7 (original bytes are a prefix, strict re-open, every other object unchanged) holds for every seed | `SafePdf/Spec/Write.lean`: every theorem is stated for an arbitrary `ivSeed`. |

## 4. Policies (task 12.4)

* **AES-128 / AES-256** (`/AESV2`, `/AESV3`): written, fresh IVs.
* **Legacy RC4** (`/V 1`, `/V 2`, `/CFM /V2`): written with the document's handler, with the
  status note "this file uses the legacy RC4 encryption: the new annotations are encrypted
  with it, as the file requires (it opens without a password, so its encryption keeps nothing
  confidential)". RC4 has no IV; the per-object key depends only on the object number and
  generation, so a rewritten page or superseded annotation (same number) reuses the
  keystream of its earlier revision — and ISO's design already restarts the same keystream
  for every string of one object. Refusing would not protect anything (the file opens without
  a password); writing a decrypted copy would silently remove the author's protection.
* **Signed** (`/SigFlags` bit 1, or a `/FT /Sig` field with a signature `/V`): written with
  the note that the signature covers only the original revision (kept byte for byte); the
  annotations are a later revision outside it.
* **Certified, annotations not permitted** (`/Perms /DocMDP`, `/P` 1 or 2, default 2):
  refused — "this document is certified and its certification (/DocMDP /P n) permits no
  annotation changes: saving would invalidate it. Export the marks as XFDF instead". `/P 3`
  is written with the signed note.

## 5. Known limitations (for the reviewer to weigh)

1. **No confidentiality against file holders** for any file we can open (empty user
   password). The IV work hardens the writer for when passwords are supported; today it
   prevents cross-save ciphertext linkage and keeps the writer reviewable.
2. **Primitives are tested, not proved**; none is constant-time (byte-table AES, data-
   dependent RC4 indices). Acceptable for decrypting files the user already holds; would not
   be for an online oracle.
3. **AES-CBC is unauthenticated** (ISO 32000's choice); a tampered ciphertext is detected
   only by PKCS#7 padding (strict) or by the object failing to parse.
4. **IV includes the plaintext** in its hash input (as in task 9.5f): with the seed unknown
   this reveals nothing; with the empty seed (preview only, never written) equal plaintexts
   at the same position give equal ciphertexts.
5. **`IO.getRandomBytes`** is documented by Lean as not guaranteed cryptographically
   secure; we prepend `/dev/urandom` and require at least one 32-byte source. On a system
   with neither, saving an encrypted document is refused.
6. **Signature detection** inspects top-level `/AcroForm /Fields` (first 1000) and
   `/SigFlags`; signature fields nested in `/Kids`, usage-rights signatures (`/Perms /UR3`)
   and `/FieldMDP` locks are not considered by the policy.
7. **RC4 keystream reuse** on rewritten objects (§4) — inherent to the handler.
8. `/Perms` mismatches and `/P` flags are advisory and not enforced (S8).

## 6. Reproducing the vectors and tests

```sh
lake build                      # runs every #guard: MD5, SHA-2, RC4, AES vectors,
                                # Algorithm 2.B, writer round trips and IV checks
lake build tests && lake exe tests   # suites crypt, write-incremental, write-annots,
                                     # write-confidentiality
lake env lean scripts/axioms.lean | grep aesEncrypt   # axioms (after adding the lines)
python3 -I Tests/adversarial/encrypted/generate.py --check      # independent Python RC4/AES
python3 -I Tests/fixtures-write/encrypted/generate.py --check   # qpdf fixtures (needs qpdf)
```

Single files: `lake env lean SafePdf/Core/Crypt/Aes.lean` (and `Md5`, `Sha2`, `Rc4`,
`Core/Crypt.lean`, `Core/Write/Encrypt.lean`) re-runs that file's vectors after a build.
`SAFEPDF_WRITE_OUT=DIR lake exe tests` writes the writer's outputs for `qpdf --check` and
`mutool` inspection.
