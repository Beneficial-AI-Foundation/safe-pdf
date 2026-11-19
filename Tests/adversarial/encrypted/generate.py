#!/usr/bin/env python3
"""Generate small encrypted PDFs for the standard security handler (task 4.3b).

ISO 32000-2 §7.6: RC4 (V1 R2, V2 R3, V4 R4 /V2), AES-128 (V4 R4 /AESV2), AES-256 (V5 R5 and
V5 R6 /AESV3), each with an EMPTY user password (and owner password "owner"), plus files whose
user password is "secret" (must fail to open cleanly: only the empty user password is
supported).

Stdlib only (hashlib for MD5/SHA-2, zlib); RC4 and AES are small pure-Python implementations
written here, independent of the Lean code. Deterministic: IVs, salts and IDs come from a
seeded counter (SHA-256 of a label), no timestamps, no randomness.

Every file holds:
  1 Catalog, 2 Pages, 3 Page (MediaBox 0 0 612 792, /Contents 4 0 R),
  4 content stream (FlateDecode, encrypted),
  5 Info dictionary with /Title (a text string, encrypted),
  6 a dictionary inside object stream 7 with /Kind (a string, NOT encrypted on its own: the
    whole object stream is),
  7 the object stream (FlateDecode, encrypted),
  8 the xref stream (never encrypted),
  9 the encryption dictionary (its strings are never encrypted) - except in rc4-40.pdf,
    where /Encrypt is a direct dictionary in the trailer,
  and in the V4/V5 files:
  10 a stream with /Filter [/Crypt /FlateDecode] /DecodeParms [<< /Name /Identity >> null]
     (stored unencrypted: the Identity crypt filter overrides /StmF),
  11 (aesv2.pdf only, /EncryptMetadata false) a /Type /Metadata stream stored unencrypted.

Usage:
    python3 -I Tests/adversarial/encrypted/generate.py           # write the PDFs
    python3 -I Tests/adversarial/encrypted/generate.py --check   # verify files on disk
    python3 -I Tests/adversarial/encrypted/generate.py --vectors # print Lean #guard vectors
"""
import hashlib
import os
import struct
import sys
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n"

PAD = bytes.fromhex("28BF4E5E4E758A4164004E56FFFA01082E2E00B6D0683E802F0CA9FE6453697A")

TITLE = b"Encrypted title \xe9"
KIND = b"inside an object stream"
CONTENT = b"BT /F1 24 Tf 72 700 Td (Hello, encrypted world) Tj ET"
IDENTITY_DATA = b"identity crypt filter: stored in the clear"
METADATA = b"<?xpacket begin='' id='W5M0MpCehiHzreSzNTczkc9d'?><x:xmpmeta xmlns:x='adobe:ns:meta/'/>"
P_VALUE = -3904


def det_bytes(label, n):
    """Deterministic pseudo-random bytes: SHA-256 counter mode over a label."""
    out = b""
    i = 0
    while len(out) < n:
        out += hashlib.sha256(b"%s/%d" % (label.encode(), i)).digest()
        i += 1
    return out[:n]


# ---------------------------------------------------------------- RC4

def rc4(key, data):
    s = list(range(256))
    j = 0
    for i in range(256):
        j = (j + s[i] + key[i % len(key)]) & 0xFF
        s[i], s[j] = s[j], s[i]
    i = j = 0
    out = bytearray()
    for b in data:
        i = (i + 1) & 0xFF
        j = (j + s[i]) & 0xFF
        s[i], s[j] = s[j], s[i]
        out.append(b ^ s[(s[i] + s[j]) & 0xFF])
    return bytes(out)


# ---------------------------------------------------------------- AES (encryption only)

SBOX = [0] * 256


def _init_sbox():
    p = q = 1
    while True:
        # multiply p by 3
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        # divide q by 3
        q ^= q << 1
        q ^= q << 2
        q ^= q << 4
        q &= 0xFF
        if q & 0x80:
            q ^= 0x09
        x = q ^ (((q << 1) | (q >> 7)) & 0xFF) ^ (((q << 2) | (q >> 6)) & 0xFF) \
            ^ (((q << 3) | (q >> 5)) & 0xFF) ^ (((q << 4) | (q >> 4)) & 0xFF)
        SBOX[p] = x ^ 0x63
        if p == 1:
            break
    SBOX[0] = 0x63


_init_sbox()


def xtime(a):
    return ((a << 1) ^ 0x1B) & 0xFF if a & 0x80 else a << 1


def expand_key(key):
    nk = len(key) // 4
    assert len(key) in (16, 24, 32)
    nr = nk + 6
    w = [list(key[4 * i:4 * i + 4]) for i in range(nk)]
    rcon = 1
    for i in range(nk, 4 * (nr + 1)):
        t = list(w[i - 1])
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = xtime(rcon)
        elif nk > 6 and i % nk == 4:
            t = [SBOX[b] for b in t]
        w.append([a ^ b for a, b in zip(w[i - nk], t)])
    return nr, w


def encrypt_block(ks, block):
    nr, w = ks
    s = [block[i] ^ w[i // 4][i % 4] for i in range(16)]  # column-major: s[4c+r]
    for rnd in range(1, nr + 1):
        s = [SBOX[b] for b in s]
        # shift rows: row r of column c moves from column c+r
        s = [s[4 * ((c + r) % 4) + r] for c in range(4) for r in range(4)]
        if rnd != nr:
            t = []
            for c in range(4):
                a = s[4 * c:4 * c + 4]
                x = a[0] ^ a[1] ^ a[2] ^ a[3]
                t += [a[r] ^ x ^ xtime(a[r] ^ a[(r + 1) % 4]) for r in range(4)]
            s = t
        s = [s[i] ^ w[4 * rnd + i // 4][i % 4] for i in range(16)]
    return bytes(s)


def cbc_encrypt(key, iv, data, pad=True):
    if pad:
        n = 16 - len(data) % 16
        data = data + bytes([n]) * n
    assert len(data) % 16 == 0
    ks = expand_key(key)
    out = b""
    prev = iv
    for i in range(0, len(data), 16):
        prev = encrypt_block(ks, bytes(a ^ b for a, b in zip(data[i:i + 16], prev)))
        out += prev
    return out


def ecb_encrypt(key, data):
    ks = expand_key(key)
    return b"".join(encrypt_block(ks, data[i:i + 16]) for i in range(0, len(data), 16))


# FIPS 197 Appendix C.1 / C.3 self-checks of the AES above.
assert encrypt_block(expand_key(bytes(range(16))), bytes.fromhex("00112233445566778899aabbccddeeff")) \
    == bytes.fromhex("69c4e0d86a7b0430d8cdb78070b4c55a")
assert encrypt_block(expand_key(bytes(range(32))), bytes.fromhex("00112233445566778899aabbccddeeff")) \
    == bytes.fromhex("8ea2b7ca516745bfeafc49904b496089")
# RFC 6229-style RC4 check (key 0x0102030405, first keystream bytes).
assert rc4(bytes([1, 2, 3, 4, 5]), bytes(4)) == bytes.fromhex("b2396305")


# ---------------------------------------------------------------- key derivation

def pad_pw(pw):
    return (pw + PAD)[:32]


def alg3_owner(opw, upw, r, n):
    """Algorithm 3: the /O value for R2-R4."""
    h = hashlib.md5(pad_pw(opw)).digest()
    if r >= 3:
        for _ in range(50):
            h = hashlib.md5(h[:n]).digest()
    key = h[:n]
    o = rc4(key, pad_pw(upw))
    if r >= 3:
        for i in range(1, 20):
            o = rc4(bytes(b ^ i for b in key), o)
    return o


def alg2_key(upw, o, p, id0, r, n, encrypt_metadata=True):
    """Algorithm 2: the file key for R2-R4."""
    m = pad_pw(upw) + o[:32] + struct.pack("<i", p) + id0
    if r >= 4 and not encrypt_metadata:
        m += b"\xff\xff\xff\xff"
    h = hashlib.md5(m).digest()
    if r >= 3:
        for _ in range(50):
            h = hashlib.md5(h[:n]).digest()
    return h[:n]


def alg45_user(key, id0, r):
    """Algorithms 4 (R2) and 5 (R3, R4): the /U value."""
    if r == 2:
        return rc4(key, PAD)
    h = rc4(key, hashlib.md5(PAD + id0).digest())
    for i in range(1, 20):
        h = rc4(bytes(b ^ i for b in key), h)
    return h + det_bytes("u-pad", 16)


def hash_2b(pw, salt, udata):
    """Algorithm 2.B (R6)."""
    k = hashlib.sha256(pw + salt + udata).digest()
    i = 0
    while True:
        k1 = (pw + k + udata) * 64
        e = cbc_encrypt(k[:16], k[16:32], k1, pad=False)
        s = sum(e[:16]) % 3
        k = [hashlib.sha256, hashlib.sha384, hashlib.sha512][s](e).digest()
        i += 1
        if i >= 64 and e[-1] <= i - 32:
            break
    return k[:32]


def hash_r(r, pw, salt, udata):
    if r == 5:
        return hashlib.sha256(pw + salt + udata).digest()
    return hash_2b(pw, salt, udata)


def v5_values(r, upw, opw, file_key, p, encrypt_metadata, label):
    uvs, uks = det_bytes(label + "/uvs", 8), det_bytes(label + "/uks", 8)
    u = hash_r(r, upw, uvs, b"") + uvs + uks
    ue = cbc_encrypt(hash_r(r, upw, uks, b""), bytes(16), file_key, pad=False)
    ovs, oks = det_bytes(label + "/ovs", 8), det_bytes(label + "/oks", 8)
    o = hash_r(r, opw, ovs, u) + ovs + oks
    oe = cbc_encrypt(hash_r(r, opw, oks, u), bytes(16), file_key, pad=False)
    perms_plain = struct.pack("<i", p) + b"\xff\xff\xff\xff" + (b"T" if encrypt_metadata else b"F") \
        + b"adb" + det_bytes(label + "/perms", 4)
    perms = ecb_encrypt(file_key, perms_plain)
    return o, u, oe, ue, perms


# ---------------------------------------------------------------- PDF writing

def hexs(b):
    return b"<" + b.hex().encode() + b">"


class Crypt:
    """One encryption setup: how to encrypt strings and streams of object (num, gen)."""

    def __init__(self, name, v, r, bits, method, upw=b"", encrypt_metadata=True,
                 direct_encrypt=False):
        self.name, self.v, self.r, self.method = name, v, r, method
        self.encrypt_metadata = encrypt_metadata
        self.direct_encrypt = direct_encrypt
        self.n = bits // 8
        self.id0 = det_bytes(name + "/id0", 16)
        self.id1 = det_bytes(name + "/id1", 16)
        self.ivn = 0
        if v < 5:
            self.o = alg3_owner(b"owner", upw, r, self.n)
            self.key = alg2_key(upw, self.o, P_VALUE, self.id0, r, self.n, encrypt_metadata)
            self.u = alg45_user(self.key, self.id0, r)
            self.oe = self.ue = self.perms = None
        else:
            self.key = det_bytes(name + "/filekey", 32)
            self.o, self.u, self.oe, self.ue, self.perms = v5_values(
                r, upw, b"owner", self.key, P_VALUE, encrypt_metadata, name)

    def obj_key(self, num, gen):
        if self.method == "aesv3":
            return self.key
        m = self.key + struct.pack("<I", num)[:3] + struct.pack("<I", gen)[:2]
        if self.method == "aesv2":
            m += b"sAlT"
        return hashlib.md5(m).digest()[:min(self.n + 5, 16)]

    def enc(self, num, gen, data):
        k = self.obj_key(num, gen)
        if self.method == "rc4":
            return rc4(k, data)
        self.ivn += 1
        iv = det_bytes("%s/iv/%d" % (self.name, self.ivn), 16)
        return iv + cbc_encrypt(k, iv, data)

    def encrypt_dict(self):
        d = b"/Filter /Standard /V %d /R %d /P %d /O %s /U %s" % (
            self.v, self.r, P_VALUE, hexs(self.o), hexs(self.u))
        if self.v in (2, 4):
            d += b" /Length %d" % (self.n * 8)
        if self.v >= 4:
            cfm = {"rc4": b"/V2", "aesv2": b"/AESV2", "aesv3": b"/AESV3"}[self.method]
            d += b" /CF << /StdCF << /Type /CryptFilter /CFM %s /AuthEvent /DocOpen /Length %d >> >>" \
                 b" /StmF /StdCF /StrF /StdCF" % (cfm, self.n)
            if not self.encrypt_metadata:
                d += b" /EncryptMetadata false"
        if self.v == 5:
            d += b" /Length 256 /OE %s /UE %s /Perms %s" % (hexs(self.oe), hexs(self.ue), hexs(self.perms))
        return b"<< " + d + b" >>"


def build(c):
    buf = bytearray(HEADER)
    offs = {}

    def add(n, raw):
        offs[n] = len(buf)
        buf.extend(raw)

    def obj(n, body):
        add(n, b"%d 0 obj\n%s\nendobj\n" % (n, body))

    def stream(n, dict_inner, data):
        add(n, b"%d 0 obj\n<< %s /Length %d >>\nstream\n" % (n, dict_inner, len(data))
            + data + b"\nendstream\nendobj\n")

    obj(1, b"<< /Type /Catalog /Pages 2 0 R >>")
    obj(2, b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>")
    obj(3, b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R >>")
    stream(4, b"/Filter /FlateDecode", c.enc(4, 0, zlib.compress(CONTENT, 9)))
    obj(5, b"<< /Title %s /Producer %s >>" % (hexs(c.enc(5, 0, TITLE)),
                                               hexs(c.enc(5, 0, b"generate.py"))))
    member = b"<< /Kind %s /N 6 >>" % hexs(KIND)
    header = b"6 0 "
    objstm_plain = header + member
    stream(7, b"/Type /ObjStm /N 1 /First %d /Filter /FlateDecode" % len(header),
           c.enc(7, 0, zlib.compress(objstm_plain, 9)))
    types = {6: (2, 7, 0)}
    if c.v >= 4:
        stream(10, b"/Filter [/Crypt /FlateDecode] /DecodeParms [<< /Name /Identity >> null]",
               zlib.compress(IDENTITY_DATA, 9))
    if not c.encrypt_metadata:
        stream(11, b"/Type /Metadata /Subtype /XML", METADATA)
    if not c.direct_encrypt:
        obj(9, c.encrypt_dict())
        enc_entry = b"/Encrypt 9 0 R"
    else:
        enc_entry = b"/Encrypt " + c.encrypt_dict()
    size = 12
    # xref stream: object 8, W [1 4 2], uncompressed
    off8 = len(buf)
    offs[8] = off8
    data = b""
    for i in range(size):
        if i in types:
            t = types[i]
        elif i in offs and i != 0:
            t = (1, offs[i], 0)
        else:
            t = (0, 0, 65535 if i == 0 else 0)
        data += struct.pack(">BIH", *t)
    d = b"/Type /XRef /Size %d /W [1 4 2] /Root 1 0 R /Info 5 0 R %s /ID [%s %s]" % (
        size, enc_entry, hexs(c.id0), hexs(c.id1))
    buf.extend(b"8 0 obj\n<< %s /Length %d >>\nstream\n" % (d, len(data)) + data
               + b"\nendstream\nendobj\n")
    buf.extend(b"startxref\n%d\n%%%%EOF\n" % off8)
    return bytes(buf)


SETUPS = [
    # file name, constructor arguments
    ("rc4-40.pdf", dict(v=1, r=2, bits=40, method="rc4", direct_encrypt=True)),
    ("rc4-128.pdf", dict(v=2, r=3, bits=128, method="rc4")),
    ("rc4-v4.pdf", dict(v=4, r=4, bits=128, method="rc4")),
    ("aesv2.pdf", dict(v=4, r=4, bits=128, method="aesv2", encrypt_metadata=False)),
    ("aesv3-r5.pdf", dict(v=5, r=5, bits=256, method="aesv3")),
    ("aesv3.pdf", dict(v=5, r=6, bits=256, method="aesv3")),
    ("userpw-rc4-128.pdf", dict(v=2, r=3, bits=128, method="rc4", upw=b"secret")),
    ("userpw-aesv3.pdf", dict(v=5, r=6, bits=256, method="aesv3", upw=b"secret")),
]


def files():
    return [(name, build(Crypt(name, **kw))) for name, kw in SETUPS]


def vectors():
    """Values pasted into SafePdf/Core/Crypt.lean #guards."""
    c = Crypt("rc4-128.pdf", **dict(SETUPS[1][1]))
    print("alg2 R3 O   =", c.o.hex())
    print("alg2 R3 id0 =", c.id0.hex())
    print("alg2 R3 key =", c.key.hex())
    print("alg2 R3 U   =", c.u.hex())
    salt = bytes(range(8))
    print("2.B('', 0001..07, '') =", hash_2b(b"", salt, b"").hex())
    print("2.B('ab', 0001..07, '') =", hash_2b(b"ab", salt, b"").hex())
    print("objkey aesv2 key=00..0f num=5 gen=0:",
          hashlib.md5(bytes(range(16)) + b"\x05\x00\x00\x00\x00sAlT").digest().hex())


def main():
    if "--vectors" in sys.argv:
        vectors()
        return 0
    check = "--check" in sys.argv
    bad = 0
    for name, data in files():
        path = os.path.join(HERE, name)
        if check:
            try:
                with open(path, "rb") as f:
                    cur = f.read()
            except OSError:
                cur = None
            ok = cur == data
            print("%s %s (%d bytes, sha256 %s)" % ("ok  " if ok else "DIFF", name, len(data),
                                                 hashlib.sha256(data).hexdigest()[:16]))
            bad += 0 if ok else 1
        else:
            with open(path, "wb") as f:
                f.write(data)
            print("wrote %s (%d bytes)" % (name, len(data)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
