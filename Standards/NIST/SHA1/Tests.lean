import Standards.NIST.SHA1
import Standards.NIST.SHA2.Tests

/-!
# FIPS 180-4 SHA-1 tests

The vectors are the unmodified bit- and byte-oriented SHA-1 response files of the NIST CAVP suite:
https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing

| Orientation | Short | Long | Monte Carlo checkpoints |
| ----------- | ----: | ---: | ----------------------: |
| Bit         |   513 |  512 |                     100 |
| Byte        |    65 |   64 |                     100 |

They run through the FIPS 180-4 test harness of `Standards.NIST.SHA2.Tests`, which also checks
padding and block continuation; each Monte Carlo suite performs 100,000 hashes following SHAVS §6.4.
-/

namespace Standards.NIST.SHA1.Tests

open Standards.NIST.SHA2 Standards.NIST.SHA2.Tests Standards.NIST.SHA1

private def sha1 : Algorithm where
  name := "SHA-1"
  filePrefix := "SHA1"
  byteCount := 20
  hash := SHA1
  pad := SHA256.pad
  blockBits := 512
  lengthBits := 64
  continues padded :=
    let M := SHA256.parse padded
    let split := M.size / 2
    (M.extract split M.size).foldl compress (hashComputation (M.extract 0 split)) ==
      hashComputation M
  shortCount byteOriented := if byteOriented then 65 else 513
  longCount byteOriented := if byteOriented then 64 else 512

def run : IO Unit := do
  checkDigest sha1 (SHA1 (bytesToBits "abc".toUTF8))
    "a9993e364706816aba3e25717850c26c9cd0d89d" "abc"
  let mut jobs := #[]
  let mut messageCount := 0
  for (orientation, byteOriented) in [("Bit", false), ("Byte", true)] do
    let short := sha1.shortCount byteOriented
    let long := sha1.longCount byteOriented
    messageCount := messageCount + short + long
    let job ← IO.asTask do
      let dir := System.FilePath.mk "Standards/NIST/SHA1/Vectors" / orientation
      messages sha1 (dir / "SHA1ShortMsg.rsp") short byteOriented
      messages sha1 (dir / "SHA1LongMsg.rsp") long byteOriented
      monteCarlo sha1 (dir / "SHA1Monte.rsp")
    jobs := jobs.push job
  for job in jobs do
    IO.ofExcept job.get
  let checkpoints := 100 * jobs.size
  IO.println s!"Passed {messageCount} NIST SHA-1 message vectors and {checkpoints} Monte Carlo \
    checkpoints ({1000 * checkpoints} hashes), padding, and continuation checks"

end Standards.NIST.SHA1.Tests
