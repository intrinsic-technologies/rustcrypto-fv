import Standards.NIST.AES.Tests
import Standards.NIST.EllipticCurves.Tests
import Standards.NIST.GCM.Tests
import Standards.NIST.SHA1.Tests
import Standards.NIST.SHA2.Tests
import Standards.NIST.SHA3.Tests
import Standards.RFC.BaseEncodings.Tests
import Standards.RFC.DeterministicSigning.Tests
import Standards.RFC.HMAC.Tests
import Standards.RFC.MD5.Tests
import Standards.RFC.HKDF.Tests
import Standards.SECG.ECC.Tests
import Standards.SECG.DomainParameters.Tests
import Standards.RFC.ChaCha20Poly1305.Tests
import Standards.RFC.ChaCha20Poly1305.ChaCha20.Tests
import Standards.RFC.ChaCha20Poly1305.AEAD.Tests

/-!
# Standards tests

Executable checks of the shared definitions against published test vectors. A subject's tests are in
its `Tests.lean`, which names the vector files it reads. Run from the repository root with
`lake test -- Standards` for every subject, or `lake test -- Standards.NIST.SHA2` for one.
`ci/crates.py tests` selects subjects by these names, so each is its test module's name without
`.Tests`.

This module only collects the subjects' suites and has no source of its own. Each subject's test
module names the source of its vectors, and the coverage table of `Standards/README.md` lists the
document each subject defines:
https://github.com/intrinsic-technologies/rustcrypto-fv/blob/main/Standards/README.md
-/

namespace Standards.Tests

/-- Each subject's suite, by the name of its module -/
def subjects : List (String × IO Unit) := [
  ("Standards.NIST.AES", NIST.AES.Tests.run),
  ("Standards.NIST.SHA1", NIST.SHA1.Tests.run),
  ("Standards.NIST.SHA2", NIST.SHA2.Tests.run),
  ("Standards.NIST.SHA3", NIST.SHA3.Tests.run),
  ("Standards.NIST.EllipticCurves", NIST.EllipticCurves.Tests.run),
  ("Standards.NIST.GCM", NIST.GCM.Tests.run),
  ("Standards.RFC.HMAC", RFC.HMAC.Tests.run),
  ("Standards.RFC.DeterministicSigning", RFC.DeterministicSigning.Tests.run),
  ("Standards.RFC.BaseEncodings", RFC.BaseEncodings.Tests.run),
  ("Standards.RFC.MD5", RFC.MD5.Tests.run),
  ("Standards.SECG.ECC", SECG.ECC.Tests.run),
  ("Standards.SECG.DomainParameters", SECG.DomainParameters.Tests.run),
  ("Standards.RFC.HKDF", RFC.HKDF.Tests.run),
  ("Standards.RFC.ChaCha20Poly1305", RFC.ChaCha20Poly1305.Tests.run),
  ("Standards.RFC.ChaCha20Poly1305.ChaCha20", RFC.ChaCha20Poly1305.ChaCha20.Tests.run),
  ("Standards.RFC.ChaCha20Poly1305.AEAD", RFC.ChaCha20Poly1305.AEAD.Tests.run),
]

/-- Runs every `Standards` test, throwing on the first failure -/
def run : IO Unit := do
  for (_, suite) in subjects do
    suite

end Standards.Tests
