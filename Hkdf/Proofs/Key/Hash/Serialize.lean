import Hkdf.Proofs.Key.Hash.Serialize.Standard
import Hkdf.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Hkdf.Spec.Program

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1165c9 bytes) s :=
  Hkdf.Proofs.Common.Machine.programText_slice
    (Hkdf.Proofs.Common.Machine.programLoaded_codeIn loaded) 0x165c9 bytes
    (by decide +kernel) (by decide +kernel)

end Hkdf.Proofs.Key.Hash.Serialize
