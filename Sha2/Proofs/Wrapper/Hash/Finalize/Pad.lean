import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Load
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Setup
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Fill
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Bytes
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Finish

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pad [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v)
    (buffered : Buffered initial s message v) (rip : s.RIP = (v.pc 0x1bb)) :
    ∃ t, Padded initial t message v := by
  obtain ⟨loaded, loadResult⟩ := Pad.load ctx buffered rip
  obtain ⟨marked, setupResult⟩ := Pad.setup ctx loadResult
  exact Pad.finish ctx setupResult

end Sha2.Proofs.Wrapper.Hash.Finalize
