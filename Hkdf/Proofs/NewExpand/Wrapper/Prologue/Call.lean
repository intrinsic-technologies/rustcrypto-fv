import Hkdf.Proofs.NewExpand.Wrapper.Frame
import Hkdf.Proofs.Common.CallFrame.Stack

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem outerBoundary {s : RamState} (ret : ValidReturnAddress s) :
    ¬ InProgram (returnBoundary s).rip := by
  obtain ⟨address, word, _, outside⟩ := ret
  have loaded := Memory.memLoad_of_loadBytes64 word.2
  change memLoad s.external (BitVec.ofNat 64 (stackPtr s).toNat) 64 = address at loaded
  change ¬ InProgram (memLoad s.external (stackPtr s) 64)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at loaded
  rwa [loaded]

theorem callExtract [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (run : Wrapper.Running initial s) (rip : s.RIP = 0x102005)
    (rsp : stackPtr s = stackPtr initial - 360) :
    ∃ t, Wrapper.Running initial t ∧
      (callEffect (fun _ ↦ (0x10fa80 : BitVec 64)) 0x10200a s).Holds s t ∧
      returnBoundary t = ⟨0x10200a, stackPtr initial - 360⟩ := by
  have avoid := (hCall.stackSeparation.2 _ (Vector.mem_singleton_self _)).2
  have step := call_rel32_effect_step 0x102005 0xda76 (by decide)
  change StepEffect (PushPre 0x102005 5)
    (codeRange 0x102005 (encodeCallRel32 0xda76))
    (callEffect (fun _ ↦ (0x10fa80 : BitVec 64)) 0x10200a) at step
  exact run.call_stack hCall.stack avoid (depth := 360) rsp (by decide) (by decide)
    0x2005 5 (by decide) rip step
    (programText_slice (programLoaded_codeIn run.loaded) 0x2005
      (encodeCallRel32 0xda76) (by decide) (by decide +kernel)) id
    (boundary_ne_program (outerBoundary hCall.returnAddress)
      (inProgram_of_textOffset 0xfa80 (by decide)))

end Hkdf.Proofs.NewExpand.Wrapper
