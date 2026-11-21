import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.State
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.SecretKeyFromBytes.Choice
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes (ChoicePre choice_code_loaded choice_correct)
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame hiding FrameState

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def choiceClobbers (s : RamState) : List Component :=
  [.reg 0, .reg 4, .flags, .rip,
    .mem (stackPtr s - 160#64) 8, .mem (stackPtr s - 161#64) 1]

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (offset : Nat) (disp : BitVec 32) (bound : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Stage s u boundary ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + 5#64 ∧
      u.regValue .rax = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (choiceClobbers s) t u := by
  obtain ⟨u, run, ready, rsp, ip, value, agrees⟩ :=
    Program.ScalarFrame.choice_step pre (frameOffset := 152) (by decide) (by decide)
      (Program.readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
      state.rsp offset disp bound bytes target rip
  have f : AgreesExcept (choiceClobbers s) t u := agrees
  have w : WritesWithin (choiceClobbers s) #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro c hc a ha
    simp only [choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨Program.ScalarFrame.workRegion s 288, by simp, work_contains pre (by decide) (by decide) ha⟩
    · exact ⟨Program.ScalarFrame.workRegion s 288, by simp, work_contains pre (by decide) (by decide) ha⟩
  exact ⟨u, state.after pre run ready f w (rsp.trans state.rsp)
    (by simp [choiceClobbers]), ip, value, f⟩

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish
