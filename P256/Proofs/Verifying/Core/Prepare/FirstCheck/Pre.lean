import P256.Proofs.Verifying.Core.Prepare.FirstCheck.Block
import P256.Proofs.Verifying.Core.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare.FirstCheck

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t)
    (rip : t.RIP = 0x10da55) (r8 : t.regValue .rbx = s.regValue .r8) : Pre t := by
  refine ⟨rip,?_,?_,?_,?_⟩
  · intro k hk
    rw [r8]
    exact signature_readable hp state (by omega)
  · intro offset ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact local_writable8 hp state (by decide) (by decide)
  · intro offset ho codeOffset len hl
    have bound : offset ≤ 152 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    have code : (0x10da55 : BitVec 64) + BitVec.ofNat 64 codeOffset =
        Extracted.textAddress + BitVec.ofNat 64 (0xda55+codeOffset) := by
      rw [BitVec.ofNat_add,← BitVec.add_assoc]
      rfl
    rw [code]
    exact stack_code (frameOffset := 1176) hp.toCalleePre state (by decide) (by omega) (by omega)
  · intro k hk j hj
    rw [r8]
    exact local_signature_apart hp state (by omega) (by omega)

end P256.Proofs.Verifying.Core.Prepare.FirstCheck
