import X86Proofs.Program.Execution
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.Entry

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Entry.Branch

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bytes : List UInt8 := [0x48,0x83,0xfa,0x41,0x73,0x0e]

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : CodeIn (codeRange 0x11637a bytes) s)
    (rip : s.RIP = 0x11637a)
    (next : (0x11637e : BitVec 64) ≠ boundary.rip)
    (short : (0x116380 : BitVec 64) ≠ boundary.rip)
    (long : (0x11638e : BitVec 64) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .rdx).toNat ≤ 64 then 0x116380 else 0x11638e) ∧
      AgreesExcept [.flags,.rip] s t := by
  obtain ⟨u, run, readyU, compared⟩ :=
    (cmp_r64_imm8_effect_step 0x11637a 0x48 0xfa 0x41
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (loaded.mono (codeRange_slice_subset 0x11637a bytes 0 4)) rip next
  have frame : AgreesExcept [.flags,.rip] s u := compared.agrees
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel8_effect_step 0x11637e 3 0xe u readyU
    ((frame.codeIn (by simp [Component.Covers]) loaded).mono
      (codeRange_slice_subset 0x11637a bytes 4 2))
    ⟨compared.rip, fun _ => by decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide ((s.regValue .rdx).toNat < 65) := by
    rw [compared.flags.1]
    change (s.regValue .rdx).ult 65 = _
    rw [BitVec.ult_eq_decide]
    rfl
  have target : t.RIP =
      (if (s.regValue .rdx).toNat ≤ 64 then 0x116380 else 0x11638e) := by
    rw [jumped.rip]
    change (if !(StatusFlags.ofRFLAGS u.RFLAGS).CF then 0x11638e else 0x116380) = _
    rw [carry]
    by_cases h : (s.regValue .rdx).toNat ≤ 64
    · have hh : (s.regValue .rdx).toNat < 65 := by omega
      simp only [hh, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
    · have hh : ¬ (s.regValue .rdx).toNat < 65 := by omega
      simp only [hh, decide_false, Bool.not_false, ↓reduceIte, h]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact short
    · exact long
  exact ⟨t, run.trans advance, readyT, target,
    (frame.trans jumped.agrees).mono (by simp [jccEffect,branchEffect,Effect.components])⟩

end Hkdf.Proofs.Key.Entry.Branch
