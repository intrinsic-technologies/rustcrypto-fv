import K256.Proofs.Sec1.Parser.Guards
import K256.Proofs.Sec1.Parser.Control

namespace K256.Proofs.Verify.Transfer.PublicKey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Parser

theorem uncompressedGuards {a : Vector Value 53} {m : Ram} {ptr : BitVec 64}
    (si : a[6].get 64 = ptr) (dx : a[2].get 64 = 65) (r9 : a[9].width = 64)
    (read : LoadOk m ptr 1) (tag : memLoad m ptr 8 = 4)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2) :
    ∃ next, Reaches Extracted.programImage .l1063a7 a m .l1063d2 next m ∧
      GuardRegisters a next ∧ next[8].width = 64 ∧ next[9].width = 64 := by
  obtain ⟨b, jump, rcx, keep⟩ := tagBlock (code := Extracted.programImage) si read
  rw [tag, ite_eq_left (by decide)] at jump
  rw [tag] at rcx
  have cx : b[1].get 64 = (4 : BitVec 8).setWidth 64 := congrArg (Value.get 64) rcx
  obtain ⟨c, step, kept⟩ := lengthBlock (code := Extracted.programImage) cx
    ((congrArg (Value.get 64) (keep 2 (by decide))).trans dx) (by decide) image
  rw [ite_eq_left (by decide)] at step
  refine ⟨c, (reaches_jump jump).trans (reaches_jump step), fun i h => (kept i h).trans (keep i h), ?_⟩
  have hb : b[8].width = 64 ∧ b[9].width = 64 := by
    cfg_eval [b_l1063a7] at jump
    repeat' (split at jump)
    all_goals simp only [Transfer.jump.injEq, Location.mk.injEq, reduceCtorEq] at jump
    all_goals obtain ⟨_,rfl,_⟩ := jump; exact ⟨rfl,r9⟩
  cfg_eval [b_l1063c4] at step
  repeat' (split at step)
  all_goals simp only [Transfer.jump.injEq, Location.mk.injEq, reduceCtorEq] at step
  all_goals obtain ⟨_, rfl, _⟩ := step; exact hb

end K256.Proofs.Verify.Transfer.PublicKey
