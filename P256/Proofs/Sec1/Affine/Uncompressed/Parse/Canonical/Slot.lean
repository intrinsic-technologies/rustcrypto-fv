import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Sec1.Affine.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BorrowPre (pc : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = pc
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 16) 8
  avoids : ∀ a, (Component.mem (stackPtr s + 16) 8).Covers a → ¬ InProgram a

theorem BorrowPre.apart {pc : BitVec 64} {s : RamState} (pre : BorrowPre pc s)
    (offset len : Nat) (bound : offset + len ≤ 118431) :
    RangeApart (stackPtr s + 16) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj eq
  apply pre.avoids _ ⟨i, hi, rfl⟩
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

theorem borrow_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {pc : BitVec 64} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = pc) : BorrowPre pc t := by
  refine ⟨rip, ScalarFrame.stack_writable pre.toCalleePre state (by decide) (by decide)
    (by decide), ?_⟩
  intro a ha hp
  have addr : stackPtr t + 16 = stackPtr s - 744 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [addr] at ha
  exact pre.avoids _ (by simp) _
    (ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ha) (.inl hp)

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
