import P256.Proofs.Projective.Multiply.Machine.Radix.Digits

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix

theorem digit_address [Bindings] {s t : RamState} (state : State s t) (i : Nat) :
    stackPtr t + BitVec.ofNat 64 (8+i) = stackPtr s - 112 + BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, ScalarFrame.scalar_stack_address state.rsp (frameOffset := 120) (offset := 8) (by decide) (by decide)]
  rfl

theorem half_address [Bindings] {s t : RamState} (state : State s t) {counter offset i : Nat}
    (hc : (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 counter)
    (he : counter+offset = 8+i) :
    halfAddress t (BitVec.ofNat 64 offset) = stackPtr s - 112 + BitVec.ofNat 64 i := by
  unfold halfAddress
  rw [hc, ← BitVec.ofNat_add, he]
  exact digit_address state i

theorem digit_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t) {i : Nat} (hi : i < 65) :
    MemWritable t (stackPtr s - 112 + BitVec.ofNat 64 i) 1 := by
  rw [← digit_address state i]
  have hw := state.stack_writable (frameOffset := 120) pre (offset := 8+i) (len := 1) (by decide) (by omega) (by decide)
  exact ⟨hw.low, hw.mem, hw.tables⟩

theorem half_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {i codeOffset : Nat} {offset : BitVec 64}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t) (hi : i < 64)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (codeBound : codeOffset + 23 ≤ 118431)
    (addr : halfAddress t offset = stackPtr s - 112 + BitVec.ofNat 64 i) :
    HalfPre (Extracted.textAddress + BitVec.ofNat 64 codeOffset) offset t := by
  have nextAddr : halfAddress t (offset+1) = stackPtr s - 112 + BitVec.ofNat 64 (i+1) := by
    rw [BitVec.ofNat_add]
    change halfAddress t (offset+1) = (stackPtr s - 112) + (BitVec.ofNat 64 i + 1)
    rw [← BitVec.add_assoc, ← addr]
    simp only [halfAddress, BitVec.add_assoc]
  refine ⟨rip, ?_, ?_, ?_⟩
  · rw [nextAddr]
    exact (digit_writable pre state (by omega)).readable
  · rw [addr]
    exact digit_writable pre state (by omega)
  · intro start len bound
    rw [addr, ← digit_address state i, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.stack_code (frameOffset := 120) pre (by decide) (by omega) (by omega)

theorem half_counter {t u : RamState} {p offset : BitVec 64} {src dst : BitVec 5}
    (hs : src = 0 ∨ src = 2) (hd : dst = 0 ∨ dst = 2)
    (effect : (halfEffect p src dst offset t).Holds t u) :
    (Operand.reg 1 : Operand 64).read u = (Operand.reg 1 : Operand 64).read t := by
  apply effect.agrees.read
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp [halfEffect, Effect.components]

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
