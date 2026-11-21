import P256.Proofs.Signing.Wrapper.Hash.Initial
import P256.Proofs.SHA256.Mathematics.Padding.Tail

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem message_slice [Bindings] {initial start s : RamState} {secret message : ByteArray} {frameOffset : Nat}
    (pre : HashEntry initial start secret message)
    (frame : Frame initial start s frameOffset)
    {offset count : Nat} (span : offset + count ≤ message.size) :
    let region := MemoryRegion.mk
      (memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 offset).toNat count
    region.Bounded ∧ region.Disjoint (Stack.region initial 5112) ∧
      region.HasBytes s.external (message.extract offset (offset + count)) := by
  have bounded : (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat +
      message.size < 2^32 := (message_input pre frame).1
  have address : (memLoad initial.external (initial.regValue .rdi + 8) 64 +
      BitVec.ofNat 64 offset).toNat =
      (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + offset :=
    toNat_add_ofNat _ _ (by omega)
  dsimp only
  constructor
  · change (memLoad initial.external (initial.regValue .rdi + 8) 64 +
      BitVec.ofNat 64 offset).toNat + count < 2^32
    rw [address]
    omega
  constructor
  · intro a ha hb
    apply (message_input pre frame).2.2 a ?_ hb
    change (memLoad initial.external (initial.regValue .rdi + 8) 64 +
      BitVec.ofNat 64 offset).toNat ≤ a ∧ a <
      (memLoad initial.external (initial.regValue .rdi + 8) 64 +
      BitVec.ofNat 64 offset).toNat + count at ha
    rw [address] at ha
    change (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat ≤ a ∧
      a < (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + message.size
    constructor <;> omega
  · have size : (message.extract offset (offset + count)).size = count := by
      rw [ByteArray.size_extract, Nat.min_eq_left span]
      omega
    refine ⟨size, fun i => ?_⟩
    have hi : i.val < count := by have := i.isLt; omega
    have byte := (message_input pre frame).2.1.2 ⟨offset + i.val, by omega⟩
    change s.external[BitVec.ofNat 64 ((memLoad initial.external (initial.regValue .rdi + 8) 64 +
      BitVec.ofNat 64 offset).toNat + i.val)]? = _
    rw [address]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte ⊢
    simp only [messageRegion] at byte
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    rw [show memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 offset +
      BitVec.ofNat 64 i.val = memLoad initial.external (initial.regValue .rdi + 8) 64 +
      BitVec.ofNat 64 (offset + i.val) by rw [BitVec.ofNat_add, BitVec.add_assoc]]
    rw [ByteArray.getElem_extract]
    simpa only [messageRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte

end P256.Proofs.Signing.Wrapper.Hash.Absorb
