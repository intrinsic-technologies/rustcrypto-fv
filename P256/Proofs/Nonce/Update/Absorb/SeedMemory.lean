import P256.Proofs.Nonce.Update.Absorb.Memory
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Program.ReadWrite.RepString

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
  {original : State} {depth : Nat} {secret reduced : ByteArray}

theorem immutable_bytes {a : BitVec 64} {len : Nat}
    (frame : ScalarFrame.FrameState initial s 64 1856 depth)
    (bounded : (MemoryRegion.mk a.toNat len).Bounded)
    (stateApart : (MemoryRegion.mk a.toNat len).Disjoint (registerRegion initial .rdi 64))
    (stackApart : (MemoryRegion.mk a.toNat len).Disjoint (Stack.region initial 1856)) :
    ∀ i < len, s.external[a + BitVec.ofNat 64 i]? = initial.external[a + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.frame
  intro region member inside
  have within := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi
  have cases : region = registerRegion initial .rdi 64 ∨ region = Stack.region initial 1856 := by
    simpa using member
  rcases cases with rfl | rfl
  · exact stateApart _ within inside
  · exact stackApart _ within inside

theorem seed_bytes {address : BitVec 64} {bytes : ByteArray}
    (frame : ScalarFrame.FrameState initial s 64 1856 depth)
    (seed : UpdateSeedAt initial address bytes) :
    ∀ i < bytes.size, s.external[address + BitVec.ofNat 64 i]? =
      initial.external[address + BitVec.ofNat 64 i]? :=
  immutable_bytes frame seed.bounded seed.stateApart seed.stackApart

theorem descriptor_bytes (pre : UpdateSeededPre initial boundary original secret reduced)
    (frame : ScalarFrame.FrameState initial s 64 1856 depth) :
    ∀ i < 48, s.external[initial.regValue .rsi + BitVec.ofNat 64 i]? =
      initial.external[initial.regValue .rsi + BitVec.ofNat 64 i]? :=
  immutable_bytes frame pre.descriptorsBounded pre.descriptorsStateApart pre.descriptorsStackApart

omit [Bindings] in
theorem seed_offset_toNat {address : BitVec 64} {bytes : ByteArray}
    (seed : UpdateSeedAt initial address bytes) {offset : Nat} (bound : offset ≤ bytes.size) :
    (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
  apply toNat_add_ofNat
  have size : address.toNat + bytes.size < 2^32 := seed.bounded
  omega

omit [Bindings] in
theorem seed_subregion {address : BitVec 64} {bytes : ByteArray}
    (seed : UpdateSeedAt initial address bytes) {offset len : Nat} (bound : offset + len ≤ bytes.size)
    {a : Nat} (inside : (MemoryRegion.mk (address + BitVec.ofNat 64 offset).toNat len).Contains a) :
    (MemoryRegion.mk address.toNat bytes.size).Contains a := by
  change (address + BitVec.ofNat 64 offset).toNat ≤ a ∧
    a < (address + BitVec.ofNat 64 offset).toNat + len at inside
  rw [seed_offset_toNat seed (by omega)] at inside
  change address.toNat ≤ a ∧ a < address.toNat + bytes.size
  exact ⟨by omega, by omega⟩

theorem descriptor_readable (pre : UpdateSeededPre initial boundary original secret reduced)
    (frame : ScalarFrame.FrameState initial s 64 1856 depth) {offset len : Nat} (bound : offset + len ≤ 48) :
    MemReadable s (initial.regValue .rsi + BitVec.ofNat 64 offset) len := by
  apply P256.Proofs.Program.readable_of_grow _ frame.allocated
  have low : (initial.regValue .rsi).toNat + 48 < 2^32 := pre.descriptorsBounded
  have address : (initial.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rsi).toNat + offset := toNat_add_ofNat _ _ (by omega)
  apply memoryRegion_memReadable pre.descriptorsBounded pre.descriptorsAllocated
  · rw [address]
    change (initial.regValue .rsi).toNat ≤ (initial.regValue .rsi).toNat + offset
    omega
  · rw [address]
    change (initial.regValue .rsi).toNat + offset + len ≤ (initial.regValue .rsi).toNat + 48
    omega

theorem descriptor_load (pre : UpdateSeededPre initial boundary original secret reduced)
    (frame : ScalarFrame.FrameState initial s 64 1856 depth) {offset : Nat} {value : BitVec 64}
    (bound : offset + 8 ≤ 48)
    (loaded : loadBytes initial.external (initial.regValue .rsi + BitVec.ofNat 64 offset) 8 = .ok value) :
    memLoad s.external (initial.regValue .rsi + BitVec.ofNat 64 offset) 64 = value := by
  have copy := P256.Proofs.Program.loadBytes_ok_copy
    (P256.Proofs.Program.copied_sub (descriptor_bytes pre frame) bound) loaded
  exact Except.ok.inj ((Bytes.of_memLoad (n := 64)
    (descriptor_readable pre frame bound).mem).loadBytes64.symm.trans copy)

end P256.Proofs.Nonce.Update.Absorb
