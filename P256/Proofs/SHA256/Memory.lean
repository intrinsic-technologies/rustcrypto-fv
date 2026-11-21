import P256.Proofs.SHA256.Frame.State

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
  {hash : Array UInt32} {input : ByteArray} {count : Nat}

theorem CompressionPre.inputSize (pre : CompressionPre initial boundary hash input count) :
    input.size = 64 * count := pre.inputBytes.1

theorem CompressionPre.inputPointer_toNat
    (pre : CompressionPre initial boundary hash input count) {index : Nat}
    (hindex : index ≤ count) :
    (initial.regValue .rsi + BitVec.ofNat 64 (64 * index)).toNat =
      (initial.regValue .rsi).toNat + 64 * index := by
  have hb : (initial.regValue .rsi).toNat + 64 * count < 2^32 := pre.inputBounded
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem CompressionPre.inputPointer_eq_iff
    (pre : CompressionPre initial boundary hash input count) {index : Nat}
    (hindex : index ≤ count) :
    initial.regValue .rsi + BitVec.ofNat 64 (64 * index) =
      initial.regValue .rsi + BitVec.ofNat 64 (64 * count) ↔ index = count := by
  constructor
  · intro he
    have h := congrArg BitVec.toNat he
    rw [pre.inputPointer_toNat hindex, pre.inputPointer_toNat (Nat.le_refl count)] at h
    omega
  · rintro rfl
    rfl

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_input_byte (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {i : Nat} (hi : i < 64 * count) :
    current.external[initial.regValue .rsi + BitVec.ofNat 64 i]? =
      initial.external[initial.regValue .rsi + BitVec.ofNat 64 i]? := by
  apply state.frame
  intro region hr
  have hin : (registerRegion initial .rsi (64 * count)).Contains
      (initial.regValue .rsi + BitVec.ofNat 64 i).toNat :=
    memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : region = registerRegion initial .rdi 32 ∨ region = Stack.region initial 336 := by
    simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_input_block_readable (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {index : Nat} (hi : index < count) :
    MemReadable current (initial.regValue .rsi + BitVec.ofNat 64 (64 * index)) 64 := by
  apply P256.Proofs.Program.readable_of_grow _ state.allocated
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · rw [pre.inputPointer_toNat (Nat.le_of_lt hi)]
    change (initial.regValue .rsi).toNat ≤ (initial.regValue .rsi).toNat + 64 * index
    omega
  · rw [pre.inputPointer_toNat (Nat.le_of_lt hi)]
    change (initial.regValue .rsi).toNat + 64 * index + 64 ≤
      (initial.regValue .rsi).toNat + 64 * count
    omega

end P256.Proofs.SHA256
