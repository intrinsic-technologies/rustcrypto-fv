import P256.Proofs.HMAC.Finalize.FrameSupport
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common

theorem state_address_toNat [Bindings] {s : RamState} {boundary : ReturnBoundary} {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) {offset : Nat} (bound : offset ≤ stateBytes) :
    (s.regValue .rdi + BitVec.ofNat 64 offset).toNat = (s.regValue .rdi).toNat + offset := by
  apply toNat_add_ofNat
  have low : (s.regValue .rdi).toNat + stateBytes < 2^32 := pre.outputBounded
  omega

theorem state_contains [Bindings] {s : RamState} {boundary : ReturnBoundary} {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ stateBytes)
    (covered : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion s .rdi stateBytes).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, state_address_toNat pre (by omega)]
  change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + stateBytes
  constructor <;> omega

theorem state_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {stateBytes reserve : Nat} {depth : BitVec 64} (pre : HashCalleePre s boundary entry stateBytes reserve)
    (state : ScalarFrame.FrameState s t 0 reserve depth) {offset len : Nat} (bound : offset + len ≤ stateBytes) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 offset) len := by
  apply P256.Proofs.Program.readable_of_grow (t := t) ?_ state.allocated
  apply memoryRegion_memReadable pre.outputBounded pre.outputAllocated
  · rw [state_address_toNat pre (by omega)]
    change (s.regValue .rdi).toNat ≤ _
    omega
  · rw [state_address_toNat pre (by omega)]
    change (s.regValue .rdi).toNat + offset + len ≤ (s.regValue .rdi).toNat + stateBytes
    omega

theorem output_address_toNat [Bindings] {s : RamState} {boundary : ReturnBoundary} {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) {offset : Nat} (bound : offset ≤ 32) :
    (s.regValue .rsi + BitVec.ofNat 64 offset).toNat = (s.regValue .rsi).toNat + offset := by
  apply toNat_add_ofNat
  have low : (s.regValue .rsi).toNat + 32 < 2^32 := pre.inputBounded
  omega

theorem output_contains [Bindings] {s : RamState} {boundary : ReturnBoundary} {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ 32)
    (covered : (Component.mem (s.regValue .rsi + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion s .rsi 32).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, output_address_toNat pre (by omega)]
  change (s.regValue .rsi).toNat ≤ _ ∧ _ < (s.regValue .rsi).toNat + 32
  constructor <;> omega

theorem output_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {stateBytes reserve : Nat} {depth : BitVec 64} (pre : HashCalleePre s boundary entry stateBytes reserve)
    (state : ScalarFrame.FrameState s t 0 reserve depth) {offset len : Nat} (bound : offset + len ≤ 32) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) len := by
  apply P256.Proofs.Program.readable_of_grow (t := t) ?_ state.allocated
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · rw [output_address_toNat pre (by omega)]
    change (s.regValue .rsi).toNat ≤ _
    omega
  · rw [output_address_toNat pre (by omega)]
    change (s.regValue .rsi).toNat + offset + len ≤ (s.regValue .rsi).toNat + 32
    omega

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {stateBytes reserve : Nat} {depth : BitVec 64} (pre : HashCalleePre s boundary entry stateBytes reserve)
    (state : ScalarFrame.FrameState s t 0 reserve depth) {offset len : Nat} (bound : offset + len ≤ 32)
    (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (s.regValue .rsi + BitVec.ofNat 64 offset) len := by
  have readable := output_readable pre state bound
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi reserved
  exact pre.digestAvoids _
    (output_contains pre bound ⟨i, hi, rfl⟩) (.inr reserved)

theorem output_code [Bindings] {s : RamState} {boundary : ReturnBoundary} {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) {offset len pc codeLen : Nat}
    (bound : offset + len ≤ 32) (codeBound : pc + codeLen ≤ 118431) :
    RangeApart (s.regValue .rsi + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 pc) codeLen := by
  intro i hi j hj eq
  apply pre.digestAvoids _
    (output_contains pre bound ⟨i, hi, rfl⟩)
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (pc+j) (by omega)


end P256.Proofs.HMAC.Finalize
