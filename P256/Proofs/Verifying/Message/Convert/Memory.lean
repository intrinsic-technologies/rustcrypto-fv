import P256.Proofs.Verifying.Message.Input
import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem key_readable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Pre initial boundary message) (state : Message.Frame initial s)
    {offset len : Nat} (bound : offset + len ≤ 72) :
    MemReadable s (initial.regValue .rsi + BitVec.ofNat 64 offset) len := by
  have first : MemReadable initial (initial.regValue .rsi) 72 :=
    memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _)
  have low : (initial.regValue .rsi).toNat + 72 ≤ 2^32 := first.low
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.allocated _ (first.mem _ (by omega))

theorem key_flag {s : RamState} {address : BitVec 64} {key : Curve.Point}
    (input : Sec1.AffineAt s address key) :
    (memLoad s.external (address + 64) 32).setWidth 8 =
      if key = .infinity then 1 else 0 := by
  have load := storedByte_memLoad s.external (address + 64) (n := 32) 0 (by decide)
  have low : (memLoad s.external (address + 64) 32).setWidth 8 =
      ((s.external[address + 64]?).getD 0).toBitVec := by
    have eq := congrArg UInt8.toBitVec load
    simpa only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.ushiftRight_zero,
      BitVec.add_zero, memByte, PhysicalMemory.read, UInt8.toBitVec_ofNat', BitVec.setWidth,
      show ¬32 ≤ 8 by decide, dite_false] using eq
  rw [low]
  cases key <;> simp only [Sec1.AffineAt] at input
  all_goals exact congrArg (fun x : Option UInt8 => (x.getD 0).toBitVec) input.2.2

theorem copy_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {ip : BitVec 64} {source destination : RamState → BitVec 64}
    (pre : Pre initial boundary message) (state : Message.Frame initial s)
    {offset : Nat} (bound : offset + 32 ≤ 1176)
    (rip : s.RIP = ip) (dst : destination s = stackPtr s + BitVec.ofNat 64 offset)
    (readable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), MemReadable s (source s + i) 8)
    (apart : RangeApart (destination s) 32 (source s) 32) :
    Copy32.Pre ip source destination s := by
  refine ⟨rip, readable, ?_, apart, ?_⟩
  · intro i hi
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_writable (frameOffset := 1176) pre.toCalleePre state (offset := offset + 0) (len := 8)
          (by decide) (by omega) (by decide))
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_writable (frameOffset := 1176) pre.toCalleePre state (offset := offset + 8) (len := 8)
          (by decide) (by omega) (by decide))
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_writable (frameOffset := 1176) pre.toCalleePre state (offset := offset + 16) (len := 8)
          (by decide) (by omega) (by decide))
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_writable (frameOffset := 1176) pre.toCalleePre state (offset := offset + 24) (len := 8)
          (by decide) (by omega) (by decide))
  · intro i hi codeOffset codeLen codeBound
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_code (frameOffset := 1176) pre.toCalleePre state (offset := offset + 0) (len := 8)
          (by decide) (by omega) codeBound)
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_code (frameOffset := 1176) pre.toCalleePre state (offset := offset + 8) (len := 8)
          (by decide) (by omega) codeBound)
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_code (frameOffset := 1176) pre.toCalleePre state (offset := offset + 16) (len := 8)
          (by decide) (by omega) codeBound)
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (stack_code (frameOffset := 1176) pre.toCalleePre state (offset := offset + 24) (len := 8)
          (by decide) (by omega) codeBound)

theorem key_stack_apart [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Pre initial boundary message) (state : Message.Frame initial s)
    {offset sourceOffset : Nat} (bound : offset + 32 ≤ 1176) (sourceBound : sourceOffset + 32 ≤ 72) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) 32
      (initial.regValue .rsi + BitVec.ofNat 64 sourceOffset) 32 := by
  intro i hi j hj eq
  rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add] at eq
  apply pre.separation 0 2 (by decide) _
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
      (by omega : sourceOffset + j < 72))
  rw [← eq]
  exact stack_contains pre.toCalleePre (by omega) (by omega) ⟨i, hi, rfl⟩

end P256.Proofs.Verifying.Message.Convert
