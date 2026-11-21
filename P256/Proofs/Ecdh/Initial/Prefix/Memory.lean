import P256.Proofs.Ecdh.Initial.Prefix.State
import P256.Proofs.Ecdh.Initial.Support
import P256.Proofs.Projective.Constants

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Field
open Standards.SECG.ECC

theorem peer_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t) {i : Nat} (hi : i < 72) :
    t.external[s.regValue .rdx + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 i]? := by
  apply frame_read state.frame (region := registerRegion s .rdx 72)
  · intro region hr
    have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 3464 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact pre.peerOutput
    · exact pre.peerStack
  · exact memoryRegion_contains_add pre.peerBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem peer_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t) {offset len : Nat}
    (bound : offset + len ≤ 72) :
    MemReadable t (s.regValue .rdx + BitVec.ofNat 64 offset) len := by
  have first : MemReadable s (s.regValue .rdx) 72 :=
    memoryRegion_memReadable pre.peerBounded pre.peerAllocated (Nat.le_refl _) (Nat.le_refl _)
  have low : (s.regValue .rdx).toNat + 72 ≤ 2^32 := first.low
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.allocated _ (first.mem _ (by omega))

theorem peer_flag [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Curve.Point}
    (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t)
    (peer : Sec1.AffineAt s (s.regValue .rdx) point) :
    (memLoad t.external (s.regValue .rdx + 64) 32).setWidth 8 =
      if point = .infinity then 1 else 0 := by
  have byte := peer_byte pre state (i := 64) (by decide)
  have load := storedByte_memLoad t.external (s.regValue .rdx + 64) (n := 32) 0 (by decide)
  have low : (memLoad t.external (s.regValue .rdx + 64) 32).setWidth 8 =
      ((t.external[s.regValue .rdx + 64]?).getD 0).toBitVec := by
    have eq := congrArg UInt8.toBitVec load
    simpa only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.ushiftRight_zero,
      BitVec.add_zero, memByte, PhysicalMemory.read, UInt8.toBitVec_ofNat', BitVec.setWidth, show ¬32 ≤ 8 by decide, dite_false] using eq
  have eq := low.trans (congrArg (fun x : Option UInt8 => (x.getD 0).toBitVec) byte)
  rw [eq]
  cases point <;> simp only [Sec1.AffineAt] at peer
  all_goals exact congrArg (fun x : Option UInt8 => (x.getD 0).toBitVec) peer.2.2

end P256.Proofs.Ecdh.Initial.Prefix
