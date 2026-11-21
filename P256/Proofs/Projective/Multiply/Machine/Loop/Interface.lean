import P256.Proofs.Program.ScalarFrame.Input

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x103250 768 96 1400 where
  tableCount : s.regValue .rdx = 1
  digitCount : s.regValue .r8 = 1
  digitsBounded : (registerRegion s .rcx 65).Bounded
  digitsAllocated : (registerRegion s .rcx 65).Allocated s.external
  digitsOutput : (registerRegion s .rcx 65).Disjoint (registerRegion s .rdi 96)
  digitsStack : (registerRegion s .rcx 65).Disjoint (Stack.region s 1400)

theorem Pre.digit_address [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {i : Nat} (bound : i < 65) :
    (s.regValue .rcx + BitVec.ofNat 64 i).toNat = (s.regValue .rcx).toNat + i := by
  have low : (s.regValue .rcx).toNat + 65 < 2^32 := pre.digitsBounded
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem Pre.digit_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset : BitVec 64} (state : FrameState s t 96 1400 offset)
    {i : Nat} (bound : i < 65) :
    MemReadable t (s.regValue .rcx + BitVec.ofNat 64 i) 1 := by
  apply readable_of_grow (memoryRegion_memReadable pre.digitsBounded pre.digitsAllocated ?_ ?_)
    state.allocated
  · change (s.regValue .rcx).toNat ≤ _
    rw [pre.digit_address bound]
    omega
  · change _ + 1 ≤ (s.regValue .rcx).toNat + 65
    rw [pre.digit_address bound]
    omega

theorem Pre.digit_value [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset : BitVec 64} (state : FrameState s t 96 1400 offset)
    {i : Nat} (bound : i < 65) :
    memLoad t.external (s.regValue .rcx + BitVec.ofNat 64 i) 8 =
      memLoad s.external (s.regValue .rcx + BitVec.ofNat 64 i) 8 := by
  refine frame_memLoad state.frame (region := registerRegion s .rcx 65) ?_ pre.digitsBounded ?_ ?_
  · intro region member
    have cases : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1400 := by
      simpa using member
    rcases cases with rfl | rfl
    · exact pre.digitsOutput
    · exact pre.digitsStack
  · change (s.regValue .rcx).toNat ≤ _
    rw [pre.digit_address bound]
    omega
  · change _ + 1 ≤ (s.regValue .rcx).toNat + 65
    rw [pre.digit_address bound]
    omega

end P256.Proofs.Projective.Multiply.Machine.Loop
