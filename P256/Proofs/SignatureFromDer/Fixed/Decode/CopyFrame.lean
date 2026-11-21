import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.Common.Memory.Readable
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program (CalleePre readyToStep memoryRegion_memReadable memoryRegion_contains_add)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_stack_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {source destination : RamState → BitVec 64} {offset : Nat}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    (bound : offset + 32 ≤ 184) (dst : destination t = stackPtr t + BitVec.ofNat 64 offset)
    (rip : t.RIP = entry) (readable : MemReadable t (source t) 32)
    (apart : RangeApart (destination t) 32 (source t) 32) : Copy32.Pre entry source destination t := by
  refine ⟨rip, ?_, ?_, apart, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact P256.Proofs.Common.Memory.memReadable_sub readable _ 8 (by decide)
  · intro i hi
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 0) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 8) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 16) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 24) (len := 8) (by omega) (by decide)
  · intro i hi off len hc
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 0) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 8) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 16) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 24) (len := 8) (by omega) hc

theorem copy_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry endIP : BitVec 64} {source destination : RamState → BitVec 64}
    {offset : Nat} {code : CodeMap}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (block : AdvanceTriple boundary (Copy32.Pre entry source destination) code
      (Effect.post (Copy32.effect endIP source destination)))
    (loaded : CodeIn code t) (input : Copy32.Pre entry source destination t)
    (bound : offset + 32 ≤ 168)
    (dst : destination t = stackPtr t + BitVec.ofNat 64 offset) :
    ∃ u, Stage s u boundary ∧ (Copy32.effect endIP source destination t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, result⟩ := block t
    (readyToStep state.machine state.bindingsSupported) loaded input
  have agrees := Copy32.frame result
  have dst' := dst.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (by omega))
  have writes : WritesWithin (Copy32.components (destination t))
      #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hc a ha
    simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [dst'] at ha
    exact ⟨workRegion s, by simp, Program.ScalarFrame.Work.contains pre (by omega) (by omega) ha⟩
  exact ⟨u, state.after pre run ready agrees writes
    ((agrees.read (n := 64) (r := 4) (by simp [Copy32.components])).trans state.rsp)
    (by simp [Copy32.components]), result⟩

theorem copy_preserves_nat256 {s t : RamState} {destination source : BitVec 64} {x : Nat}
    (agrees : AgreesExcept (Copy32.components destination) s t)
    (apart : RangeApart destination 32 source 32) (input : Nat256At s source x) :
    Nat256At t source x := by
  refine ⟨input.1, fun i hi => Eq.trans (agrees.byte ?_) (input.2 i hi)⟩
  intro c hc ha
  simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  exact apart j hj i hi he.symm

end P256.Proofs.SignatureFromDer.Fixed.Decode
