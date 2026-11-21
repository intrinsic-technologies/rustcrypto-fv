import P256.Proofs.Generate.Sampler.State
import P256.Proofs.Common.Der.Memory.Writable

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}

theorem State.input_bytes (pre : Pre s boundary input) (state : State s t) :
    (inputRegion s input).HasBytes t.external input :=
  frame_hasBytes state.frame (by simpa using pre.separateInput) pre.bounded pre.bytes

theorem State.stack_readable (pre : Pre s boundary input) (state : State s t)
    {offset len : Nat} (bound : offset + len ≤ 264) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by omega)]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated

theorem State.stack_writable (pre : Pre s boundary input) (state : State s t)
    {offset len : Nat} (bound : offset + len ≤ 264) :
    P256.Proofs.Common.Der.Memory.MemWritable t
      (stackPtr t + BitVec.ofNat 64 offset) len := by
  have readable := state.stack_readable pre bound
  refine ⟨readable.low, readable.mem, ?_⟩
  intro i hi hreserved
  apply pre.avoids (Stack.region s 3624) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by omega)]
  exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i,hi,rfl⟩

theorem State.stack_code (pre : Pre s boundary input) (state : State s t)
    {offset len codeOffset codeLen : Nat} (bound : offset + len ≤ 264)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 3624) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by omega)]
    exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i,hi,rfl⟩
  · apply Or.inl
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset+j) (by omega)

theorem State.stack_descriptor (pre : Pre s boundary input) (state : State s t)
    {offset len : Nat} (bound : offset + len ≤ 264) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len (s.regValue .rsi) 16 := by
  intro i hi j hj he
  have stack := ScalarFrame.stack_contains pre.toCalleePre (offset := 264-offset)
    (len := len) (a := stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
    (by omega) (by omega) (by
      rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by omega)]
      exact ⟨i,hi,rfl⟩)
  have descriptor := memoryRegion_contains_add pre.inputBounded
    (addr := s.regValue .rsi) (len := 16) (by exact Nat.le_refl _) (by exact Nat.le_refl _) hj
  rw [he] at stack
  exact pre.separation 0 2 (by decide) _ descriptor stack

theorem State.work_writes (pre : Pre s boundary input) (state : State s t)
    {offset len : Nat} (bound : offset + len + 48 ≤ 264) {a : BitVec 64}
    (covered : (Component.mem (stackPtr t + BitVec.ofNat 64 offset) len).Covers a) :
    (ScalarFrame.workRegion s 3624).Contains a.toNat := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by omega)] at covered
  exact ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) covered

end P256.Proofs.Generate.Sampler
