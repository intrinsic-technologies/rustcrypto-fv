import P256.Proofs.Verifying.Model
import P256.Proofs.Verifying.Wrapper.ReturnState
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem output_region (initial : RamState) (key signature message : ByteArray) :
    outputRegion verifyingKeyVerify initial [key, signature, message] =
      registerRegion initial .rcx 8 := by
  change registerRegion initial .rcx
    (8 + resultBytes (Ecdsa.verifyMessage #[key, signature, message])) = _
  rw [verifyMessage_eq]
  split <;> rfl

theorem output_writable [Bindings] {initial t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (accepted : verifyingKeyVerify.accepts #[key, signature, message] = true)
    (state : ReturnState initial t) : CrossPageStore.Writable t (initial.regValue .rcx) 8 := by
  have valid := call.outputInMemoryIfAccepted accepted
  rw [ValidOutput, output_region] at valid
  have readable := readable_of_grow
    (memoryRegion_memReadable valid.2.1 valid.2.2 (Nat.le_refl _) (Nat.le_refl _)) state.allocated
  refine ⟨readable, tables_of_not_reserved (by decide) readable.low ?_⟩
  intro i hi page
  have contains := memoryRegion_contains_add valid.2.1 (Nat.le_refl _) (Nat.le_refl _) hi
  have avoids := ((call.outputSeparationIfAccepted accepted).2
    (outputRegion verifyingKeyVerify initial [key, signature, message]) (by simp)).2
  rw [output_region] at avoids
  exact avoids _ contains (.inr page)

theorem output_code [Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (accepted : verifyingKeyVerify.accepts #[key, signature, message] = true)
    {offset len : Nat} (bound : offset + len ≤ 118431) :
    RangeApart (initial.regValue .rcx) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  have valid := call.outputInMemoryIfAccepted accepted
  rw [ValidOutput, output_region] at valid
  have avoids := ((call.outputSeparationIfAccepted accepted).2
    (outputRegion verifyingKeyVerify initial [key, signature, message]) (by simp)).2
  rw [output_region] at avoids
  intro i hi j hj eq
  apply avoids _ (memoryRegion_contains_add valid.2.1 (Nat.le_refl _) (Nat.le_refl _) hi)
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + j) (by omega)

theorem output_frame [Bindings] {initial t u : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (accepted : verifyingKeyVerify.accepts #[key, signature, message] = true)
    (agrees : AgreesExcept [.mem (initial.regValue .rcx) 8, .reg 0, .flags, .rip] t u) :
    MemoryWriteFrame t u #v[outputRegion verifyingKeyVerify initial [key, signature, message]] := by
  have valid := call.outputInMemoryIfAccepted accepted
  rw [ValidOutput, output_region] at valid
  apply agrees.memoryWriteFrame
  intro c hc a cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨i, hi, rfl⟩ := cover
    refine ⟨outputRegion verifyingKeyVerify initial [key, signature, message], by simp, ?_⟩
    rw [output_region]
    exact memoryRegion_contains_add valid.2.1 (Nat.le_refl _) (Nat.le_refl _) hi
  all_goals exact cover.elim

theorem output_saved [Bindings] {initial t u : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (accepted : verifyingKeyVerify.accepts #[key, signature, message] = true)
    (frame : MemoryWriteFrame t u #v[outputRegion verifyingKeyVerify initial [key, signature, message]])
    {off : Nat} (bound : off ≤ 40) :
    memLoad u.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 := by
  have disjoint := (call.outputSeparationIfAccepted accepted).1
    ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide)
  change (outputRegion verifyingKeyVerify initial [key, signature, message]).Disjoint
    (callStack verifyingKeyVerify initial) at disjoint
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr initial - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).getD 0 = _
  rw [frame _]
  · rfl
  intro r hr contains
  have eq : r = outputRegion verifyingKeyVerify initial [key, signature, message] := by simpa using hr
  subst r
  exact disjoint _ contains (stack_component_within call.stackAvailable.1
    (by change off ≤ 10280; omega) (by omega) ⟨i, hi, rfl⟩)

theorem ReturnState.after_output [Bindings] {initial t u : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (state : ReturnState initial t)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (accepted : verifyingKeyVerify.accepts #[key, signature, message] = true)
    (ready : ReadyToStep u)
    (agrees : AgreesExcept [.mem (initial.regValue .rcx) 8, .reg 0, .flags, .rip] t u) :
    ReturnState initial u := by
  have frame := output_frame call accepted agrees
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear (by simp) state.directionFlag,
    (agrees.read (n := 64) (r := 4) (by simp)).trans state.rsp, ?_, ?_,
    (agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp,
    fun a ha => agrees.grow a (state.allocated a ha)⟩
  · intro a b byte
    rw [frame a]
    · exact state.loaded a b byte
    · intro r hr contains
      have eq : r = outputRegion verifyingKeyVerify initial [key, signature, message] := by simpa using hr
      subst r
      exact ((call.outputSeparationIfAccepted accepted).2 _ (by simp)).2 a contains (.inl ⟨b, byte⟩)
  · intro entry member
    have bound : entry.2 ≤ 40 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_saved call accepted frame bound).trans (state.saved entry member)
  · have saved := output_saved call accepted frame (off := 0) (by decide)
    change memLoad u.external (stackPtr initial - 0#64) 64 =
      memLoad t.external (stackPtr initial - 0#64) 64 at saved
    simp only [BitVec.sub_zero] at saved
    exact saved.trans state.returnAddress

end P256.Proofs.Verifying.Wrapper
