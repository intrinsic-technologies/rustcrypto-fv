import P256.Proofs.Sec1.Wrapper.ReturnState
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Sec1Serialize.Tail.Prepare.Encoding
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem accepted_of_model {input : ByteArray} {x y : Nat}
    (model : Points.decodePublicKey input = some (.affine x y)) :
    publicKeyFromSec1Bytes.accepts [input].toArray = true := by
  change (Keys.publicKeyFromSec1 [input].toArray).isSome = true
  change ((Points.decodePublicKey input).map Keys.uncompressed).isSome = true
  rw [model]
  rfl

theorem output_region_eq {initial : RamState} {input : ByteArray} {x y : Nat}
    (model : Points.decodePublicKey input = some (.affine x y)) :
    outputRegion publicKeyFromSec1Bytes initial [input] = registerRegion initial .rcx 73 := by
  change registerRegion initial .rcx
    (8 + resultBytes ((Points.decodePublicKey input).map Keys.uncompressed)) = _
  rw [model]
  have size := P256.Proofs.Sec1Serialize.Prepare.encodePoint_uncompressed_size x y
  change registerRegion initial .rcx (8 + (Points.encode (.affine x y)).size) = _
  rw [size]


theorem output_stack_disjoint [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y)) :
    (outputRegion publicKeyFromSec1Bytes initial [input]).Disjoint (Stack.region initial 4048) := by
  have sep := (valid.outputSeparationIfAccepted (accepted_of_model model)).1
    (0 : Fin 5) (4 : Fin 5) (by decide)
  intro a ha hb
  exact sep a ha (stack_contains_callStack hb)

theorem output_contains [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat} {off len : Nat} {a : BitVec 64}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (bound : off + len ≤ 8 + 65)
    (covers : (Component.mem (initial.regValue .rcx + BitVec.ofNat 64 off) len).Covers a) :
    (outputRegion publicKeyFromSec1Bytes initial [input]).Contains a.toNat := by
  have bounded : (registerRegion initial .rcx (8 + 65)).Bounded := by
    simpa only [ValidOutput, output_region_eq model] using
      (valid.outputInMemoryIfAccepted (accepted_of_model model)).2.1
  obtain ⟨i, hi, rfl⟩ := covers
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, output_region_eq model]
  exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _)
    (by change off + i < 8 + 65; omega)

theorem output_apart_stack [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat} {off len outOff outLen : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (bound : off ≤ 4048) (ends : len ≤ off + 8) (output : outOff + outLen ≤ 8 + 65) :
    RangeApart (initial.regValue .rcx + BitVec.ofNat 64 outOff) outLen
      (stackPtr initial - BitVec.ofNat 64 off) len := by
  intro i hi j hj eq
  apply output_stack_disjoint valid model _ (output_contains valid model output ⟨i, hi, rfl⟩)
  rw [eq]
  exact stack_buffer_contains valid.stackAvailable.1 bound ends
    (memoryRegion_contains_add (stack_buffer_bounded valid.stackAvailable.1 bound ends)
      (Nat.le_refl _) (Nat.le_refl _) hj)

theorem output_writable [Bindings] {initial t : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (grown : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) :
    CrossPageStore.Writable t (initial.regValue .rcx) (8 + 65) := by
  have bounded : (registerRegion initial .rcx (8 + 65)).Bounded := by
    simpa only [ValidOutput, output_region_eq model] using
      (valid.outputInMemoryIfAccepted (accepted_of_model model)).2.1
  have allocated : (registerRegion initial .rcx (8 + 65)).Allocated initial.external := by
    simpa only [ValidOutput, output_region_eq model] using
      (valid.outputInMemoryIfAccepted (accepted_of_model model)).2.2
  have readable := readable_of_grow
    (memoryRegion_memReadable bounded allocated (Nat.le_refl _) (Nat.le_refl _)) grown
  refine ⟨readable, tables_of_not_reserved (by omega) readable.low ?_⟩
  intro i hi hp
  apply ((valid.outputSeparationIfAccepted (accepted_of_model model)).2
    (outputRegion publicKeyFromSec1Bytes initial [input]) (by simp)).2 _ ?_ (.inr hp)
  rw [output_region_eq model]
  exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi

end P256.Proofs.Sec1.Wrapper.Success.Tail
