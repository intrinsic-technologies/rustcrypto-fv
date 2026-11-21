import P256.Proofs.Sec1.Wrapper.Tag
import P256.Proofs.Sec1.Wrapper.DecoderReturn
import P256.Proofs.Sec1.Representation
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem accepted_entry [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (entry : DecoderEntry initial s input (returnBoundary initial))
    (result : CalleeResult s t (returnBoundary initial) 80 3680)
    (decoded : PublicKeyResultAt t (s.regValue .rdi) (some (.affine x y))) :
    ∃ fuel a, Advances (returnBoundary initial) fuel initial a ∧ ReturnState initial a ∧
      a.RIP = 0x10184b ∧ a.regValue .rbx = initial.regValue .rcx ∧
      a.regValue .r14 = initial.regValue .r8 ∧
      AffineAt a (stackPtr initial - 224) (.affine x y) ∧
      MemoryWriteFrame initial a (wrapperRegions publicKeyFromSec1Bytes initial) := by
  have stack : Stack.Valid initial 4048 := valid.stackAvailable.1
  have state := decoder_return_state stack entry result
  have frame := decoder_return_frame stack entry result
  have tag : memLoad t.external (stackPtr initial - 232) 64 = 0 := by
    rw [← entry.destination]
    exact decoded.1
  obtain ⟨a, run, stateA, ripA, _, agrees⟩ := tag_branch (valid := true) state stack
    entry.pre.outerBoundary (result.rip.trans entry.decoderReturn) tag
  have memory := agrees.external (by simp [Component.Covers])
  obtain ⟨n, before⟩ := decoder_return_execution entry result
  refine ⟨n + 3, a, before.trans run, stateA, ripA, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans
      ((result.calleeSaved .rbx (by simp)).trans entry.output)
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans
      ((result.calleeSaved .r14 (by simp)).trans entry.capacity)
  · apply decoded.2.of_bytes_eq
    intro i hi
    rw [memory, entry.destination]
    congr 2
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro address outside
    rw [memory]
    exact frame address outside

end P256.Proofs.Sec1.Wrapper
