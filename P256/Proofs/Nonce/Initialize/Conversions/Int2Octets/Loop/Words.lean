import P256.Proofs.Program.Interface
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.Copy
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Encoding

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar P256.Proofs.Common.Instructions
open P256.Proofs.Projective.Multiply.Machine.Radix.Serialize (canonicalLimb)

def Words (initial s : RamState) (value count : Nat) : Prop :=
  ∀ j < count, memLoad s.external (initial.regValue .rdx + BitVec.ofNat 64 (24-8*j)) 64 =
    bswap64 (canonicalLimb value j)

theorem copy_keeps_word [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {offset old : Nat} (pre : Pre initial boundary)
    (agrees : AgreesExcept (copyFrame initial offset) s t)
    (bound : old + 8 ≤ 32) (before : offset + 8 ≤ old) :
    memLoad t.external (initial.regValue .rdx + BitVec.ofNat 64 old) 64 =
      memLoad s.external (initial.regValue .rdx + BitVec.ofNat 64 old) 64 := by
  have bounded := pre.outputBounded
  change (initial.regValue .rdx).toNat + 32 < 2^32 at bounded
  have oldNat : (initial.regValue .rdx + BitVec.ofNat 64 old).toNat =
      (initial.regValue .rdx).toNat + old := toNat_add_ofNat _ _ (by omega)
  have newNat : (initial.regValue .rdx + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rdx).toNat + offset := toNat_add_ofNat _ _ (by omega)
  have apart : RangeApart (initial.regValue .rdx + BitVec.ofNat 64 old) 8
      (initial.regValue .rdx + BitVec.ofNat 64 offset) 8 := by
    apply RangeApart.of_toNat
    · rw [oldNat]; omega
    · rw [newNat]; omega
    · rw [oldNat,newNat]; exact Or.inr (by omega)
  apply memLoad_congr
  intro j hj
  apply congrArg (fun o : Option UInt8 => o.getD 0)
  apply agrees.memory
  intro c hc cover
  simp only [copyFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover
  · exact pre.separation (1 : Fin 3) 2 (by decide) _
      (output_contains pre bound ⟨j,hj,rfl⟩)
      (stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) cover)
  · obtain ⟨k,hk,eqn⟩ := cover
    exact apart j hj k hk eqn

theorem words_output [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (words : Words initial s value 4) :
    (registerRegion initial .rdx 32).HasBytes s.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n value) := by
  apply intToOctets_hasBytes (address := initial.regValue .rdx) (value := value)
  · intro i hi
    apply stage.allocated
    exact Option.isSome_iff_exists.mpr (pre.outputAllocated _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi))
  · intro i hi
    have word := words (3-i) (by omega)
    have offset : 24-8*(3-i) = 8*i := by omega
    simpa only [offset] using word

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
