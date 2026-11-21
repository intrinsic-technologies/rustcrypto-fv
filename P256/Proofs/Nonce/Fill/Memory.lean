import P256.Proofs.Nonce.UpdateValue.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program

theorem GeneratorAt.copy {s t : RamState} {a b orderAddress : BitVec 64} {state : State}
    (present : GeneratorAt s a orderAddress state)
    (copied : ∀ i < 72, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?)
    (order : Nat256At t orderAddress P256.Spec.Operations.domain.n) :
    GeneratorAt t b orderAddress state := by
  refine ⟨?_, order, ?_⟩
  · calc
      memLoad t.external b 64 = memLoad s.external a 64 := by
        apply memLoad_congr
        intro i hi
        exact congrArg (fun x : Option UInt8 => x.getD 0) (copied i (by omega))
      _ = orderAddress := present.1
  · exact present.2.2.copy
      (copied_sub (offset := 8) (len := 64) copied (by decide))

theorem GeneratorAt.of_frame {s t : RamState} {a orderAddress : BitVec 64} {state : State}
    {n : Nat} {regions : Vector MemoryRegion n}
    (present : GeneratorAt s a orderAddress state)
    (bounded : (MemoryRegion.mk a.toNat 72).Bounded)
    (orderBounded : (MemoryRegion.mk orderAddress.toNat 32).Bounded)
    (frame : MemoryWriteFrame s t regions)
    (apart : ∀ region ∈ regions, (MemoryRegion.mk a.toNat 72).Disjoint region)
    (orderApart : ∀ region ∈ regions, (MemoryRegion.mk orderAddress.toNat 32).Disjoint region) :
    GeneratorAt t a orderAddress state := by
  apply present.copy (fun i hi => frame_read frame apart
    (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi))
  refine ⟨present.2.1.1, ?_⟩
  intro i hi
  exact (frame_read frame orderApart
    (memoryRegion_contains_add orderBounded (Nat.le_refl _) (Nat.le_refl _) hi)).trans (present.2.1.2 i hi)

end P256.Proofs.Nonce
