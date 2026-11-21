import P256.Proofs.Nonce.Interface
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem DrbgAt.key_size {s : RamState} {a : BitVec 64} {state : State}
    (present : DrbgAt s a state) : state.key.size = 32 := present.1.1

theorem DrbgAt.value_size {s : RamState} {a : BitVec 64} {state : State}
    (present : DrbgAt s a state) : state.value.size = 32 := present.2.1

theorem DrbgAt.copy {s t : RamState} {a b : BitVec 64} {state : State}
    (present : DrbgAt s a state)
    (copied : ∀ i < 64, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    DrbgAt t b state := by
  refine ⟨hasBytes_copy present.1 (fun i hi => copied i (by omega)), ?_⟩
  exact hasBytes_copy present.2
    (copied_sub (offset := 32) (len := 32) copied (by decide))

theorem DrbgAt.of_frame {s t : RamState} {a : BitVec 64} {state : State}
    {n : Nat} {regions : Vector MemoryRegion n}
    (present : DrbgAt s a state)
    (bounded : (MemoryRegion.mk a.toNat 64).Bounded)
    (frame : MemoryWriteFrame s t regions)
    (apart : ∀ region ∈ regions, (MemoryRegion.mk a.toNat 64).Disjoint region) :
    DrbgAt t a state := by
  apply present.copy
  intro i hi
  exact frame_read frame apart
    (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi)

end P256.Proofs.Nonce
