import Sha3.Proofs.Permutation.Precondition
import Sha3.Proofs.Permutation.RoundMachine.Semantics
import Sha3.Proofs.Permutation.LoadStore.Store.Basic
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program Keccak

theorem CallPre.roundMemory {copy : Copy} {initial s : RamState} (h : CallPre copy initial)
    (hf : CallFrame initial s) : RoundMachine.RoundMemory (frameBase initial) s := by
  have hr := h.frameRead_of_frame hf
  refine ⟨⟨by have := hr.low; omega, fun i hi ↦ hr.mem i (by omega)⟩,
    fun i hi ht ↦ h.frameAvoid (by omega) (.inr ht),
    fun i hi hp ↦ h.frameAvoid (by omega) (.inl hp)⟩

theorem CallPre.storePre {copy : Copy} {initial s : RamState} {a : Lanes} (h : CallPre copy initial)
    (hi : RoundInvariant copy initial 24 a s) : Store.Pre copy (frameBase initial) (initial.regValue .rdi) s := by
  refine ⟨hi.rip, hi.frame.stack, hi.frame.pointer,
    h.frameRead_of_frame hi.frame, h.dataRead_of_frame hi.frame, h.apart, ?_,
    fun i hi ht ↦ h.dataAvoid i hi (.inr ht)⟩
  intro i hi j hj he
  apply h.dataAvoid i hi
  apply Or.inl
  rw [he]
  have hlen : Store.bytes.length = 214 := by decide +kernel
  have hj' : j < 214 := by simpa only [hlen] using hj
  have hbounds : ∀ (c : Copy) (k : Fin 214),
      0x100000 ≤ (storeAddress c + BitVec.ofNat 64 k.val).toNat ∧
      (storeAddress c + BitVec.ofNat 64 k.val).toNat ≤ 0x106222 := by
    intro c
    cases c <;> decide +kernel
  exact inProgram_permutation_address (hbounds copy ⟨j, hj'⟩).1 (hbounds copy ⟨j, hj'⟩).2

end Sha3.Proofs.Permutation
