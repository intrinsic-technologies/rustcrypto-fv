import ChaCha20Poly1305.Proofs.Common.WritableRange
import X86Proofs.Program.ReadWrite.Stack

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Instructions.MemoryWriteFrame

open Prelude X86 X86.Machine X86Proofs

theorem identityPageTableMemory_memStore {m : Ram} (h : IdentityPageTableMemory m)
    (a : BitVec 64) {n : Nat} (v : BitVec n)
    (htables : ∀ i, i < n / 8 →
      ¬ ChaCha20Poly1305.Proofs.Common.InPageTables (a + BitVec.ofNat 64 i)) :
    IdentityPageTableMemory (memStore m a v) := by
  have hf (x : BitVec 64) (hx : ChaCha20Poly1305.Proofs.Common.InPageTables x) :
      (memStore m a v)[x]? = m[x]? := by
    apply memStore_getElem?_of_ne
    intro i hi he
    exact htables i hi (he.symm ▸ hx)
  refine ⟨fun i ↦ ?_, fun page i ↦ ?_⟩
  · rw [hf _ (ChaCha20Poly1305.Proofs.Common.inPageTables_iff _ |>.mpr ?_)]
    · exact h.1 i
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      have := i.isLt
      omega
  · rw [hf _ (ChaCha20Poly1305.Proofs.Common.inPageTables_iff _ |>.mpr ?_)]
    · exact h.2 page i
    · rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := i.isLt; have := page.isLt; omega)]
      have := i.isLt
      have := page.isLt
      omega

theorem readyToStep_afterStep_store [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (a : BitVec 64) (v : BitVec n) (nextIP : BitVec 64)
    (hlow : a.toNat + n / 8 ≤ 2^32)
    (htables : ∀ i, i < n / 8 →
      ¬ ChaCha20Poly1305.Proofs.Common.InPageTables (a + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
  have _ := hlow
  apply h.of_agreesExcept (AgreesExcept.afterStep_store s length a v nextIP)
  rw [afterStep_store_external]
  exact identityPageTableMemory_memStore h.memory.tables a v htables

end ChaCha20Poly1305.Proofs.MemoryRoutines.Instructions.MemoryWriteFrame
