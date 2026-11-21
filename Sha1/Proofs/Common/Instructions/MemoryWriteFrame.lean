import Sha1.Spec.Program
import X86Proofs.Program.ReadWrite.Stack

namespace Sha1.Proofs.Common.Instructions.MemoryWriteFrame

open Prelude X86 X86.Machine X86Proofs

theorem inPageTables_iff (a : BitVec 64) :
    Sha1.Spec.Program.InPageTables a ↔
      (0x1000 ≤ a.toNat ∧ a.toNat < 0x1008) ∨
      (0x2000 ≤ a.toNat ∧ a.toNat < 0x2020) := by
  simp [Sha1.Spec.Program.InPageTables, MemoryRegion.Contains]

theorem identityPageTableMemory_memStore {m : Ram} (h : IdentityPageTableMemory m)
    (a : BitVec 64) {n : Nat} (v : BitVec n)
    (htables : ∀ i, i < n / 8 →
      ¬ Sha1.Spec.Program.InPageTables (a + BitVec.ofNat 64 i)) :
    IdentityPageTableMemory (memStore m a v) := by
  have hf (x : BitVec 64) (hx : Sha1.Spec.Program.InPageTables x) :
      (memStore m a v)[x]? = m[x]? := by
    apply memStore_getElem?_of_ne
    intro i hi he
    exact htables i hi (he.symm ▸ hx)
  refine ⟨fun i ↦ ?_, fun page i ↦ ?_⟩
  · rw [hf _ (inPageTables_iff _ |>.mpr ?_)]
    · exact h.1 i
    · left
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      have := i.isLt
      omega
  · rw [hf _ (inPageTables_iff _ |>.mpr ?_)]
    · exact h.2 page i
    · right
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := i.isLt; have := page.isLt; omega)]
      have := i.isLt
      have := page.isLt
      omega

theorem readyToStep_afterStep_store [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (a : BitVec 64) (v : BitVec n) (nextIP : BitVec 64)
    (hlow : a.toNat + n / 8 ≤ 2^32)
    (htables : ∀ i, i < n / 8 →
      ¬ Sha1.Spec.Program.InPageTables (a + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
  have _ := hlow
  apply h.of_agreesExcept (AgreesExcept.afterStep_store s length a v nextIP)
  rw [afterStep_store_external]
  exact identityPageTableMemory_memStore h.memory.tables a v htables

end Sha1.Proofs.Common.Instructions.MemoryWriteFrame
