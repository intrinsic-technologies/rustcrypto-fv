import K256.Proofs.Ecdh.Decode.Affine.Contract

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

def writes (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp-1192).toNat,1192⟩, ⟨fr.rdi.toNat,89⟩]

theorem Entry.afterSaves {fr : Activation} {a m bs} (e : Entry fr a m bs) {n}
    (saved : RamWriteFrame m n [⟨(fr.rsp-40).toNat,40⟩]) : RamWriteFrame m n (writes fr) := by
  have room := e.low
  have bottom : (fr.rsp-1192).toNat = fr.rsp.toNat-1192 := BitVec.toNat_sub_of_le (by change 1192 ≤ fr.rsp.toNat; omega)
  have top : (fr.rsp-40).toNat = fr.rsp.toNat-40 := BitVec.toNat_sub_of_le (by change 40 ≤ fr.rsp.toNat; omega)
  apply (RamWriteFrame.refl m (writes fr)).trans saved
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_,List.mem_cons_self,?_,?_⟩ <;> dsimp only [writes] <;> omega

theorem Entry.savedImage {fr : Activation} {a m bs} (e : Entry fr a m bs) {n}
    (saved : RamWriteFrame m n [⟨(fr.rsp-40).toNat,40⟩]) :
    ∀ x ∈ Extracted.programImage, n[x.1]? = some x.2 := by
  have write : Writable Extracted.programImage m (fr.rsp-40) 40 :=
    e.window.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  intro b hb
  let base := fr.rsp-40
  apply (saved.outside b.1 ?_).trans (e.image b hb)
  refine ⟨by have := b.1.isLt; omega,fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change b.1.toNat + 1 ≤ base.toNat ∨ base.toNat + 40 ≤ b.1.toNat
  apply Classical.byContradiction
  intro h
  have hi : b.1.toNat - base.toNat < 40 := by omega
  apply write.notCode b hb (b.1.toNat - base.toNat) hi
  apply BitVec.eq_of_toNat_eq
  symm
  change (base + BitVec.ofNat 64 (b.1.toNat-base.toNat)).toNat = b.1.toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ - _) (by omega),
    Nat.add_sub_cancel' (by omega), Nat.mod_eq_of_lt b.1.isLt]

theorem withOutput {fr : Activation} {m n o : Ram}
    (h : RamWriteFrame m n (writes fr)) (output : RamWriteFrame n o [⟨fr.rdi.toNat,89⟩]) :
    RamWriteFrame m o (writes fr) := by
  apply h.trans output
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩

end K256.Proofs.Ecdh.Decode.Affine
