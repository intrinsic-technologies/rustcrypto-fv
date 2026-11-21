import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)




namespace Iterator

def descriptor (m : Ram) (sp : BitVec 64) : Ram :=
  let n := memStore m (sp + 0x228) (sp + 0x1568)
  let n := memStore n (sp + 0x230) (sp + 0x28a8)
  let n := memStore n (sp + 0x238) (0 : BitVec 64)
  memStore n (sp + 0x268) (0 : BitVec 64)

abbrev pushed (m : Ram) (sp : BitVec 64) :=
  memStore (descriptor m sp) (sp - 8) (0x10fca6 : BitVec 64)

theorem fields (m : Ram) (sp : BitVec 64) :
    let n := pushed m sp
    memLoad n (sp + 0x228) 64 = sp + 0x1568 ∧
    memLoad n (sp + 0x230) 64 = sp + 0x28a8 ∧
    memLoad n (sp + 0x238) 64 = 0 ∧ memLoad n (sp + 0x268) 64 = 0 ∧
    memLoad n (sp - 8) 64 = 0x10fca6 := by
  simp (disch := store_disch) only [pushed, descriptor, memLoad_memStore_same,
    memLoad_memStore_of_rangeApart, and_self]

theorem setup {a : Registers} {m : Ram} {sp dst : BitVec 64}
    (rsp : a[4].get 64 = sp) (table : a[13].get 64 = sp + 0x1568)
    (dest : memLoad m sp 64 = dst) (window : Writable Extracted.programImage m (sp - 8) 0x280) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10fc62,a,m⟩ =
      .call ⟨.l1100a0,b,pushed m sp⟩ (callResume .l10fca6 0x10fca6) ∧
      b[4] = ⟨64,sp - 8⟩ ∧ b[7] = ⟨64,dst⟩ ∧ b[6] = ⟨64,sp + 0x228⟩ ∧ b[3] = ⟨64,dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m (pushed m sp) [scratch sp 8, ⟨(sp + 0x228).toNat,72⟩] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,table]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10fc62)
    simp (disch := store_disch) only [memLoad_memStore_of_rangeApart,dest]
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
    · rintro ⟨i,hi⟩ live
      simp only [List.mem_cons,List.not_mem_nil,or_false] at live
      rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · have low := window.readable.low
      have room : 8 ≤ sp.toNat := by
        change (2^64 - 8 + sp.toNat) % 2^64 + 0x280 ≤ 2^32 at low
        omega
      have addr : (sp - 8).toNat = sp.toNat - 8 :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
      have base := toNat_add_ofNat sp 0x228 (by omega)
      let regions : List MemoryRegion := [scratch sp 8, ⟨(sp + 0x228).toNat,72⟩]
      have inBuffer (k : Nat) (lo : 0x228 ≤ k) (hi : k + 8 ≤ 0x270) :
          InRegions regions (sp + BitVec.ofNat 64 k) 8 := by
        have pos := toNat_add_ofNat sp k (by omega)
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        change (sp + 0x228).toNat ≤ _ ∧ _ + 8 ≤ (sp + 0x228).toNat + 72 ∧ _ + 8 ≤ 2^64
        change (sp + 0x228).toNat = sp.toNat + 0x228 at base
        omega
      unfold pushed descriptor
      apply RamWriteFrame.memStore
      · apply RamWriteFrame.memStore
        · apply RamWriteFrame.memStore
          · apply RamWriteFrame.memStore
            · exact (RamWriteFrame.refl m regions).memStore _ (inBuffer 0x228 (by decide) (by decide))
            · exact inBuffer 0x230 (by decide) (by decide)
          · exact inBuffer 0x238 (by decide) (by decide)
        · exact inBuffer 0x268 (by decide) (by decide)
      · exact ⟨_,List.mem_cons_self ..,by change sp.toNat - 8 ≤ _ ∧ _ + 8 ≤ sp.toNat - 8 + 8 ∧ _ + 8 ≤ 2^64; omega⟩

end Iterator
end K256.Proofs.Verify.Core.Lincomb
