import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Copy
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Step.Stage
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Step.Advance
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Step.Memory
import K256.Proofs.Verify.Core.Affine.Call

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)
open Encode

set_option maxRecDepth 2048 in
theorem Encode.stepLoop {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x k : Nat}
    (hk : k < 4) (depth : 208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 208)
    (srcAfter : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (srcBeforeDst : fr.rdi.toNat + 32 ≤ fr.rdx.toNat)
    (srcRead : Readable fr.original fr.rdi 32)
    (dstWrite : Writable Extracted.programImage fr.original fr.rdx 32)
    (srcWords : WordsAt fr.original fr.rdi 64 (scalarWords x))
    (loop : Loop fr x k a m) :
    ∃ b n, Verify.Core.Reaches (label k) a m (label (k+1)) b n ∧ Loop fr x (k+1) b n := by
  have lab : label k = .l100110 := ite_eq_left hk
  have atoms := loop.atoms
  rw [lab] at atoms
  simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,r13,r14,_,_,_,_,_,_,_,_,_,_,_,_,area,_,_,got,ptr,apart,_⟩ := atoms
  let val := bswapSpec ((scalarWords x)[k])
  let st := memStore m (fr.rsp-56) val
  let pushed := memStore st (fr.rsp-80) (0x10014b : BitVec 64)
  let dest := wordAddr fr.rdx 64 (3-k)
  have sub (t : Nat) (ht : t ≤ 208) : (fr.rsp - BitVec.ofNat 64 t).toNat = fr.rsp.toNat-t := by
    have small : (BitVec.ofNat 64 t).toNat = t := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [small]; omega)),small]
  have dstAfter : fr.rsp.toNat + 8 ≤ fr.rdx.toNat := by omega
  have dstTop := dstWrite.readable.low
  have wordNat (base : BitVec 64) (i : Nat) (hi : i < 4) (hb : base.toNat + 32 ≤ 2^32) :
      (wordAddr base 64 i).toNat = base.toNat+8*i := by
    simp only [wordAddr,Nat.reduceDiv,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8*i) (by omega),Nat.mod_eq_of_lt (by omega)]
  have srcIndex := wordNat _ k hk srcRead.low
  have dstIndex : dest.toNat = fr.rdx.toNat+8*(3-k) :=
    wordNat _ _ (by omega) dstWrite.readable.low
  have lowNat : fr.low.toNat = fr.rsp.toNat-208 := low ▸ sub 208 (by decide)
  have read := LoadOk.of_region (n := 8) (a := wordAddr fr.rdi 64 k)
    (srcRead.of_frame loop.writes) (by omega) (by omega)
  have word : memLoad m (wordAddr fr.rdi 64 k) 64 = (scalarWords x)[k] := by
    rw [loop.writes.memLoad_eq]
    · exact srcWords k hk
    · refine ⟨by omega,?_⟩
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · right
        change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
        omega
      · left
        change _ ≤ fr.rdx.toNat
        omega
  have floor : (fr.rsp - 208).toNat = fr.rsp.toNat-208 := sub 208 (by decide)
  have stack (t : Nat) (ht : t ≤ 208) (ht' : 8 ≤ t) :
      Writable Extracted.programImage m (fr.rsp-BitVec.ofNat 64 t) 8 := by
    exact area.sub (by rw [sub t ht, floor]; omega)
      (by rw [sub t ht, floor]; omega)
  have included : ∀ z ∈ codeRange 0x100110 bytes_l100110, z ∈ Extracted.programImage :=
    fun z hz => Verify.Core.Affine.coreText z (code_l100110 z hz)
  have store := ParseSignature.storeOk_of_codeRange (stack 56 (by decide) (by decide))
    included (off := 0x22) (len := 5) (by decide)
  have push := ParseSignature.storeOk_of_codeRange
    ((stack 80 (by decide) (by decide)).memStore (fr.rsp-56) val)
    included (off := 0x35) (len := 6) (by decide)
  have slotR := got.memStore (fr.rsp-56) val
  have ptr' : memLoad st 0x203dd0 64 = 0x12a820 := by
    rw [show st = _ from rfl,memLoad_memStore_of_rangeApart]
    · exact ptr
    · apply RangeApart.of_toNat
      all_goals simp only [BitVec.reduceToNat,Nat.reduceDiv,Nat.reducePow]
      all_goals have h := sub 56 (by decide)
      all_goals change (fr.rsp-56).toNat = fr.rsp.toNat-56 at h
      all_goals omega
  obtain ⟨b, call, bd, bs, bn, bp, bc, bi, keep⟩ := stageWord hk (congrArg (Value.get 64) sp)
    (congrArg (Value.get 64) r13) (congrArg (Value.get 64) r14)
    (congrArg (Value.get 64) loop.index) (congrArg (Value.get 64) loop.remaining)
    (congrArg (Value.get 64) loop.cursor) (congrArg (Value.get 64) loop.zero)
    read word store push ⟨slotR.low,slotR.present⟩ ptr'
  have pushReadable := ((stack 80 (by decide) (by decide)).readable.memStore (fr.rsp-56) val).memStore
    (fr.rsp-80) (0x10014b : BitVec 64)
  have tag : memLoad pushed (fr.rsp-80) 64 = 0x10014b :=
    memLoad_memStore_same st _ _ (by decide) (by decide)
  have srcReadable := ((stack 56 (by decide) (by decide)).readable.memStore (fr.rsp-56) val).memStore
    (fr.rsp-80) (0x10014b : BitVec 64)
  have destWritable := (((dstWrite.of_frame loop.writes).sub (a := dest) (n := 8)
    (by omega) (by omega)).memStore (fr.rsp-56) val).memStore (fr.rsp-80) (0x10014b : BitVec 64)
  have nat56 : (fr.rsp-56).toNat = fr.rsp.toNat-56 := sub 56 (by decide)
  have nat80 : (fr.rsp-80).toNat = fr.rsp.toNat-80 := sub 80 (by decide)
  have disj : (fr.rsp-56).toNat+8 ≤ dest.toNat := by omega
  have retApart : RangeApart dest 8 (fr.rsp-80) 8 :=
    RangeApart.of_toNat (by omega) (by omega) (by omega)
  have bdf : b[22].get 1 = 0 := congrArg (Value.get 1) ((keep 22 (by decide)).trans df)
  obtain ⟨out, exec, mem, ret, _, rsp, saved⟩ := Verify.Hash.Update.memcpy
    (mem := pushed) (rsp := fr.rsp-80) (dst := dest) (src := fr.rsp-56) (count := 8) bd bs bn (congrArg (Value.get 64) bp) bdf srcReadable destWritable
    (Or.inl disj) retApart pushReadable (by rw [tag]; decide)
  rw [tag] at ret
  have path := Verify.Core.Affine.resumeCoreCall call exec ret
  have widths := copyArgumentWidths exec ((congrArg Value.width (keep 9 (by decide))).trans
    (loop.widths 9 (by decide)))
  obtain ⟨atoms',writes,words⟩ := writtenWord hk depth low dstAfter dstWrite loop
  change out.store = memCopy pushed dest (fr.rsp-56) 8 at mem
  change Atom.All _ _ (memCopy pushed dest (fr.rsp-56) 8) _ at atoms'
  rw [← mem] at atoms'
  change RamWriteFrame _ (memCopy pushed dest (fr.rsp-56) 8) _ at writes
  rw [← mem] at writes
  change ∀ i (_ : i < k+1) (bound : i < 4), memLoad (memCopy pushed dest (fr.rsp-56) 8) _ 64 = bswapSpec ((scalarWords x)[i]) at words
  rw [← mem] at words
  have kept (i : Fin Reg.count) (hs : i.val ∈ [12,13,14,15,22,39,50,51]) : out.values[i] = a[i] := by
    apply Eq.trans (saved i ?_) (keep i ?_)
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at *
    all_goals omega
  have stackRet : out.values[4] = ⟨64,fr.rsp-72⟩ := by
    rw [rsp]
    congr 1
    bv_omega
  obtain ⟨c,branch,inv⟩ := advance hk atoms' (fun i hi => kept i (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)) stackRet
    ((saved 3 (by decide)).trans bc) ((saved 5 (by decide)).trans bi)
    ((kept 12 (by decide)).trans loop.zero) ((kept 15 (by decide)).trans loop.count)
    widths writes words
  exact ⟨c,out.store,lab ▸ path.trans branch,inv⟩

end K256.Proofs.Signing.Nonce.Initialize
