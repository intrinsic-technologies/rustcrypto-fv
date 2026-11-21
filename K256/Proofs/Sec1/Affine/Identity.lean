import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.ParseSignature.BlackBox
import K256.Spec.Program.Extracted.Image
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Sec1.Affine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine Prelude
open K256.Spec.Program K256.Proofs.Sec1.LIR K256.Proofs.CFG

def identityWords : Vector (BitVec 64) 11 :=
  #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def identityBytes := List.ofFn fun i : Fin 88 => if i.val = 80 then (1 : UInt8) else 0

set_option maxRecDepth 4096 in
private theorem identityCode : ∀ x ∈ codeRange 0x2033a8 identityBytes, x ∈ Extracted.programImage := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  exact codeRange_sub_section (s := sec)
    (by simp [sec, Extracted.programSections]) 0x33a8 88 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl

private theorem identityWordByte : ∀ (i : Fin 11) (j : Fin 8),
    storedByte identityWords[i.val] j.val = (if 8*i.val+j.val = 80 then 1 else 0) := by
  decide +kernel

theorem identityWords_loaded {mem : Ram}
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2) :
    Readable mem 0x2033a8 88 ∧ WordsAt mem 0x2033a8 64 identityWords := by
  have bytes (i : Fin 88) :
      mem[0x2033a8 + BitVec.ofNat 64 i.val]? = some (if i.val = 80 then 1 else 0) := by
    apply loaded (0x2033a8 + BitVec.ofNat 64 i.val, if i.val = 80 then 1 else 0)
    apply identityCode
    have h := mem_codeRange (0x2033a8 : BitVec 64) identityBytes i.val
      (by simpa only [identityBytes, List.length_ofFn] using i.isLt)
    simpa only [identityBytes, List.getElem_ofFn] using h
  constructor
  · exact ⟨by decide, fun i hi => by rw [bytes ⟨i, hi⟩]; rfl⟩
  · intro i hi
    apply Bytes.memLoad (n := 64) _ (by decide) (by decide)
    intro j hj
    have hw := identityWordByte ⟨i, hi⟩ ⟨j, hj⟩
    change storedByte identityWords[i] j = _ at hw
    rw [hw]
    simpa only [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_comm i 8] using
      bytes ⟨8*i+j, by omega⟩

private theorem naturalSpanApart {p q a b : Nat}
    (apart : ∀ i < a, ∀ j < b, p + i ≠ q + j) (ha : 0 < a) (hb : 0 < b) :
    p + a ≤ q ∨ q + b ≤ p := by
  by_cases h : p ≤ q
  · apply Classical.byContradiction
    intro hn
    exact (apart (q - p) (by omega) 0 hb) (by omega)
  · apply Classical.byContradiction
    intro hn
    exact (apart 0 ha (p - q) (by omega)) (by omega)

theorem identityWords_apart {mem : Ram} {dst : BitVec 64}
    (write : Writable Extracted.programImage mem dst 89) :
    0x203400 ≤ dst.toNat ∨ dst.toNat + 88 ≤ 0x2033a8 := by
  apply naturalSpanApart (a := 88) (b := 88) (p := 0x2033a8) (q := dst.toNat) _ (by decide) (by decide)
  intro i hi j hj he
  have h := mem_codeRange (0x2033a8 : BitVec 64) identityBytes i
    (by simpa only [identityBytes, List.length_ofFn] using hi)
  apply write.notCode _ (identityCode _ h) j (by omega)
  have same := congrArg (BitVec.ofNat 64) he
  rw [BitVec.ofNat_add, ofNat_toNat_add] at same
  exact same

theorem writeIdentity {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (dst : BitVec 64)
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2)
    (outPtr : args[3].get 64 = dst) (df : args[22].get 1 = 0)
    (writable : Writable code mem dst 89) (apart : 0x203400 ≤ dst.toNat ∨ dst.toNat + 88 ≤ 0x2033a8) :
    ∃ next after, program.runBlock (dialect code) ⟨.l1214d8, args, mem⟩ =
        .jump ⟨.l121599, next, after⟩ ∧
      WordsAt after dst 64 identityWords ∧ memLoad after (dst + 88) 8 = 1 ∧
      RamWriteFrame mem after [⟨dst.toNat, 89⟩] ∧
      ∀ i : Fin Reg.count, i.val ∉ [1, 6, 7] → next[i] = args[i] := by
  obtain ⟨source, words⟩ := identityWords_loaded loaded
  have low := writable.readable.low
  have flagAddr : (dst + 88).toNat = dst.toNat + 88 := by bv_omega
  have dstCopy : Writable code mem dst 88 := writable.sub (Nat.le_refl _) (by omega)
  have included := fun x hx => hcode x (code_l1214d8 x hx)
  have storeCopy : StoreOk code mem dst 88 0x1214e7 3 :=
    ParseSignature.storeOk_of_codeRange (off := 15) dstCopy included (by decide)
  have copyOK : RepMovsOk code mem 0 0x2033a8 dst 11 8 0x1214e7 3 :=
    ⟨rfl, source.low, storeCopy.low, source.present, storeCopy.present, apart,
      storeCopy.tables, storeCopy.apart, storeCopy.notCode⟩
  let copied := memCopy mem dst 0x2033a8 88
  let after := memStore copied (dst + 88) (1 : BitVec 8)
  have flagWrite : Writable code mem (dst + 88) 1 := writable.sub (by omega) (by omega)
  have storeFlag : StoreOk code copied (dst + 88) 1 0x1214ea 4 :=
    ParseSignature.storeOk_of_codeRange (off := 18)
      (flagWrite.memStore dst (memLoad mem 0x2033a8 704)) included (by decide)
  have copiedWords : WordsAt copied dst 64 identityWords := by
    intro i hi
    exact (Parser.Result.memLoad_memCopy (off := 8*i) mem dst 0x2033a8 (by decide : 88 ≤ 2^64)
      (by omega : 8*i + 64/8 ≤ 88)).trans (words i hi)
  refine ⟨?_, after, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · cfg_eval
    simp only [outPtr, df, copyOK, or_true, ↓reduceIte]
    change (if StoreOk code copied (dst + 88) 1 0x1214ea 4 then _ else _) = _
    rw [ite_eq_left storeFlag]
  · apply copiedWords.write_apart
    exact RangeApart.of_offsets (x := dst) (c := 88) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · apply ((RamWriteFrame.refl _ _).memStore (memLoad mem 0x2033a8 704) ?_).memStore 1 ?_
    · refine ⟨_, List.mem_singleton_self _, ?_⟩
      change dst.toNat ≤ dst.toNat ∧ dst.toNat + 88 ≤ dst.toNat + 89 ∧ dst.toNat + 88 ≤ 2^64
      omega
    · refine ⟨_, List.mem_singleton_self _, ?_⟩
      change dst.toNat ≤ (dst + 88).toNat ∧ (dst + 88).toNat + 1 ≤ dst.toNat + 89 ∧
        (dst + 88).toNat + 1 ≤ 2^64
      omega
  · intro i
    change Fin 53 at i
    finite_cases i <;> intro hi <;> first | rfl | exact (hi (by decide)).elim

end K256.Proofs.Sec1.Affine
