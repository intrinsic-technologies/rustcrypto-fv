import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Sec1.Affine.Compressed.Tail.Stages
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field Serialize.Coordinates

private theorem wordOffset (sp : Word) (offset i : Nat) :
    wordAddr (sp + BitVec.ofNat 64 offset) 64 i = sp + BitVec.ofNat 64 (offset + 8 * i) := by
  simp only [wordAddr, Nat.reduceDiv, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem maskWindowWord {code : CodeMap} {mem : Ram} {sp p : Word} {n : Nat}
    (stack : Writable code mem (sp - 121) 466) (hp : (p + 121).toNat + n ≤ 466) :
    Writable code mem (sp + p) n := by
  have he : p - (0 - 121) = p + 121 := by bv_omega
  exact stack.of_offsets (x := sp) rfl (addr_sub sp 121) (he ▸ hp)

private theorem maskStore {code : CodeMap} {mem m : Ram} {sp p q : Word} {w size off len : Nat}
    (cover : ∀ e ∈ fnCode, e ∈ code) (stack : Writable code mem (sp - 121) 466)
    (frame : RamWriteFrame mem m (selectWrites sp))
    (v : BitVec w) (fit : (p + 121).toNat + w / 8 ≤ 466)
    (hregion : ⟨(sp + q).toNat, size⟩ ∈ selectWrites sp)
    (qfit : (q + 121).toNat ≤ 466)
    (inside : (q + 121).toNat ≤ (p + 121).toNat ∧
      (p + 121).toNat + w / 8 ≤ (q + 121).toNat + size)
    (hi : off + len ≤ bytes_l120d03.length) :
    StoreOk code m (sp + p) (w / 8) (0x120d03 + BitVec.ofNat 64 off) len ∧
      RamWriteFrame mem (memStore m (sp + p) v) (selectWrites sp) := by
  have wpos := maskWindowWord (stack.of_frame frame) fit
  refine ⟨ParseSignature.storeOk_of_codeRange wpos
    (fun e he => cover e (code_l120d03 e he)) hi, frame.memStore v ⟨_, hregion, ?_⟩⟩
  have low := stack.readable.low
  have natAt (j : Word) (hj : (j + 121).toNat ≤ 466) :
      (sp + j).toNat = (sp - 121).toNat + (j + 121).toNat := by
    have he : j - (0 - 121) = j + 121 := by bv_omega
    rw [toNat_of_offsets (a := sp + j) (c := j) (n := 0) rfl (addr_sub sp 121) low
      (by simpa only [he, Nat.add_zero] using hj), he]
  change (sp + q).toNat ≤ (sp + p).toNat ∧
    (sp + p).toNat + w / 8 ≤ (sp + q).toNat + size ∧ (sp + p).toNat + w / 8 ≤ 2 ^ 64
  rw [natAt p (by omega), natAt q qfit]
  omega

set_option maxHeartbeats 1000000 in
theorem maskRootCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    {fr : Activation} {args : Values Value Reg.count} {mem : Ram} {xs : Limbs}
    {xOK ok : Bool} {want : BitVec 8} (body : BodyAt code fr args mem xs xOK want)
    {root : Fin modulus} (hroot : RootAt mem (workSP fr) root ok)
    (wide : ∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15] → args[i] = ⟨64,args[i].get 64⟩) :
    ∃ next m a, program.runBlock (dialect code) ⟨.l120d03,args,mem⟩ =
        .call ⟨.l114930,next,m⟩ (callFrame .l120d83 0x120d83) ∧
      NormalizeAt code args next mem m (workSP fr) 0x120d83 184 224 a ok ∧
      (ok = true → FieldRepr a root 8) := by
  let sp := workSP fr
  have atoms := body.atoms
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, _, _, _⟩ := atoms
  change args[4] = ⟨64, sp⟩ at rsp
  have spGet : args[4].get 64 = sp := by rw [rsp, Value.get_mk]
  have window : Writable code mem (sp - 121) 466 := by
    apply stack.of_offsets (x := fr.rsp) (c := 0 - 609) (d := 0 - 1048)
    · dsimp only [sp, workSP]
      bv_omega
    · exact addr_sub fr.rsp 1048
    · decide
  let bit := BitVec.ofNat 8 ok.toNat
  let mask := -(bit.setWidth 64)
  let flagged := memStore mem (sp + 32) bit
  let a : Limbs := Vector.ofFn (fun i : Fin 5 => memLoad flagged (wordAddr (sp + 304) 64 i.val) 64 &&& mask)
  have frame := RamWriteFrame.refl mem (selectWrites sp)
  have flagRegion : ⟨(sp + 32).toNat, 16⟩ ∈ selectWrites sp := by simp [selectWrites]
  have wordsRegion : ⟨(sp + 184).toNat, 248⟩ ∈ selectWrites sp := by simp [selectWrites]
  have slotRegion : ⟨(sp + (-(121 : Word))).toNat, 121⟩ ∈ selectWrites sp := by
    rw [← BitVec.sub_eq_add_neg]
    exact List.mem_cons_self ..
  obtain ⟨gFlag, fFlag⟩ := maskStore (p := 32) (q := 32) (off := 8) (len := 4)
    cover window frame bit (by decide) flagRegion (by decide) (by decide) (by decide +kernel)
  have read {t : Ram} (p : Word) (w : Nat) (f : RamWriteFrame mem t (selectWrites sp))
      (h : (p + 121).toNat + w ≤ 466) : LoadOk t (sp + p) w :=
    let rd := (maskWindowWord (window.of_frame f) h).readable
    ⟨rd.low, rd.present⟩
  have rFlag : LoadOk mem (sp + 344) 1 := read 344 1 frame (by decide)
  have atWord (i : Nat) (hi : i < 5) :
      memLoad flagged (sp + BitVec.ofNat 64 (304 + 8 * i)) 64 &&& mask = a[i] := by
    simp only [a, Vector.getElem_ofFn]
    have e : wordAddr (sp + 304) 64 i = sp + BitVec.ofNat 64 (304 + 8 * i) := wordOffset sp 304 i
    rw [e]
  have r0 : LoadOk flagged (sp + 304) 8 := read 304 8 fFlag (by decide)
  have h0 : memLoad flagged (sp + 304) 64 &&& mask = a[0] := atWord 0 (by decide)
  have r1 : LoadOk flagged (sp + 312) 8 := read 312 8 fFlag (by decide)
  have h1 : memLoad flagged (sp + 312) 64 &&& mask = a[1] := atWord 1 (by decide)
  have r2 : LoadOk flagged (sp + 320) 8 := read 320 8 fFlag (by decide)
  have h2 : memLoad flagged (sp + 320) 64 &&& mask = a[2] := atWord 2 (by decide)
  have r3 : LoadOk flagged (sp + 328) 8 := read 328 8 fFlag (by decide)
  have h3 : memLoad flagged (sp + 328) 64 &&& mask = a[3] := atWord 3 (by decide)
  have r4 : LoadOk flagged (sp + 336) 8 := read 336 8 fFlag (by decide)
  have h4 : memLoad flagged (sp + 336) 64 &&& mask = a[4] := atWord 4 (by decide)
  let m0 := memStore flagged (sp + 184) a[0]
  obtain ⟨g0, f0⟩ := maskStore (p := 184) (q := 184) (off := 67) (len := 8)
    cover window fFlag a[0] (by decide) wordsRegion (by decide) (by decide) (by decide +kernel)
  let m1 := memStore m0 (sp + 192) a[1]
  obtain ⟨g1, f1⟩ := maskStore (p := 192) (q := 184) (off := 75) (len := 8)
    cover window f0 a[1] (by decide) wordsRegion (by decide) (by decide) (by decide +kernel)
  let m2 := memStore m1 (sp + 200) a[2]
  obtain ⟨g2, f2⟩ := maskStore (p := 200) (q := 184) (off := 83) (len := 8)
    cover window f1 a[2] (by decide) wordsRegion (by decide) (by decide) (by decide +kernel)
  let m3 := memStore m2 (sp + 208) a[3]
  obtain ⟨g3, f3⟩ := maskStore (p := 208) (q := 184) (off := 91) (len := 8)
    cover window f2 a[3] (by decide) wordsRegion (by decide) (by decide) (by decide +kernel)
  let m4 := memStore m3 (sp + 216) a[4]
  obtain ⟨g4, f4⟩ := maskStore (p := 216) (q := 184) (off := 99) (len := 8)
    cover window f3 a[4] (by decide) wordsRegion (by decide) (by decide) (by decide +kernel)
  let final := memStore m4 (sp - 8) (0x120d83 : Word)
  obtain ⟨push, fFinal⟩ := maskStore (p := -8) (q := -121) (off := 123) (len := 5)
    cover window f4 (0x120d83 : Word) (by decide) slotRegion (by decide) (by decide) (by decide +kernel)
  have away {p q : Word} {n k : Nat} (h : n ≤ (q - p).toNat ∧ k ≤ (p - q).toNat) :
      RangeApart (sp + p) n (sp+q) k :=
    Refine.RangeApart.of_offsets (x := sp) rfl rfl h
  have repr (h : ok = true) : FieldRepr a root 8 := by
    obtain ⟨ys, yw, yr⟩ := hroot.repr h
    have hm : mask = BitVec.allOnes 64 := by subst ok; rfl
    have eq : a = ys := by
      apply Vector.ext
      intro i hi
      simp only [a, Vector.getElem_ofFn, hm, BitVec.and_allOnes]
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _]
      · exact yw i hi
      · exact RangeApart.right_sub (away (p := 32) (q := 304) (by decide)) (by omega : 8 * i + 8 ≤ 40)
    rw [eq]
    exact yr
  have dstWindow := maskWindowWord (p := 184) (n := 40) window (by decide)
  have dstLow : (sp + 184).toNat + 64 / 8 * 5 ≤ 2^64 := by
    have := dstWindow.readable.low
    omega
  let before : Limbs := Vector.ofFn (fun i : Fin 5 => memLoad flagged (wordAddr (sp + 184) 64 i.val) 64)
  have d : WordsAt flagged (sp + 184) 64 before := by
    intro i hi
    simp only [before, Vector.getElem_ofFn]
  have d0 := d.write_set (j := 0) (by decide) a[0] (by decide) (by decide) (by decide) dstLow
  have d1 := d0.write_set (j := 1) (by decide) a[1] (by decide) (by decide) (by decide) dstLow
  have d2 := d1.write_set (j := 2) (by decide) a[2] (by decide) (by decide) (by decide) dstLow
  have d3 := d2.write_set (j := 3) (by decide) a[3] (by decide) (by decide) (by decide) dstLow
  have d4 := d3.write_set (j := 4) (by decide) a[4] (by decide) (by decide) (by decide) dstLow
  have atDest : WordsAt m4 (sp + 184) 64 a := by
    intro i hi
    have w := d4 i hi
    have o (j : Nat) : wordAddr (sp + 184) 64 j =
        sp + BitVec.ofNat 64 (184 + 8 * j) := wordOffset sp 184 j
    simp only [o] at w
    rw [show wordAddr (sp + 184) 64 i = _ from o i]
    change memLoad m4 (sp + BitVec.ofNat 64 (184 + 8 * i)) 64 = _ at w
    rw [w]
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    all_goals rfl
  have finalWords : WordsAt final (sp + 184) 64 a :=
    atDest.write_apart (sp - 8) (0x120d83 : Word) (by
      rw [BitVec.sub_eq_add_neg]
      exact away (p := -8) (q := 184) (by decide))
  have slot : memLoad final (sp - 8) 64 = 0x120d83 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have retain (t : Ram) (p v : Word) (h : 8 ≤ (32 - p).toNat ∧ 1 ≤ (p - 32).toNat) :
      memLoad (memStore t (sp + p) v) (sp + 32) 8 = memLoad t (sp + 32) 8 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (away h)
  have finalFlag : memLoad final (sp + 32) 8 = bit := by
    dsimp only [final]
    rw [BitVec.sub_eq_add_neg, retain m4 (-8) _ (by decide)]
    dsimp only [m4, m3, m2, m1, m0]
    rw [retain _ 216 _ (by decide), retain _ 208 _ (by decide), retain _ 200 _ (by decide),
      retain _ 192 _ (by decide), retain _ 184 _ (by decide)]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have flagFold : memLoad mem (sp + 344) 8 = bit := hroot.flag
  have flaggedFold : memStore mem (sp + 32) bit = flagged := rfl
  have maskFold : -(bit.setWidth 64) = mask := rfl
  have h4' : mask &&& memLoad flagged (sp + 336) 64 = a[4] := (BitVec.and_comm _ _).trans h4
  have m0Fold : memStore flagged (sp + 184) a[0] = m0 := rfl
  have m1Fold : memStore m0 (sp + 192) a[1] = m1 := rfl
  have m2Fold : memStore m1 (sp + 200) a[2] = m2 := rfl
  have m3Fold : memStore m2 (sp + 208) a[3] = m3 := rfl
  have m4Fold : memStore m3 (sp + 216) a[4] = m4 := rfl
  have finalFold : memStore m4 (sp - 8) (0x120d83 : Word) = final := rfl
  simp only [Nat.reduceDiv, BitVec.reduceAdd] at gFlag g0 g1 g2 g3 g4 push
  simp only [← BitVec.ofNat_eq_ofNat] at gFlag g0 g1 g2 g3 g4 push
  rw [← BitVec.sub_eq_add_neg] at push fFinal
  simp only [flaggedFold, m0Fold, m1Fold, m2Fold, m3Fold, m4Fold] at g0 g1 g2 g3 g4 push fFinal
  rw [finalFold] at fFinal
  refine ⟨?next, final, a, ?eval, ?post, repr⟩
  case eval =>
    cfg_eval
    simp only [spGet, flagFold, flaggedFold, maskFold, h0, h1, h2, h3, h4', m0Fold,
      m1Fold, m2Fold, m3Fold, m4Fold, finalFold, rFlag, gFlag, r0, r1, r2, r3, r4,
      g0, g1, g2, g3, g4, push, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, slot, finalWords, finalFlag, fFinal⟩
    · intro ⟨i, bound⟩ hi
      have h := wide ⟨i, bound⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Affine.Compressed
