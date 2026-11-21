import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Finish.CorrectionCall
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Finish.Return
import K256.Proofs.Verify.Core.Scalars.Inverse.CorrectSign
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Arithmetic
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert (value)
open Generate.Generator.Affine.Invert.Core (CalleeFrame SignedSource stackImage)

private theorem terminalWords {a b : Registers} {m p : Ram} {sp : Word} {s n : Nat}
    {d e : Int} (h : Entry a m sp s) (st : LoopState a m sp s n b p d e)
    (exit : n = 591 ∨ (Inverse.model s n).g = 0) :
    ∃ neg : Bool, WordsAt p (base sp + 8) 64 (#v[1,0,0,0] : Vector Word 4) ∧
      memLoad p (base sp + 40) 8 = (if neg then 1 else 0) ∧
      ((if neg then -d else d) % (domain.n : Int)).toNat = Curve.inverse domain.n s := by
  have unit := Inverse.unit_at_exit h.positive h.bound exit
  have inv := Inverse.coefficient_at_exit h.positive h.bound exit st.dInvariant
  obtain ⟨v, neg, hv, hs, he⟩ := st.fValue
  have mag : value v = 1 := by cases neg <;> simpa [he] using unit
  have low : v[0] = 1 ∧ v[1] = 0 ∧ v[2] = 0 ∧ v[3] = 0 := by
    unfold value at mag
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> first | (change _ = 1; omega) | (change _ = 0; omega)
  refine ⟨neg, ?_, ?_, ?_⟩
  · have veq : v = #v[1,0,0,0] := by
      apply Vector.ext
      intro i hi
      have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases c with rfl|rfl|rfl|rfl
      all_goals first | exact low.1 | exact low.2.1 | exact low.2.2.1 | exact low.2.2.2
    exact veq ▸ hv
  · rw [show base sp + 40 = base sp + 8 + 32 by bv_omega]; exact hs
  · cases neg <;> simpa [he, mag] using inv

private theorem words_value (v : Vector Word 4) : v = scalarWords (value v) := by
  let q : Common.Invert.LinearCombination.Limbs := ⟨v[0], v[1], v[2], v[3]⟩
  have hv : q.toNat = value v := by unfold value; dsimp [q, Common.Invert.LinearCombination.Limbs.toNat]; omega
  rw [← hv, ← Generate.Generator.Multiply.Split.Addition.limbWords_eq]
  apply Vector.ext
  intro i hi
  have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases c with rfl|rfl|rfl|rfl <;> rfl

private theorem finish_add {q : Word} (high : q.toNat + 441 ≤ 2^32) (k : Word)
    (hk : k.toNat ≤ 440) : (q + k).toNat = q.toNat + k.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

private theorem finish_sub {q : Word} (low : 328 ≤ q.toNat) (k : Word) (hk : k.toNat ≤ 328) :
    (q - k).toNat = q.toNat - k.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))

private theorem mk_get64 (v : Value) (hw : v.width = 64) : ⟨64,v.get 64⟩ = v := by
  rcases v with ⟨n, x⟩
  change n = 64 at hw
  subst n
  rfl

set_option maxRecDepth 4096 in
theorem finish {a b : Registers} {m p : Ram} {sp : Word} {s n : Nat} {d e : Int}
    (h : Entry a m sp s) (state : LoopState a m sp s n b p d e)
    (exit : n = 591 ∨ (Inverse.model s n).g = 0) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109948,b,p⟩,[]⟩ out ∧
      Result a m sp s out := by
  let q := base sp
  have spEq : sp = q + 392 := by dsimp only [q, base]; bv_omega
  have qs : q.toNat = sp.toNat - 392 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by have := h.depthBound; change 392 ≤ _; omega))
  have low : 328 ≤ q.toNat := by have := h.depthBound; omega
  have high : q.toNat + 441 ≤ 2^32 := by have := h.high; omega
  have st : sp - BitVec.ofNat 64 720 = q - 328 := by rw [spEq]; bv_omega
  have dst : sp + 16 = q + 408 := by rw [spEq]; bv_omega
  have flag : sp + 48 = q + 440 := by rw [spEq]; bv_omega
  have sub := finish_sub low
  have add := finish_add high
  have wstack := h.stack
  rw [st] at wstack
  have f : RamWriteFrame m p [⟨(sp - BitVec.ofNat 64 720).toNat,720⟩] := state.frame
  rw [st] at f
  have stp := wstack.of_frame f
  have dstp := h.output.of_frame f
  rw [dst] at dstp
  have retp : memLoad p sp 64 = 0x10a0f2 := by
    refine (f.memLoad_eq ?_).trans h.retAddr
    simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, sub, Nat.reduceDiv, BitVec.reduceToNat]
    have := h.high
    omega
  have win : Writable Extracted.programImage p (q - 8) 344 := by
    apply stp.sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  obtain ⟨neg, fwords, sign, inv⟩ := terminalWords h state exit
  obtain ⟨c, call, csp, cdi, c14, cw3, c3, csi, ccx, cdx, ckeep⟩ :=
    correctionCallBlock neg (show b[4].get 64 = q from congrArg (Value.get 64) state.rsp)
      win (state.outputPtr.trans dst) state.modulusPtr sign state.originalNonzero
  let p₁ := memStore p (q - 8) (0x109989 : Word)
  have push : RamWriteFrame p p₁ [⟨(q - 8).toNat,8⟩] := by
    dsimp only [p₁]
    slot_state region
  have fullPush : RamWriteFrame m p₁ [⟨(q - 328).toNat,720⟩] := by
    apply f.trans push
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    simp (disch := decide) only [sub, BitVec.reduceToNat]
    omega
  have stack₁ := wstack.of_frame fullPush
  have destination₁ := dstp.of_frame push
  have deep : q - 8 - BitVec.ofNat 64 56 = q - 64 := by bv_omega
  have cf : CalleeFrame c p₁ (q - 8) (q + 408) 0x109989 56 32 := by
    refine ⟨csp, cdi, (ckeep 22 (by decide)).trans ((state.kept 22 (by decide)).trans h.df),
      stackImage wstack fullPush h.image, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩
    · rw [sub 8 (by decide)]; change 56 ≤ q.toNat - 8; omega
    · have := h.aligned
      rw [sub 8 (by decide)]; change (q.toNat - 8) % 16 = 8; omega
    · apply stack₁.readable.sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [deep]
      apply stack₁.sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
    · exact destination₁.sub (by omega) (by omega)
    · right; simp (disch := decide) only [add, sub, BitVec.reduceToNat]; omega
  have src : SignedSource p₁ (q - 8) (q + 408) (c[6].get 64) 56 32 d := by
    rw [csi]
    refine ⟨?_, Or.inr ?_, Or.inl ?_, ?_⟩
    · apply stack₁.readable.sub <;> simp (disch := decide) only [sub, add, BitVec.reduceToNat] <;> omega
    · simp (disch := decide) only [sub, add, BitVec.reduceToNat]; omega
    · simp (disch := decide) only [add, BitVec.reduceToNat]; omega
    · obtain ⟨v, n, words, sign', val⟩ := state.dValue
      change WordsAt p (q + 96) 64 v at words
      change memLoad p ((q + 96) + 32) 8 = _ at sign'
      refine ⟨v,n, words.of_frame push (by decide) ?_, (push.memLoad_eq ?_).trans sign', val⟩
      all_goals change Outside _ _ _
      all_goals simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, Nat.reduceDiv,
        Nat.reduceMul, Lift.reduceAddOffset, add, sub, BitVec.reduceToNat]
      all_goals omega
  obtain ⟨o, run, res, v, vw, vv⟩ := correctSign neg cf src ccx cdx state.dBound
  have cfFrame := res.frame
  rw [deep] at cfFrame
  let regions : List MemoryRegion := [⟨(q - 64).toNat,64⟩,⟨(q + 408).toNat,32⟩]
  have corr : RamWriteFrame p o.store regions := by
    refine ((RamWriteFrame.refl p regions).trans push ?_).trans cfFrame ?_
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_cons_self, ?_⟩
      simp (disch := decide) only [sub, BitVec.reduceToNat]; omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl|rfl
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (show 56 ≤ 64 by decide) _⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have apart (k : Word) (hk : k.toNat ≤ 392) (len : Nat) (hlen : k.toNat + len ≤ 408) :
      Outside regions (q + k) len := by
    simp (disch := first | decide | omega) only [Outside, regions, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, add, sub, BitVec.reduceToNat]
    omega
  have winOut : Readable o.store q 392 := by
    apply (stp.readable.of_frame corr).sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have retRead := (h.returnSlot.of_frame f).of_frame corr
  rw [spEq] at retRead retp
  have dstOut := dstp.of_frame corr
  have retOut := (corr.memLoad_eq (k := 64) (apart 392 (by decide) 8 (by decide))).trans retp
  have bb := res.kept 3 (by decide) cw3
  have rr := res.kept 14 (by decide) (congrArg Value.width c14)
  have spOut : o.values[4].get 64 = q := by
    rw [res.rsp]; change q - 8 + 8 = q; bv_omega
  obtain ⟨out, tailRun, tag, store, osp, saves, controls⟩ :=
    correctionReturnBlock spOut ((congrArg (Value.get 8) bb).trans c3)
      (show o.values[14].get 64 = q + 408 from congrArg (Value.get 64) (rr.trans c14)) winOut retRead
      (dstOut.sub (by simp (disch := decide) only [add, BitVec.reduceToNat]; omega)
        (by simp (disch := decide) only [add, BitVec.reduceToNat]; omega)) retOut
      (fwords.of_frame corr (by decide) (apart 8 (by decide) 32 (by decide)))
  refine ⟨out, ParseSignature.exec_call call run (by rw [res.returned]; rfl) tailRun, ⟨tag, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [osp, spEq]; congr 1; bv_omega
  · intro i hi width
    have restore (off off' : Nat)
        (hs : (i.val,off) ∈ [(3,344),(5,384),(12,352),(13,360),(14,368),(15,376)])
        (he : (i.val,off') ∈ [(3,48),(5,8),(12,40),(13,32),(14,24),(15,16)])
        (ho : off ≤ 392) (total : off + off' = 392) : out.values[i] = a[i] := by
      have eq : q + BitVec.ofNat 64 off = sp - BitVec.ofNat 64 off' := by
        rw [spEq, ← BitVec.add_sub_cancel (q + BitVec.ofNat 64 off) (BitVec.ofNat 64 off')]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add, total]
        rfl
      have retLoad := corr.memLoad_eq (k := 64) (apart (BitVec.ofNat 64 off)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) 8 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
      rw [saves i off hs, retLoad, eq, state.saved i off' he, mk_get64 _ width]
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · apply restore 344 48 <;> simp -failIfUnchanged only <;> decide
    · apply restore 384 8 <;> simp -failIfUnchanged only <;> decide
    · apply restore 352 40 <;> simp -failIfUnchanged only <;> decide
    · apply restore 360 32 <;> simp -failIfUnchanged only <;> decide
    · apply restore 368 24 <;> simp -failIfUnchanged only <;> decide
    · apply restore 376 16 <;> simp -failIfUnchanged only <;> decide
  · intro i hi
    exact (controls i hi).trans ((res.controls i hi).trans ((ckeep i hi).trans (state.kept i hi)))
  · rw [store, st, dst]
    apply RamWriteFrame.memStore
    · refine ((RamWriteFrame.refl m _).trans f ?_).trans corr ?_
      · intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
      · intro r hr
        simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl|rfl
        · refine ⟨_, List.mem_cons_self, ?_⟩
          simp (disch := decide) only [sub, BitVec.reduceToNat]; omega
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (show 32 ≤ 33 by decide) _⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp (disch := decide) only [InRegion, add, BitVec.reduceToNat, Nat.reduceDiv]; omega
  · rw [store, dst, ← vv.trans inv, ← words_value v]
    have byteFrame : RamWriteFrame o.store (memStore o.store (q + 440) (1 : BitVec 8)) [⟨(q + 440).toNat,1⟩] := by
      slot_state region
    refine vw.of_frame byteFrame (by decide) ?_
    simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, add, Nat.reduceDiv, Nat.reduceMul, BitVec.reduceToNat]; omega
  · rw [store, flag]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
