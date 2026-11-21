import K256.Proofs.Ecdh.Affine.Inverse.Zero.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Correct
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Generator.Entry

namespace K256.Proofs.Ecdh.Affine.Inverse.Zero

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

open K256.Proofs.Generate.Generator.Affine K256.Proofs.Generate.Generator.Affine.Invert K256.Proofs.Generate.Generator.Affine.Invert.Core

set_option maxRecDepth 4096 in
private theorem correctionCallBlock {b : Registers} {p : Ram} {q dst : Word} (neg : Bool)
    (rsp : b[4].get 64 = q)
    (win : Writable Extracted.programImage p (q - 8) 344)
    (ptr : memLoad p (q + 320) 64 = dst)
    (modPtr : memLoad p (q + 160) 64 = 0x2021e0)
    (sign : memLoad p (q + 152) 8 = (if neg then 1 else 0))
    (originalZero : (((memLoad p (q + 312) 64 ||| memLoad p (q + 296) 64) |||
      memLoad p (q + 288) 64) ||| memLoad p (q + 304) 64) = 0) :
    ∃ c : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1093fe, b, p⟩ =
      .call ⟨.l109c00, c, memStore p (q - 8) (0x109448 : Word)⟩ (K256.Proofs.Generate.Generator.callFrame .l109448 0x109448) ∧
      c[4] = ⟨64, q - 8⟩ ∧ c[7] = ⟨64, dst⟩ ∧ c[14] = ⟨64, dst⟩ ∧
      c[3].width = 64 ∧ c[3].get 8 = 0 ∧ c[6].get 64 = q + 208 ∧
      c[1].get 64 = 0x2021e0 ∧ (c[2].get 8 &&& 1) = (if neg then 1 else 0) ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l1093fe [rsp, ptr, modPtr]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · change (mergeGPR 8 _ _).setWidth 8 = _
      simp only [setWidth_mergeGPR8, orFlags, originalZero]
      rfl
    · have byte := extractLsb'_memLoad p (q + 152) (n := 32) 0 8 (by decide) (by decide) (by decide)
      change (memLoad p (q + 152) 32).setWidth 8 = memLoad p ((q + 152) + 0) 8 at byte
      rw [show q + 152 + 0 = q + 152 by bv_omega, sign] at byte
      change (((memLoad p (q + 152) 32).setWidth 64).setWidth 8 &&& 1) = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), byte]
      cases neg <;> decide
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 4096 in
private theorem correctionReturnBlock {c : Registers} {p : Ram} {q : Word}
    (rsp : c[4].get 64 = q) (rbx : c[3].get 8 = 0) (r14 : c[14].get 64 = q + 504)
    (win : Readable p q 408) (retRead : Readable p (q + 408) 8)
    (dest : Writable Extracted.programImage p (q + 536) 1)
    (ret : memLoad p (q + 408) 64 = 0x10ed84) :
    ∃ out, CalleeExec .l109448 c p out ∧ out.tag = some ⟨64, 0x10ed84⟩ ∧
      out.store = memStore p (q + 536) (0 : BitVec 8) ∧ out.values[4] = ⟨64, q + 416⟩ ∧
      (∀ (i : Fin Reg.count) (off : Nat), (i.val,off) ∈ [(3,360),(5,400),(12,368),(13,376),(14,384),(15,392)] →
        out.values[i] = ⟨64, memLoad p (q + BitVec.ofNat 64 off) 64⟩) ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = c[i] := by
  have byte : (c[3].get 64).setWidth 8 = 0 := (BitVec.setWidth_setWidth_of_le _ (by decide)).trans rbx
  refine ⟨?out, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rsp, r14, Lift.reduceAddOffset, setWidth_mergeGPR8, byte]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_)
    all_goals try slot_guard using code_l109448
    all_goals try simp (disch := store_disch) only [memLoad_memStore_of_rangeApart, ret, BitVec.reduceToNat]
    all_goals try exact ⟨by slot_guard using code_l109448, by decide⟩
    all_goals try rfl
  case post =>
    refine ⟨rfl, by
      apply congrArg (fun byte : BitVec 8 => memStore p (q + 536) byte)
      exact BitVec.and_zero, rfl, ?_, ?_⟩
    · intro ⟨i, hi⟩ off hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
    · intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl

private theorem finish_add {q : Word} (high : q.toNat + 537 ≤ 2^32) (k : Word)
    (hk : k.toNat ≤ 536) : (q + k).toNat = q.toNat + k.toNat := by
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
theorem finish {a : Registers} {m : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}
    (h : ZeroEntry a m sp z w) {b : Registers} {p : Ram} {d e : Int}
    (state : ZeroLoopState a m sp z 591 b p d e) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1093fe, b, p⟩, []⟩ out ∧
      ZeroResult a m sp out := by
  let q := base sp
  have spEq : sp = q + 408 := by dsimp only [q, base]; bv_omega
  have qs : q.toNat = sp.toNat - 408 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by have := h.low; change 408 ≤ _; omega))
  have low : 328 ≤ q.toNat := by have := h.low; omega
  have high : q.toNat + 537 ≤ 2^32 := by have := h.high; omega
  have st : sp - 736 = q - 328 := by rw [spEq]; bv_omega
  have dst : sp + 96 = q + 504 := by rw [spEq]; bv_omega
  have flag : sp + 128 = q + 536 := by rw [spEq]; bv_omega
  have sub := finish_sub low
  have add := finish_add high
  have wstack := h.stack
  rw [st] at wstack
  have f := state.frame
  rw [st] at f
  have stp := wstack.of_frame f
  have dstp := h.destination.of_frame f
  rw [dst] at dstp
  have retp : memLoad p sp 64 = 0x10ed84 := by
    refine (f.memLoad_eq ?_).trans h.ret
    simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, sub, Nat.reduceDiv, BitVec.reduceToNat]
    have := h.high
    omega
  have win : Writable Extracted.programImage p (q - 8) 344 := by
    apply stp.sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  obtain ⟨_, neg, _, fSign, _⟩ := state.fValue
  have sign : memLoad p (q + 152) 8 = (if neg then 1 else 0) := by
    rw [show q + 152 = (q + 120) + 32 by bv_omega]
    exact fSign
  obtain ⟨c, call, csp, cdi, c14, cw3, c3, csi, ccx, cdx, ckeep⟩ :=
    correctionCallBlock neg (show b[4].get 64 = q from congrArg (Value.get 64) state.rsp)
      win (state.outputPtr.trans dst) state.modulusPtr sign state.originalZero
  let p₁ := memStore p (q - 8) (0x109448 : Word)
  have push : RamWriteFrame p p₁ [⟨(q - 8).toNat,8⟩] := by
    dsimp only [p₁]
    slot_state region
  have fullPush : RamWriteFrame m p₁ [⟨(q - 328).toNat,736⟩] := by
    apply f.trans push
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    simp (disch := decide) only [sub, BitVec.reduceToNat]
    omega
  have stack₁ := wstack.of_frame fullPush
  have destination₁ := dstp.of_frame push
  have deep : q - 8 - BitVec.ofNat 64 56 = q - 64 := by bv_omega
  have cf : CalleeFrame c p₁ (q - 8) (q + 504) 0x109448 56 32 := by
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
  have src : SignedSource p₁ (q - 8) (q + 504) (c[6].get 64) 56 32 d := by
    rw [csi]
    refine ⟨?_, Or.inr ?_, Or.inl ?_, ?_⟩
    · apply stack₁.readable.sub <;> simp (disch := decide) only [sub, add, BitVec.reduceToNat] <;> omega
    · simp (disch := decide) only [sub, add, BitVec.reduceToNat]; omega
    · simp (disch := decide) only [add, BitVec.reduceToNat]; omega
    · obtain ⟨v, n, words, sign', val⟩ := state.dValue
      change WordsAt p (q + 208) 64 v at words
      change memLoad p ((q + 208) + 32) 8 = _ at sign'
      refine ⟨v,n, words.of_frame push (by decide) ?_, (push.memLoad_eq ?_).trans sign', val⟩
      all_goals change Outside _ _ _
      all_goals simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, Nat.reduceDiv,
        Nat.reduceMul, Lift.reduceAddOffset, add, sub, BitVec.reduceToNat]
      all_goals omega
  obtain ⟨o, run, res, _⟩ := correctSign neg cf src ccx cdx state.dBound
  have cfFrame := res.frame
  rw [deep] at cfFrame
  let regions : List MemoryRegion := [⟨(q - 64).toNat,64⟩,⟨(q + 504).toNat,32⟩]
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
  have apart (k : Word) (hk : k.toNat ≤ 408) (len : Nat) (hlen : len ≤ 32) :
      Outside regions (q + k) len := by
    simp (disch := first | decide | omega) only [Outside, regions, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, add, sub, BitVec.reduceToNat]
    omega
  have winOut : Readable o.store q 408 := by
    apply (stp.readable.of_frame corr).sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have retRead := (h.source.of_frame f).of_frame corr
  rw [spEq] at retRead retp
  have dstOut := dstp.of_frame corr
  have retOut := (corr.memLoad_eq (k := 64) (apart 408 (by decide) 8 (by decide))).trans retp
  have bb := res.kept 3 (by decide) cw3
  have rr := res.kept 14 (by decide) (congrArg Value.width c14)
  have spOut : o.values[4].get 64 = q := by
    rw [res.rsp]; change q - 8 + 8 = q; bv_omega
  obtain ⟨out, tailRun, tag, store, osp, saves, controls⟩ :=
    correctionReturnBlock spOut ((congrArg (Value.get 8) bb).trans c3)
      (show o.values[14].get 64 = q + 504 from congrArg (Value.get 64) (rr.trans c14)) winOut (retRead.sub (by omega) (by omega))
      (dstOut.sub (by simp (disch := decide) only [add, BitVec.reduceToNat]; omega)
        (by simp (disch := decide) only [add, BitVec.reduceToNat]; omega)) retOut
  let frame := K256.Proofs.Generate.Generator.callFrame .l109448 0x109448
  have accepts : frame.Accepts (dialect Extracted.programImage) o.tag = true := by
    rw [res.returned]
    rfl
  have execution : program.Exec (dialect Extracted.programImage) ⟨⟨.l1093fe, b, p⟩, []⟩ out :=
    ParseSignature.exec_call (P := program) (D := dialect Extracted.programImage)
      (callee := ⟨.l109c00, c, p₁⟩) (frame := frame) (output := o) call run accepts tailRun
  refine ⟨out, execution, tag, ?_, ?_, ?_, ?_⟩
  · calc
      out.values[4] = ⟨64, q + 416⟩ := osp
      _ = ⟨64, (q + 408) + 8⟩ := congrArg (fun x : Word => (⟨64, x⟩ : Value))
        (BitVec.add_assoc q 408 8).symm
      _ = ⟨64, sp + 8⟩ := congrArg (fun x : Word => (⟨64, x + 8⟩ : Value)) spEq.symm
  · intro i hi
    have restore (off off' : Nat) (hw : i.val ∈ [3,5,12,13,14,15])
        (hs : (i.val,off) ∈ [(3,360),(5,400),(12,368),(13,376),(14,384),(15,392)])
        (he : (i.val,off') ∈ [(3,48),(5,8),(12,40),(13,32),(14,24),(15,16)])
        (ho : off ≤ 408) (total : off + off' = 408) : out.values[i] = a[i] := by
      have eq : q + BitVec.ofNat 64 off = sp - BitVec.ofNat 64 off' := by
        rw [spEq, ← BitVec.add_sub_cancel (q + BitVec.ofNat 64 off) (BitVec.ofNat 64 off')]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add, total]
        rfl
      have retLoad := corr.memLoad_eq (k := 64) (apart (BitVec.ofNat 64 off)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) 8 (by decide))
      rw [saves i off hs, retLoad, eq, state.saved i off' he, mk_get64 _ (h.widths i hw)]
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · apply restore 360 48 <;> simp -failIfUnchanged only <;> decide
    · apply restore 400 8 <;> simp -failIfUnchanged only <;> decide
    · apply restore 368 40 <;> simp -failIfUnchanged only <;> decide
    · apply restore 376 32 <;> simp -failIfUnchanged only <;> decide
    · apply restore 384 24 <;> simp -failIfUnchanged only <;> decide
    · apply restore 392 16 <;> simp -failIfUnchanged only <;> decide
    all_goals
      exact (controls _ (by simp only; decide)).trans ((res.controls _ (by simp only; decide)).trans
        ((ckeep _ (by simp only; decide)).trans (state.kept _ (by simp only; decide))))
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
  · rw [store, flag]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Ecdh.Affine.Inverse.Zero
