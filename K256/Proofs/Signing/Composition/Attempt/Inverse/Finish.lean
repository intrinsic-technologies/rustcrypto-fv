import K256.Proofs.Signing.Composition.Attempt.Inverse.LoopState
import K256.Proofs.Signing.Transfer.Generator.Blocks
import K256.Proofs.Verify.Core.Scalars.Inverse.CorrectSign
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Arithmetic

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Common.Field Generate.LIR
open Generate.Generator.Affine.Invert (value)
open Generate.Generator.Affine.Invert.Core (base signedAt CalleeResult CalleeFrame SignedSource
  stackImage CalleeExec)
open Generate.Generator (callFrame)
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

private theorem terminalWords {a b : Registers} {m p : Ram} {sp : Word} {s n : Nat}
    {d e : Int} (h : Entry a m sp s) (st : LoopState a m sp s n b p d e)
    (exit : n = 591 ∨ (Verify.Core.Scalars.Inverse.model s n).g = 0) :
    ∃ neg : Bool, WordsAt p (base sp + 120) 64 (#v[1,0,0,0] : Vector Word 4) ∧
      memLoad p (base sp + 152) 8 = (if neg then 1 else 0) ∧
      ((if neg then -d else d) % (domain.n : Int)).toNat = Curve.inverse domain.n s := by
  have unit := Verify.Core.Scalars.Inverse.unit_at_exit h.positive h.bound exit
  have inv := Verify.Core.Scalars.Inverse.coefficient_at_exit h.positive h.bound exit st.dInvariant
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
  · rw [show base sp + 152 = base sp + 120 + 32 by bv_omega]; exact hs
  · cases neg <;> simpa [he, mag] using inv

private theorem words_value (v : Vector Word 4) : v = scalarWords (value v) := by
  let q : Common.Invert.LinearCombination.Limbs := ⟨v[0], v[1], v[2], v[3]⟩
  have hv : q.toNat = value v := by unfold value; dsimp [q, Common.Invert.LinearCombination.Limbs.toNat]; omega
  rw [← hv, ← Generate.Generator.Multiply.Split.Addition.limbWords_eq]
  apply Vector.ext
  intro i hi
  have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases c with rfl|rfl|rfl|rfl <;> rfl

private theorem finish_add {q : Word} (high : q.toNat + 457 ≤ 2^32) (k : Word)
    (hk : k.toNat ≤ 456) : (q + k).toNat = q.toNat + k.toNat := by
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
private theorem correctionCallBlock {b : Registers} {p : Ram} {q dst : Word} (neg : Bool)
    (rsp : b[4].get 64 = q)
    (win : Writable Extracted.programImage p (q - 8) 344)
    (ptr : memLoad p (q + 320) 64 = dst)
    (modPtr : memLoad p (q + 160) 64 = 0x2021a0)
    (sign : memLoad p (q + 152) 8 = (if neg then 1 else 0))
    (nonzero : (((memLoad p (q + 312) 64 ||| memLoad p (q + 296) 64) |||
      memLoad p (q + 288) 64) ||| memLoad p (q + 304) 64) ≠ 0) :
    ∃ c : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1093fe, b, p⟩ =
      .call ⟨.l109c00, c, memStore p (q - 8) (0x109448 : Word)⟩ (callFrame .l109448 0x109448) ∧
      c[4] = ⟨64, q - 8⟩ ∧ c[7] = ⟨64, dst⟩ ∧ c[14] = ⟨64, dst⟩ ∧
      c[3].width = 64 ∧ c[3].get 8 = 1 ∧ c[6].get 64 = q + 208 ∧
      c[1].get 64 = 0x2021a0 ∧ (c[2].get 8 &&& 1) = (if neg then 1 else 0) ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l1093fe [rsp, ptr, modPtr]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · change (mergeGPR 8 _ _).setWidth 8 = _
      simp [setWidth_mergeGPR8, orFlags]
      intro h₁ h₂ h₃ h₄
      exact nonzero (by simp [h₁, h₂, h₃, h₄])
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
    (rsp : c[4].get 64 = q) (rbx : c[3].get 8 = 1) (r14 : c[14].get 64 = q + 424)
    (win : Readable p q 408) (retRead : Readable p (q + 408) 8)
    (dest : Writable Extracted.programImage p (q + 456) 1)
    (ret : memLoad p (q + 408) 64 = 0x109db2)
    (unit : WordsAt p (q + 120) 64 (#v[1,0,0,0] : Vector Word 4)) :
    ∃ out, CalleeExec .l109448 c p out ∧ out.tag = some ⟨64, 0x109db2⟩ ∧
      out.store = memStore p (q + 456) (1 : BitVec 8) ∧ out.values[4] = ⟨64, q + 416⟩ ∧
      (∀ (i : Fin Reg.count) (off : Nat), (i.val,off) ∈ [(3,360),(5,400),(12,368),(13,376),(14,384),(15,392)] →
        out.values[i] = ⟨64, memLoad p (q + BitVec.ofNat 64 off) 64⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = c[i]) ∧
      out.values[9] = c[9] := by
  have u0 := unit 0 (by decide)
  have u1 := unit 1 (by decide)
  have u2 := unit 2 (by decide)
  have u3 := unit 3 (by decide)
  change memLoad p (q + 120 + 0) 64 = 1 at u0
  change memLoad p (q + 120 + 8) 64 = 0 at u1
  change memLoad p (q + 120 + 16) 64 = 0 at u2
  change memLoad p (q + 120 + 24) 64 = 0 at u3
  simp only [Lift.reduceAddOffset] at u0 u1 u2 u3
  have byte : (c[3].get 64).setWidth 8 = 1 := (BitVec.setWidth_setWidth_of_le _ (by decide)).trans rbx
  refine ⟨?out, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rsp, r14, reduceAddOffset, u0, u1, u2, u3, orFlags, Option.getD_some,
      setWidth_mergeGPR8, byte]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_)
    all_goals try slot_guard using code_l109448
    all_goals try simp (disch := store_disch) only [memLoad_memStore_of_rangeApart, ret, BitVec.reduceToNat]
    all_goals try exact ⟨by slot_guard using code_l109448, by decide⟩
    all_goals try rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
    · intro ⟨i, hi⟩ off hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
    · intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl

private def CorrectionOutcome :
    Transfer Value Ram Generate.LIR.Label (fun _ => Reg.count) Reg.count → Prop
  | .stuck => True
  | .returned out => out.values[9].width = 64
  | _ => False

private theorem correctionOutcomeGuard {p : Prop} [Decidable p]
    {next : Transfer Value Ram Generate.LIR.Label (fun _ => Reg.count) Reg.count}
    (h : CorrectionOutcome next) : CorrectionOutcome (if p then next else .stuck) := by
  split
  · exact h
  · trivial

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem correctionBlockShape (a : Registers) (m : Ram) :
    CorrectionOutcome (Generate.LIR.program.runBlock (dialect Extracted.programImage) ⟨.l109c00,a,m⟩) := by
  cfg_eval [b_l109c00, b_l109c00_1, b_l109c00_2, b_l109c00_3, b_l109c00_4, b_l109c00_5]
  repeat' apply correctionOutcomeGuard
  rfl

private theorem correctSignBlock {a : Registers} {m : Ram} {sp dst ret : Word} {d : Int}
    (neg : Bool) (fr : CalleeFrame a m sp dst ret 56 32)
    (src : SignedSource m sp dst (a[6].get 64) 56 32 d)
    (ptr : a[1].get 64 = 0x2021a0)
    (flag : (a[2].get 8 &&& 1) = (if neg then 1 else 0)) (bound : d.natAbs < domain.n) :
    ∃ out, CalleeExec .l109c00 a m out ∧ CalleeResult a m sp dst ret 56 32 out ∧
      out.values[9].width = 64 ∧
      ∃ v : Vector Word 4, WordsAt out.store dst 64 v ∧
        value v = ((if neg then -d else d) % (domain.n : Int)).toNat := by
  obtain ⟨out, verification, post, result⟩ :=
    Verify.Core.Scalars.Inverse.correctSign neg fr src ptr flag bound
  let D := dialect Extracted.programImage
  let loc : Verify.LIR.lifted.Location := ⟨.l109c00,a,m⟩
  let gen : Generate.LIR.lifted.Location := ⟨.l109c00,a,m⟩
  have block : Generate.Serialize.Relabel.block Signing.Transfer.Generator.target
      (Generate.LIR.program.blocks .l109c00) =
      Generate.Serialize.Relabel.block some (Verify.LIR.program.blocks .l109c00) :=
    Signing.Transfer.Generator.blocks .l109c00 .l109c00 rfl
  have evaluated : Generate.Serialize.Relabel.transfer Signing.Transfer.Generator.target
      (Generate.LIR.program.runBlock D gen) =
      Generate.Serialize.Relabel.transfer some (Verify.LIR.program.runBlock D loc) := by
    simp only [Program.runBlock, gen, loc, ← Generate.Serialize.Relabel.eval_block, block]
  have shape : CorrectionOutcome (Generate.LIR.program.runBlock D gen) := correctionBlockShape a m
  cases run : Generate.LIR.program.runBlock D gen with
  | jump _ =>
    rw [run] at shape
    exact False.elim shape
  | call _ _ =>
    rw [run] at shape
    exact False.elim shape
  | stuck =>
    rw [run] at evaluated
    have stopped : Verify.LIR.program.runBlock D loc = .stuck := by
      cases hv : Verify.LIR.program.runBlock D loc <;> rw [hv] at evaluated <;> cases evaluated
    have reply : Verify.LIR.program.step D ⟨loc, []⟩ = .stuck := by
      simp only [Program.step, stopped, Transfer.next]
    cases verification with
    | done h => exact nomatch reply.symm.trans h
    | next h _ => exact nomatch reply.symm.trans h
  | returned actual =>
    rw [run] at evaluated shape
    have done : Verify.LIR.program.runBlock D loc = .returned actual := by
      cases hv : Verify.LIR.program.runBlock D loc <;> rw [hv] at evaluated <;> cases evaluated
      rfl
    have reply : Verify.LIR.program.step D ⟨loc, []⟩ = .done actual := by
      simp only [Program.step, done, Transfer.next]
    have eq : actual = out := by
      cases verification with
      | done h => exact Outcome.done.inj (reply.symm.trans h)
      | next h _ => exact nomatch reply.symm.trans h
    subst out
    have finished : CalleeExec .l109c00 a m actual := .done (by
      change (Generate.LIR.program.runBlock D gen).next D [] = .done actual
      simp only [run, Transfer.next])
    exact ⟨actual, finished, post, shape, result⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem finish {a : Registers} {m : Ram} {p : Word} {k : Nat} (h : Entry a m p k)
    {b : Registers} {n : Ram} {d e : Int} (state : LoopState a m p k 591 b n d e) :
    ∃ out, Generate.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l1093fe,b,n⟩,[]⟩ out ∧
      CalleeResult a m p (p+16) 0x109db2 736 33 out ∧
      WordsAt out.store (p+16) 64 (scalarWords (Curve.inverse domain.n k)) ∧
      memLoad out.store (p+48) 8 = 1 ∧ out.values[9].width = 64 := by
  let q := base p
  have spEq : p = q + 408 := by dsimp only [q, base]; bv_omega
  have qs : q.toNat = p.toNat - 408 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by have := h.depthBound; change 408 ≤ _; omega))
  have low : 328 ≤ q.toNat := by have := h.depthBound; omega
  have high : q.toNat + 457 ≤ 2^32 := by have := h.high; omega
  have st : p - BitVec.ofNat 64 736 = q - 328 := by rw [spEq]; bv_omega
  have dst : p + 16 = q + 424 := by rw [spEq]; bv_omega
  have flag : p + 48 = q + 456 := by rw [spEq]; bv_omega
  have sub := finish_sub low
  have add := finish_add high
  have wstack := h.stack
  rw [st] at wstack
  have f : RamWriteFrame m n [⟨(p - BitVec.ofNat 64 736).toNat,736⟩] := state.frame
  rw [st] at f
  have stp := wstack.of_frame f
  have dstp := h.output.of_frame f
  rw [dst] at dstp
  have retp : memLoad n p 64 = 0x109db2 := by
    refine (f.memLoad_eq ?_).trans h.retAddr
    simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, sub, Nat.reduceDiv, BitVec.reduceToNat]
    have := h.high
    omega
  have win : Writable Extracted.programImage n (q - 8) 344 := by
    apply stp.sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  obtain ⟨neg, fwords, sign, inv⟩ := terminalWords h state (Or.inl rfl)
  obtain ⟨c, call, csp, cdi, c14, cw3, c3, csi, ccx, cdx, ckeep⟩ :=
    correctionCallBlock neg (show b[4].get 64 = q from congrArg (Value.get 64) state.rsp)
      win (state.outputPtr.trans dst) state.modulusPtr sign state.originalNonzero
  let p₁ := memStore n (q - 8) (0x109448 : Word)
  have push : RamWriteFrame n p₁ [⟨(q - 8).toNat,8⟩] := by
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
  have cf : CalleeFrame c p₁ (q - 8) (q + 424) 0x109448 56 32 := by
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
  have src : SignedSource p₁ (q - 8) (q + 424) (c[6].get 64) 56 32 d := by
    rw [csi]
    refine ⟨?_, Or.inr ?_, Or.inl ?_, ?_⟩
    · apply stack₁.readable.sub <;> simp (disch := decide) only [sub, add, BitVec.reduceToNat] <;> omega
    · simp (disch := decide) only [sub, add, BitVec.reduceToNat]; omega
    · simp (disch := decide) only [add, BitVec.reduceToNat]; omega
    · obtain ⟨v, isNegative, words, sign', val⟩ := state.dValue
      change WordsAt n (q + 208) 64 v at words
      change memLoad n ((q + 208) + 32) 8 = _ at sign'
      refine ⟨v,isNegative, words.of_frame push (by decide) ?_, (push.memLoad_eq ?_).trans sign', val⟩
      all_goals change Outside _ _ _
      all_goals simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, Nat.reduceDiv,
        Nat.reduceMul, Lift.reduceAddOffset, add, sub, BitVec.reduceToNat]
      all_goals omega
  obtain ⟨o, run, res, width, v, vw, vv⟩ := correctSignBlock neg cf src ccx cdx state.dBound
  have cfFrame := res.frame
  rw [deep] at cfFrame
  let regions : List MemoryRegion := [⟨(q - 64).toNat,64⟩,⟨(q + 424).toNat,32⟩]
  have corr : RamWriteFrame n o.store regions := by
    refine ((RamWriteFrame.refl n regions).trans push ?_).trans cfFrame ?_
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_cons_self, ?_⟩
      simp (disch := decide) only [sub, BitVec.reduceToNat]; omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl|rfl
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (show 56 ≤ 64 by decide) _⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have apart (k : Word) (hk : k.toNat ≤ 408) (len : Nat) (hlen : k.toNat + len ≤ 424) :
      Outside regions (q + k) len := by
    simp (disch := first | decide | omega) only [Outside, regions, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, add, sub, BitVec.reduceToNat]
    omega
  have winOut : Readable o.store q 408 := by
    apply (stp.readable.of_frame corr).sub <;> simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have retRead := (h.returnSlot.of_frame f).of_frame corr
  rw [spEq] at retRead retp
  have dstOut := dstp.of_frame corr
  have retOut := (corr.memLoad_eq (k := 64) (apart 408 (by decide) 8 (by decide))).trans retp
  have bb := res.kept 3 (by decide) cw3
  have rr := res.kept 14 (by decide) (congrArg Value.width c14)
  have spOut : o.values[4].get 64 = q := by
    rw [res.rsp]; change q - 8 + 8 = q; bv_omega
  have flagWrite : Writable Extracted.programImage o.store (q + 456) 1 :=
    dstOut.of_offsets rfl rfl (by decide)
  obtain ⟨out, tailRun, tag, store, osp, saves, controls, r9⟩ :=
    correctionReturnBlock spOut ((congrArg (Value.get 8) bb).trans c3)
      (show o.values[14].get 64 = q + 424 from congrArg (Value.get 64) (rr.trans c14)) winOut retRead
      flagWrite retOut
      (fwords.of_frame corr (by decide) (apart 120 (by decide) 32 (by decide)))
  refine ⟨out, ParseSignature.exec_call call run (by rw [res.returned]; rfl) tailRun, ⟨tag, ?_, ?_, ?_, ?_⟩, ?_, ?_, (congrArg Value.width r9).trans width⟩
  · exact osp.trans (congrArg (fun w => (⟨64,w⟩ : Value)) (by rw [spEq]; bv_omega))
  · intro i hi width
    have restore (off off' : Nat)
        (hs : (i.val,off) ∈ [(3,360),(5,400),(12,368),(13,376),(14,384),(15,392)])
        (he : (i.val,off') ∈ [(3,48),(5,8),(12,40),(13,32),(14,24),(15,16)])
        (ho : off ≤ 408) (total : off + off' = 408) : out.values[i] = a[i] := by
      have eq : q + BitVec.ofNat 64 off = p - BitVec.ofNat 64 off' := by
        rw [spEq, ← BitVec.add_sub_cancel (q + BitVec.ofNat 64 off) (BitVec.ofNat 64 off')]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add, total]
        rfl
      have retLoad := corr.memLoad_eq (k := 64) (apart (BitVec.ofNat 64 off)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) 8 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
      rw [saves i off hs, retLoad, eq, state.saved i off' he, mk_get64 _ width]
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · apply restore 360 48 <;> simp -failIfUnchanged only <;> decide
    · apply restore 400 8 <;> simp -failIfUnchanged only <;> decide
    · apply restore 368 40 <;> simp -failIfUnchanged only <;> decide
    · apply restore 376 32 <;> simp -failIfUnchanged only <;> decide
    · apply restore 384 24 <;> simp -failIfUnchanged only <;> decide
    · apply restore 392 16 <;> simp -failIfUnchanged only <;> decide
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
    have byteFrame : RamWriteFrame o.store (memStore o.store (q + 456) (1 : BitVec 8)) [⟨(q + 456).toNat,1⟩] := by
      slot_state region
    refine vw.of_frame byteFrame (by decide) ?_
    simp (disch := decide) only [Outside, List.mem_singleton, forall_eq, add, Nat.reduceDiv, Nat.reduceMul, BitVec.reduceToNat]; omega
  · rw [store, flag]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Signing.Composition.Attempt.Inverse
