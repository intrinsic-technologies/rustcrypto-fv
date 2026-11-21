import K256.Proofs.Common.Invert.LinearShift
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
import K256.Proofs.Generate.Generator.Affine.Memory

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

private def shiftResume : StackFrame Value Label signature Reg.count :=
  ⟨.l1088a6, #v[], rfl, some ⟨64, 0x1088a6⟩⟩

private def shiftPrefixMemory (a : Registers) (m : Ram) (sp : Word) : Ram :=
  let m := memStore m (sp - 8) (a[5].get 64)
  let m := memStore m (sp - 16) (a[14].get 64)
  let m := memStore m (sp - 24) (a[3].get 64)
  memStore m (sp - 80) (0x1088a6 : Word)

private structure ShiftChild (a b : Registers) (sp dst : Word) (s : BitVec 32) : Prop where
  rsp : b[4] = ⟨64, sp - 80⟩
  rdi : b[7] = ⟨64, sp - 72⟩
  rbx : b[3] = ⟨64, dst⟩
  rbp : b[5] = ⟨64, s.setWidth 64⟩
  left : b[6] = a[6]
  right : b[2] = a[2]
  coeffLeft : b[1] = a[1]
  coeffRight : b[8] = a[8]
  saved : ∀ i : Fin Reg.count, i.val ∈ [12, 13, 15, 22, 39, 50, 51] → b[i] = a[i]

set_option maxHeartbeats 650000 in
private theorem shiftPrefix {a : Registers} {m : Ram} {sp dst ret : Word} {s : BitVec 32}
    (fr : CalleeFrame a m sp dst ret 208 33) (hs : a[9].get 32 = s) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l108890, a, m⟩ =
      .call ⟨.l1084e0, b, shiftPrefixMemory a m sp⟩ shiftResume ∧ ShiftChild a b sp dst s := by
  have rsp : a[4] = ⟨64, sp⟩ := fr.rsp
  have shiftBits : (a[9].get 64).setWidth 32 = s := by
    change (a[9].bits.setWidth 64).setWidth 32 = s
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact hs
  have rdi : a[7] = ⟨64, dst⟩ := fr.rdi
  have stack : Writable Extracted.programImage m (sp - 208) 208 := fr.stack
  refine ⟨?regs, ?run, ?post⟩
  case run =>
    unfold shiftPrefixMemory shiftResume
    cfg_eval
    simp only [rsp, rdi, shiftBits, Value.get_mk]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l108890)
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def shiftArgs (a : Registers) (sp dst : Word) (s : BitVec 32) : Prop :=
  a[4] = ⟨64, sp - 72⟩ ∧ a[3] = ⟨64, dst⟩ ∧ a[5] = ⟨64, s.setWidth 64⟩

private def shiftPreserved (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 12, 13, 15, 22, 39, 50, 51] → b[i] = a[i]

set_option maxHeartbeats 650000 in
private theorem shiftBranches {a : Registers} {m : Ram} {sp dst : Word} {s : BitVec 32}
    (h : shiftArgs a sp dst s) (h0 : 0 < s.toNat) (h64 : s.toNat < 64) :
    ∃ b, Reaches .l1088a6 a m .l1088c3 b m ∧ shiftPreserved a b ∧
      b[0] = ⟨64, (64 - s).setWidth 64⟩ := by
  obtain ⟨_, _, bp⟩ := h
  have bp' : (a[5].get 64).setWidth 32 = s := by
    rw [bp]
    change (s.setWidth 64).setWidth 32 = s
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  have c₁ : (64 - s : BitVec 32).toNat < 64 := by bv_omega
  have c₃ : s ≠ 0 := by bv_omega
  have j1 : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l1088a6, a, m⟩ =
      .jump ⟨.l1088b6, b, m⟩ ∧ shiftPreserved a b ∧
      b[0] = ⟨64, (64 - s).setWidth 64⟩ := by
    refine ⟨?args1, ?run1, ?keep1, ?ax1⟩
    case run1 =>
      cfg_eval [bp']
      simp only [cmpSpec, subSpec, BitVec.reduceToNat, c₁, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    case keep1 =>
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case ax1 => rfl
  obtain ⟨b, j1, keep1, ax1⟩ := j1
  have bp2 : (b[5].get 64).setWidth 32 = s := by
    have hk : b[5] = a[5] := keep1 5 (by decide)
    rwa [hk]
  have j2 : ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l1088b6, b, m⟩ =
      .jump ⟨.l1088bb, c, m⟩ ∧ shiftPreserved b c ∧ c[0] = b[0] := by
    refine ⟨?args2, ?run2, ?keep2, ?ax2⟩
    case run2 =>
      cfg_eval [bp2]
      simp only [cmpSpec, subSpec, BitVec.reduceToNat, h64, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    case keep2 =>
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case ax2 => rfl
  obtain ⟨c, j2, keep2, ax2⟩ := j2
  have bp3 : (c[5].get 64).setWidth 32 = s := by
    have hk : c[5] = b[5] := keep2 5 (by decide)
    rwa [hk]
  have j3 : ∃ d, program.runBlock (dialect Extracted.programImage) ⟨.l1088bb, c, m⟩ =
      .jump ⟨.l1088c3, d, m⟩ ∧ shiftPreserved c d ∧ d[0] = c[0] := by
    refine ⟨?args3, ?run3, ?keep3, ?ax3⟩
    case run3 =>
      cfg_eval [bp3, BitVec.and_self]
      simp only [testFlags, Option.getD_some, beq_iff_eq, c₃, ↓reduceIte]
      rfl
    case keep3 =>
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case ax3 => rfl
  obtain ⟨d, j3, keep3, ax3⟩ := j3
  refine ⟨d, .step (b := ⟨⟨.l1088b6, b, m⟩, []⟩) ?_
    (.step (b := ⟨⟨.l1088bb, c, m⟩, []⟩) ?_ (.step (b := ⟨⟨.l1088c3, d, m⟩, []⟩) ?_ (.refl _))), ?_, ax3.trans (ax2.trans ax1)⟩
  · simp only [Program.sem, Program.step, j1, Transfer.next]
  · simp only [Program.sem, Program.step, j2, Transfer.next]
  · simp only [Program.sem, Program.step, j3, Transfer.next]
  · intro i hi
    exact (keep3 i hi).trans ((keep2 i hi).trans (keep1 i hi))

open K256.Proofs.Common.Invert.LinearShift K256.Proofs.Common.Invert.LinearCombination

private def shiftOutput (m : Ram) (dst : Word) (w : Vector Word 4) (sgn : BitVec 8) : Ram :=
  let m := memStore m dst w[0]
  let m := memStore m (dst + 8) w[1]
  let m := memStore m (dst + 16) w[2]
  let m := memStore m (dst + 24) w[3]
  memStore m (dst + 32) sgn

set_option maxHeartbeats 2500000 in
private theorem shiftTail {a : Registers} {m : Ram} {sp dst ret : Word} {s : BitVec 32}
    {w : Vector Word 5} {sgn : BitVec 8}
    (rsp : a[4] = ⟨64, sp - 72⟩) (rbx : a[3] = ⟨64, dst⟩)
    (rbp : a[5] = ⟨64, s.setWidth 64⟩) (rax : a[0] = ⟨64, (64 - s).setWidth 64⟩)
    (h0 : 0 < s.toNat) (h64 : s.toNat < 64)
    (slots : Readable m (sp - 72) 41) (save : Readable m (sp - 24) 24)
    (returnSlot : Readable m sp 8) (returnEq : memLoad m sp 64 = ret) (retLow : ret.toNat < 2^32)
    (outW : Writable Extracted.programImage m dst 33)
    (room : 208 ≤ sp.toNat)
    (apart : dst.toNat + 33 ≤ sp.toNat - 208 ∨ sp.toNat + 8 ≤ dst.toNat)
    (words : WordsAt m (sp - 72) 64 w) (sign : memLoad m (sp - 72 + 40) 8 = sgn) :
    ∃ out, CalleeExec .l1088c3 a m out ∧ out.tag = some ⟨64, ret⟩ ∧
      out.store = shiftOutput m dst (shiftedWords w s.toNat) sgn ∧
      RamWriteFrame m out.store [⟨dst.toNat, 33⟩] ∧
      out.values[4] = ⟨64, sp + 8⟩ ∧
      out.values[3] = ⟨64, memLoad m (sp - 24) 64⟩ ∧
      out.values[14] = ⟨64, memLoad m (sp - 16) 64⟩ ∧
      out.values[5] = ⟨64, memLoad m (sp - 8) 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [12, 13, 15, 22, 39, 50, 51] → out.values[i] = a[i]) := by
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  simp only [wordAddr, Nat.reduceMul, Nat.reduceDiv, BitVec.add_zero, Lift.reduceAddOffset] at w0 w1 w2 w3 w4 sign
  have shiftComplement : (64 - s : BitVec 32).toNat = 64 - s.toNat := by bv_omega
  have hs64 : shiftCount 64 (s.setWidth 8) = s.toNat := by
    simp only [shiftCount, ↓reduceIte, BitVec.toNat_setWidth]
    omega
  have hc64 : shiftCount 64 ((64 - s : BitVec 32).setWidth 8) = 64 - s.toNat := by
    simp only [shiftCount, ↓reduceIte, BitVec.toNat_setWidth, shiftComplement]
    omega
  have rightCount : shiftCount 64 ((s.setWidth 64).setWidth 32 |>.setWidth 8) = s.toNat := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), hs64]
  have leftCount : shiftCount 64 (((64 - s : BitVec 32).setWidth 64).setWidth 32 |>.setWidth 8) =
      64 - s.toNat := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), hc64]
  have dstLow := outW.readable.low
  have outputFrame : RamWriteFrame m (shiftOutput m dst (shiftedWords w s.toNat) sgn)
      [⟨dst.toNat, 33⟩] := by
    unfold shiftOutput
    first
    | slot_state region
    | have within (off : Nat) (n : Nat) (h : off + n ≤ 33) :
          InRegions [⟨dst.toNat, 33⟩] (dst + BitVec.ofNat 64 off) n := by
        refine ⟨_, List.mem_cons_self, ?_⟩
        have hOff : off < 2^64 := by omega
        have hAdd : dst.toNat + off < 2^64 := by omega
        simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hOff,
          Nat.mod_eq_of_lt hAdd]
        omega
      repeat' (apply RamWriteFrame.memStore _ _ (within _ _ (by decide)))
      exact (RamWriteFrame.refl _ _).memStore _
        (by
          have h := within 0 8 (by decide)
          change InRegions _ (dst + (0 : Word)) 8 at h
          rwa [show dst + (0 : Word) = dst by bv_omega] at h)
  have noOutput (k : Word) (hk : k.toNat ≤ 24) : Outside [⟨dst.toNat, 33⟩] (sp - k) 8 := by
    have rlow := returnSlot.low
    have eq : (sp - k).toNat = sp.toNat - k.toNat := by bv_omega
    simp only [Outside, List.mem_singleton, forall_eq, eq]
    omega
  have savedLoad (k : Word) (hk : k.toNat ≤ 24) :
      memLoad (shiftOutput m dst (shiftedWords w s.toNat) sgn) (sp - k) 64 =
        memLoad m (sp - k) 64 :=
    outputFrame.memLoad_eq (noOutput k hk)
  have returnLoad : memLoad (shiftOutput m dst (shiftedWords w s.toNat) sgn) sp 64 = ret :=
    (outputFrame.memLoad_eq (by
      have h := noOutput 0 (by decide)
      change Outside _ (sp - (0 : Word)) 8 at h
      rw [show sp - (0 : Word) = sp by bv_omega] at h
      exact h)).trans returnEq
  refine ⟨?out, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rsp, rbx, rbp, rax, Value.get_mk, Lift.reduceAddOffset,
      w0, w1, w2, w3, w4, sign, rightCount, leftCount]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; first
      | slot_guard using code_l1088c3_1
      | exact ⟨by slot_guard using code_l1088c3_1, by change (memLoad (shiftOutput m dst (shiftedWords w s.toNat) sgn) sp 64).toNat < 2^32; rwa [returnLoad]⟩)
    rfl
  case post =>
    refine ⟨?_, rfl, outputFrame, rfl, ?_, ?_, ?_, ?_⟩
    · exact congrArg (fun w : Word => some (⟨64, w⟩ : Value)) returnLoad
    · exact congrArg (Value.mk 64) (savedLoad 24 (by decide))
    · exact congrArg (Value.mk 64) (savedLoad 16 (by decide))
    · exact congrArg (Value.mk 64) (savedLoad 8 (by decide))
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


private theorem shiftOutput_words (m : Ram) (dst : Word) (w : Vector Word 4) (sgn : BitVec 8) :
    WordsAt (shiftOutput m dst w sgn) dst 64 w ∧
      memLoad (shiftOutput m dst w sgn) (dst + 32) 8 = sgn := by
  constructor
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp (disch := first | store_disch | decide) only [shiftOutput, wordAddr, Nat.reduceDiv,
        Nat.reduceMul, BitVec.add_zero, memLoad_memStore_of_rangeApart, memLoad_memStore_same] <;>
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

set_option exponentiation.threshold 512 in
set_option maxHeartbeats 1200000 in
theorem linearShift {a : Registers} {m : Ram} {sp dst ret : Word} {x y q : Int} {u v : Word} {shift : Nat}
    (fr : CalleeFrame a m sp dst ret 208 33)
    (args : LinearArgs a m sp dst 208 33 x y u v)
    (hs : a[9].get 32 = BitVec.ofNat 32 shift) (pos : 0 < shift) (hshift : shift ≤ 62)
    (exactShift : (2 : Int)^shift * q = x * u.toInt + y * v.toInt) (fits : q.natAbs < 2^256) :
    ∃ out, CalleeExec .l108890 a m out ∧ CalleeResult a m sp dst ret 208 33 out ∧
      signedAt out.store dst q := by
  obtain ⟨b, call, child⟩ := shiftPrefix fr hs
  let m₁ := shiftPrefixMemory a m sp
  let stackRegion : MemoryRegion := ⟨(sp - 208).toNat, 208⟩
  have room := fr.depthBound
  have high := fr.returnSlot.low
  have dstHigh := fr.output.readable.low
  have win : Writable Extracted.programImage m (sp - 208) 208 := fr.stack
  have outW : Writable Extracted.programImage m dst 33 := fr.output
  have subNat (k : Word) (hk : k.toNat ≤ 208) : (sp - k).toNat = sp.toNat - k.toNat := by
    bv_omega
  have stackBase : (sp - (208 : Word)).toNat = sp.toNat - 208 := subNat 208 (by decide)
  have frame₁ : RamWriteFrame m m₁ [stackRegion] := by
    unfold m₁ shiftPrefixMemory stackRegion
    first
    | slot_state region
    | have within (k : Word) (lo : 8 ≤ k.toNat) (hi : k.toNat ≤ 208) :
          InRegions [⟨(sp - 208).toNat, 208⟩] (sp - k) 8 := by
        refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [InRegion, subNat k hi, stackBase]
        omega
      repeat' (apply RamWriteFrame.memStore _ _ (within _ (by decide) (by decide)))
      exact RamWriteFrame.refl _ _
  have childImage := stackImage win frame₁ fr.image
  have childSp : (sp - 80).toNat = sp.toNat - 80 := subNat 80 (by decide)
  have childDst : (sp - 72).toNat = sp.toNat - 72 := subNat 72 (by decide)
  have childStack : (sp - 80 - BitVec.ofNat 64 112).toNat = sp.toNat - 192 := by
    rw [show sp - 80 - BitVec.ofNat 64 112 = sp - 192 by bv_omega]
    exact subNat 192 (by decide)
  have win₁ := win.of_frame frame₁
  have childRet : Readable m₁ (sp - 80) 8 := by slot_state region
  have childOut : Writable Extracted.programImage m₁ (sp - 72) 41 := by slot_state region
  have childWin : Writable Extracted.programImage m₁ (sp - 80 - BitVec.ofNat 64 112) 112 := by
    rw [show sp - 80 - BitVec.ofNat 64 112 = sp - 192 by bv_omega]
    slot_state region
  have childFrame : CalleeFrame b m₁ (sp - 80) (sp - 72) 0x1088a6 112 41 :=
    ⟨child.rsp, child.rdi, (child.saved 22 (by decide)).trans fr.df, childImage, by omega,
      by have := fr.aligned; omega, childRet,
      by unfold m₁ shiftPrefixMemory; exact memLoad_memStore_same _ _ _ (by decide) (by decide),
      by decide, childWin, childOut, Or.inr (by omega)⟩
  have source (p : Word) (k : Int) (h : SignedSource m sp dst p 208 33 k) :
      SignedSource m₁ (sp - 80) (sp - 72) p 112 41 k := by
    have srcLow := h.read.low
    have srcApart := h.stackApart
    have outside : Outside [stackRegion] p 33 := by
      simp only [Outside, List.mem_singleton, forall_eq, stackRegion, stackBase]
      omega
    obtain ⟨w, n, hw, hn, hk⟩ := h.signed
    have byteOutside : Outside [stackRegion] (p + 32) 1 := by
      apply outside_subregion outside <;> bv_omega
    exact ⟨h.read.of_frame frame₁, by omega, by omega, w, n,
      hw.of_frame frame₁ (by decide) (outside_subregion outside (by omega) (by omega)),
      (frame₁.memLoad_eq byteOutside).trans hn, hk⟩
  have childArgs : LinearArgs b m₁ (sp - 80) (sp - 72) 112 41 x y u v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [child.left]; exact source _ _ args.left
    · rw [child.right]; exact source _ _ args.right
    · rw [child.coeffLeft]; exact args.coeffLeft
    · rw [child.coeffRight]; exact args.coeffRight
  obtain ⟨mid, run, post, mag⟩ := linearCombination childFrame childArgs
  have frame₂ : RamWriteFrame m mid.store [stackRegion] := by
    refine frame₁.trans post.frame ?_
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    all_goals refine ⟨stackRegion, List.mem_cons_self, ?_, ?_⟩
    all_goals simp only [stackRegion, stackBase, childStack, childDst]
    all_goals omega
  have saveEq (k : Word) (lo : 8 ≤ k.toNat) (hi : k.toNat ≤ 24) :
      memLoad mid.store (sp - k) 64 = memLoad m₁ (sp - k) 64 := by
    apply post.frame.memLoad_eq
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      childStack, childDst, subNat k (by omega), Nat.reduceDiv]
    omega
  have retEq : memLoad mid.store sp 64 = ret := by
    rw [frame₂.memLoad_eq, fr.retAddr]
    simp only [Outside, List.mem_singleton, forall_eq, stackRegion, stackBase, Nat.reduceDiv]
    omega
  have rbpWidth : (b[5]).width = 64 := congrArg Value.width child.rbp
  have rbxWidth : (b[3]).width = 64 := congrArg Value.width child.rbx
  have sNat : (BitVec.ofNat 32 shift).toNat = shift := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have shiftReady : shiftArgs mid.values sp dst (BitVec.ofNat 32 shift) := by
    refine ⟨?_, (post.kept 3 (by decide) rbxWidth).trans child.rbx,
      (post.kept 5 (by decide) rbpWidth).trans child.rbp⟩
    rw [post.rsp, show sp - (80 : Word) + 8 = sp - 72 by bv_omega]
  obtain ⟨c, arrive, kept, ax⟩ := shiftBranches shiftReady (by rw [sNat]; exact pos) (by rw [sNat]; omega)
  obtain ⟨w, n, hw, hn, hm⟩ := mag
  have midOut := childOut.readable.of_frame post.frame
  have midWin := win.of_frame frame₂
  have save : Readable mid.store (sp - 24) 24 := by slot_state region
  obtain ⟨out, tail, tag, store, outFrame, stack, bx, r14, bp, keepTail⟩ := shiftTail
    ((kept 4 (by decide)).trans shiftReady.1)
    ((kept 3 (by decide)).trans shiftReady.2.1) ((kept 5 (by decide)).trans shiftReady.2.2)
    ax (by rwa [sNat]) (by rw [sNat]; omega) midOut save (fr.returnSlot.of_frame frame₂) retEq fr.retLow
    (outW.of_frame frame₂) room fr.apart hw hn
  have hm' : (2 : Int)^shift * q = if n then -(wideValue w : Int) else (wideValue w : Int) := by
    rw [exactShift, hm]
    have pack : (wideValue w : Int) =
        (((w[4].toNat * 2^64 + w[3].toNat) * 2^64 + w[2].toNat) * 2^64 +
          w[1].toNat) * 2^64 + w[0].toNat := by
      simp only [wideValue, packFive, Vector.getElem_map, Int.natCast_add, Int.natCast_mul,
        Int.natCast_pow]
      omega
    rw [pack]
  have hshifted := signedShift w n shift (by omega) q hm' fits
  have result : signedAt out.store dst q := by
    rw [store, sNat]
    let limbs := shiftedWords w shift
    have pack : packFour (limbs.map BitVec.toNat) = value limbs := by
      simp only [packFour, Vector.getElem_map, value]
      omega
    rw [show shiftedWords w shift = limbs from rfl] at hshifted
    rw [pack] at hshifted
    exact ⟨limbs, n, (shiftOutput_words _ _ _ _).1, (shiftOutput_words _ _ _ _).2, hshifted⟩
  have frame : RamWriteFrame m out.store [stackRegion, ⟨dst.toNat, 33⟩] := by
    have widened : RamWriteFrame m mid.store [stackRegion, ⟨dst.toNat, 33⟩] :=
      (RamWriteFrame.refl m _).trans frame₂ (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨stackRegion, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
    exact widened.trans outFrame (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨dst.toNat, 33⟩, by simp, Nat.le_refl _, Nat.le_refl _⟩)
  have ofWidth (v : Value) (h : v.width = 64) : (⟨64, v.get 64⟩ : Value) = v := by
    cases v with
    | mk n bits => cases h; rfl
  have savedWords : memLoad m₁ (sp - 24) 64 = a[3].get 64 ∧
      memLoad m₁ (sp - 16) 64 = a[14].get 64 ∧ memLoad m₁ (sp - 8) 64 = a[5].get 64 := by
    simp (disch := store_disch) only [m₁, shiftPrefixMemory, memLoad_memStore_of_rangeApart,
      memLoad_memStore_same, and_self]
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [12, 13, 15]) (hw : a[i].width = 64) :
      out.values[i] = a[i] := by
    have hm : i.val ∈ [12, 13, 15, 22, 39, 50, 51] :=
      (show [12, 13, 15] ⊆ [12, 13, 15, 22, 39, 50, 51] by decide) hi
    have hl : i.val ∈ [3, 4, 5, 12, 13, 15, 22, 39, 50, 51] :=
      (show [12, 13, 15] ⊆ [3, 4, 5, 12, 13, 15, 22, 39, 50, 51] by decide) hi
    have hc : i.val ∈ [3, 5, 12, 13, 14, 15] :=
      (show [12, 13, 15] ⊆ [3, 5, 12, 13, 14, 15] by decide) hi
    have hb := child.saved i hm
    exact (keepTail i hm).trans ((kept i hl).trans
      ((post.kept i hc ((congrArg Value.width hb).trans hw)).trans hb))
  refine ⟨out, ?_, ⟨tag, stack, ?_, ?_, frame⟩, result⟩
  · apply ParseSignature.exec_call call run (by rw [post.returned]; rfl)
    exact Program.Exec.of_sem (arrive.exec tail.sem)
  · intro ⟨i, hi⟩ mem width
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
    · change out.values[3] = a[3]
      rw [bx, saveEq 24 (by decide) (by decide), savedWords.1]
      exact ofWidth _ width
    · change out.values[5] = a[5]
      rw [bp, saveEq 8 (by decide) (by decide), savedWords.2.2]
      exact ofWidth _ width
    · exact preserved _ (show 12 ∈ [12, 13, 15] by decide) width
    · exact preserved _ (show 13 ∈ [12, 13, 15] by decide) width
    · change out.values[14] = a[14]
      rw [r14, saveEq 16 (by decide) (by decide), savedWords.2.1]
      exact ofWidth _ width
    · exact preserved _ (show 15 ∈ [12, 13, 15] by decide) width
  · intro i hi
    have sm : i.val ∈ [12, 13, 15, 22, 39, 50, 51] :=
      (show [22, 39, 50, 51] ⊆ [12, 13, 15, 22, 39, 50, 51] by decide) hi
    have pm : i.val ∈ [3, 4, 5, 12, 13, 15, 22, 39, 50, 51] :=
      (show [22, 39, 50, 51] ⊆ [3, 4, 5, 12, 13, 15, 22, 39, 50, 51] by decide) hi
    exact (keepTail i sm).trans ((kept i pm).trans ((post.controls i hi).trans (child.saved i sm)))

end K256.Proofs.Generate.Generator.Affine.Invert.Core
