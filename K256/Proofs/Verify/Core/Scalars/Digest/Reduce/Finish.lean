import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.State
import K256.Proofs.Verify.Core.Serializer.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core.Reduce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply ParseSignature

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem finish {fr : Activation} {a : Registers} {m : Ram} {w : Vector (BitVec 64) 4} (choose : Bool)
    (h : Live fr w a m) (flag : a[0] = ⟨64,if choose then 1 else 0⟩)
    (dst : Writable Extracted.programImage fr.original fr.rdi 32) (apart : Outside [callStack fr] fr.rdi 32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a05f,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn109f80.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, buffer fr.rdi 32] ∧
      WordsAt out.store fr.rdi 64 (if choose then difference w else w) ∧ ArgumentWidths out.values := by
  have atoms := h.atoms
  simp only [Fn109f80.frameAt, Fn109f80.frameAtG11, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, mx, ftw, fcw, di, bx, r12, r13, r14, r15, bp, read, ret, low, win, room, _, _⟩ := atoms
  have stack : a[4].get 64 = fr.rsp - 88 := congrArg (Value.get 64) rsp
  have writable := dst.of_frame h.frame
  let byte := (a[0].get 64).setWidth 8
  let marked := memStore m (fr.rsp - 81) byte
  let vals := if choose then difference w else w
  let result := memStore (memStore (memStore (memStore marked fr.rdi vals[0])
    (fr.rdi + 8) vals[1]) (fr.rdi + 16) vals[2]) (fr.rdi + 24) vals[3]
  have zf : (!(testFlags (byte &&& byte)).ZF.getD false) = choose := by
    cases choose <;> rw [show byte = _ from congrArg (fun v : Value => (v.get 64).setWidth 8) flag] <;> rfl
  have select (i : Nat) (hi : i < 4) :
      (if choose then (difference w)[i] else w[i]) = vals[i] := by cases choose <;> rfl
  have markedEq : memStore m (fr.rsp - 81) ((a[0].get 64).setWidth 8) = marked := rfl
  have mark : memLoad marked (fr.rsp - 81) 8 = byte :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have markRead (off : Nat) (small : off ≤ 72) :
      memLoad marked (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
    dsimp only [marked]
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj
    change i < 1 at hi
    change j < 8 at hj
    bv_omega
  have l0 : memLoad marked (fr.rsp - 64) 64 = (difference w)[0] := by
    refine (markRead 64 (by decide)).trans ?_
    change memLoad m (fr.rsp - 64) 64 = (difference w)[0]
    simpa only [sp, Lift.reduceAddOffset] using h.lowDiff
  have l2 : memLoad marked (fr.rsp - 72) 64 = (difference w)[2] := by
    refine (markRead 72 (by decide)).trans ?_
    change memLoad m (fr.rsp - 72) 64 = (difference w)[2]
    simpa only [sp, Lift.reduceAddOffset] using h.highDiff
  have dest : memLoad marked (fr.rsp - 56) 64 = fr.rdi := (markRead 56 (by decide)).trans di
  have dstLow := apart.1
  have dframe : RamWriteFrame marked result [buffer fr.rdi 32] :=
    Serializer.storeWords_frame vals (.refl _ _) ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, dstLow⟩
  have saved (off : Nat) (small : off ≤ 48) :
      memLoad result (fr.rsp - BitVec.ofNat 64 off) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
    rw [dframe.memLoad_eq, markRead off (by omega)]
    have ds := apart.2 _ List.mem_cons_self
    change fr.rdi.toNat + 32 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at ds
    have bound := read.low
    have addr : (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by bv_omega
    refine ⟨?_, ?_⟩
    · rw [addr]; change fr.rsp.toNat - off + 8 ≤ 2^64; omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change _ + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ _
      rw [addr]; omega
  have back : memLoad result fr.rsp 64 = fr.ret := by
    have z := saved 0 (by decide)
    simp only [BitVec.sub_zero] at z
    exact z.trans ret
  have popbx : memLoad result (fr.rsp - 48) 64 = fr.rbx := (saved 48 (by decide)).trans bx
  have popr12 : memLoad result (fr.rsp - 40) 64 = fr.r12 := (saved 40 (by decide)).trans r12
  have popr13 : memLoad result (fr.rsp - 32) 64 = fr.r13 := (saved 32 (by decide)).trans r13
  have popr14 : memLoad result (fr.rsp - 24) 64 = fr.r14 := (saved 24 (by decide)).trans r14
  have popr15 : memLoad result (fr.rsp - 16) 64 = fr.r15 := (saved 16 (by decide)).trans r15
  have popbp : memLoad result (fr.rsp - 8) 64 = fr.rbp := (saved 8 (by decide)).trans bp
  have resultEq : memStore (memStore (memStore (memStore marked fr.rdi vals[0])
    (fr.rdi + 8) vals[1]) (fr.rdi + 16) vals[2]) (fr.rdi + 24) vals[3] = result := rfl
  have inc : ∀ x ∈ codeRange 0x10a05f bytes_l10a05f, x ∈ Extracted.programImage :=
    fun x hx => Common.fnCode_subset_programImage x (code_l10a05f x hx)
  have stackM : Writable Extracted.programImage marked (fr.rsp - 97) 97 := win.memStore (fr.rsp - 81) byte
  have destM : Writable Extracted.programImage marked fr.rdi 32 := writable.memStore (fr.rsp - 81) byte
  have stackR := stackM.of_frame dframe
  have retR := (read.memStore (fr.rsp - 81) byte).of_frame dframe
  refine ⟨?_, .done ?run, ?tag, ?done_, ?frame, ?words, ?widths⟩
  case run =>
    unfold Program.step
    cfg_eval [stack]
    simp only [markedEq, mark, zf, l0, l2, dest, h.r14, h.r12, h.rbp, h.r15, h.r13, h.rbx,
      Value.get_mk, select 0 (by decide), select 1 (by decide), select 2 (by decide), select 3 (by decide),
      resultEq, back, low, and_true, popbx, popr12, popr13, popr14, popr15, popbp]
    simp (disch := slot_guard using inc) only [ite_eq_left]
    rfl
  case tag => rfl
  case done_ => exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ftw, fcw, trivial⟩
  case words => exact Serializer.storeWords_wordsAt marked fr.rdi vals dstLow
  case widths =>
    intro ⟨i, hi⟩ ha
    have hw := h.widths ⟨i, hi⟩ ha
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact hw
  case frame =>
    have initial : RamWriteFrame fr.original m [fr.region, buffer fr.rdi 32] :=
      (RamWriteFrame.refl _ _).trans h.frame (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
    have sf : RamWriteFrame fr.original marked [fr.region, buffer fr.rdi 32] := by
      apply initial.memStore
      refine ⟨_, List.mem_cons_self, ?_⟩
      change fr.low.toNat ≤ (fr.rsp - 81).toNat ∧ (fr.rsp - 81).toNat + 1 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ _
      bv_omega
    exact sf.trans dframe (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩)

end K256.Proofs.Verify.Core.Reduce
