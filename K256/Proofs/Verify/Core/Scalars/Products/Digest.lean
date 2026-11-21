import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.Scalars.Products.Call

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Generate.Generator.Multiply (scalarWords)
open ScalarProduct (CallRegisters callFrame inverseBound invoke outsideWrites pushNat slot slotNat)

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

private def digestProductStage (m : Ram) (sp : BitVec 64) : Ram :=
  let w0 := memLoad m (sp + 8) 64
  let w1 := memLoad m (sp + 16) 64
  let w2 := memLoad m (sp + 24) 64
  let w3 := memLoad m (sp + 32) 64
  let n := memStore m (sp + 288) w0
  let n := memStore n (sp + 296) w1
  let n := memStore n (sp + 304) w2
  let n := memStore n (sp + 312) w3
  let n := memStore n (sp + 32) w3
  let n := memStore n (sp + 24) w2
  let n := memStore n (sp + 16) w1
  let n := memStore n (sp + 8) w0
  memStore n (sp - 8) (0x105216 : BitVec 64)

set_option maxRecDepth 4096 in
private theorem digestProductSetup (b : Registers) (m : Ram) (sp : BitVec 64)
    (rsp : b[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp - 8) 328) :
    ∃ c : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1051b1, b, m⟩ =
        .call ⟨.l109f60, c, digestProductStage m sp⟩ (callFrame .l105216 0x105216) ∧
      c[4] = ⟨64, sp - 8⟩ ∧ c[6] = ⟨64, sp + 352⟩ ∧ c[7] = ⟨64, sp + 384⟩ ∧
      c[2] = ⟨64, sp + 8⟩ ∧ c[12] = ⟨64, sp + 384⟩ ∧ c[1].width = 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 5, 13, 14, 15, 22, 39, 50, 51] → c[i] = b[i] := by
  refine ⟨?c, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1051b1)
    simp (disch := store_disch) only [digestProductStage, memLoad_memStore_of_rangeApart] <;> rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem digestProductStagedWords {m : Ram} {sp : BitVec 64} {v : Vector (BitVec 64) 4}
    (words : WordsAt m (sp + 8) 64 v) :
    WordsAt (digestProductStage m sp) (sp + 8) 64 v ∧
      WordsAt (digestProductStage m sp) (sp + 288) 64 v := by
  constructor <;> intro i hi <;> rw [← words i hi]
  all_goals
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals simp (disch := store_disch) only [digestProductStage, wordAddr, Nat.reduceDiv,
    Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]

private def digestProductStageWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 8).toNat, 48⟩, ⟨(sp + 288).toNat, 32⟩]

private theorem digestProductStageFrame (e : Entry fr a p digest r s) (m : Ram) :
    RamWriteFrame m (digestProductStage m (localSp fr)) (digestProductStageWrites (localSp fr)) := by
  have low := e.low
  have room := e.stackRoom
  have push := pushNat e
  have first : InRegions (digestProductStageWrites (localSp fr)) (localSp fr - 8) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (localSp fr - 8).toNat ≤ (localSp fr - 8).toNat ∧
      (localSp fr - 8).toNat + 8 ≤ (localSp fr - 8).toNat + 48 ∧ _
    omega
  have temp (off : Nat) (fits : off ≤ 32) :
      InRegions (digestProductStageWrites (localSp fr)) (slot fr off) 8 := by
    have addr := slotNat e (off := off) (by omega)
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (localSp fr - 8).toNat ≤ (slot fr off).toNat ∧
      _ + 8 ≤ (localSp fr - 8).toNat + 48 ∧ _
    omega
  have backup (off : Nat) (fits : 288 ≤ off ∧ off ≤ 312) :
      InRegions (digestProductStageWrites (localSp fr)) (slot fr off) 8 := by
    have addr := slotNat e (off := off) (by omega)
    have start := slotNat e (off := 288) (by decide)
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change (slot fr 288).toNat ≤ (slot fr off).toNat ∧ _ + 8 ≤ (slot fr 288).toNat + 32 ∧ _
    omega
  unfold digestProductStage
  apply RamWriteFrame.memStore _ _ first
  apply RamWriteFrame.memStore _ _ (temp 8 (by decide))
  apply RamWriteFrame.memStore _ _ (temp 16 (by decide))
  apply RamWriteFrame.memStore _ _ (temp 24 (by decide))
  apply RamWriteFrame.memStore _ _ (temp 32 (by decide))
  apply RamWriteFrame.memStore _ _ (backup 312 (by decide))
  apply RamWriteFrame.memStore _ _ (backup 304 (by decide))
  apply RamWriteFrame.memStore _ _ (backup 296 (by decide))
  apply RamWriteFrame.memStore _ _ (backup 288 (by decide))
  exact .refl _ _

theorem multiplyDigest (e : Entry fr a p digest r s) {b m} (h : Inverted fr b m digest r s) :
    ∃ c n, Reaches .l1051b1 b m .l105216 c n ∧
      DigestProduct fr c n digest r s := by
  have room := e.stackRoom
  have low := e.low
  have base := e.low_toNat
  have push := pushNat e
  have backupSlot := slotNat e (off := 288) (by decide)
  have stack : Writable Extracted.programImage m (localSp fr - 8) 328 :=
    (e.stack.of_frame h.frame).sub (by omega) (by omega)
  have sp : b[4].get 64 = localSp fr := congrArg (Value.get 64) h.sp
  obtain ⟨c, call, rsp, rsi, rdi, rdx, ptr, rcx, keep⟩ := digestProductSetup b m _ sp stack
  have atoms := h.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, _, _, _, _, size, key, sig, _, _, _, _⟩ := atoms
  have regs : CallRegisters fr c 352 8 384 := by
    refine ⟨rsp, (keep 22 (by decide)).trans h.df, rsi, rdx, rdi, ?_, ?_, ?_, ?_⟩
    · intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact rcx
      · exact congrArg Value.width ((keep 3 (by decide)).trans h.dst)
      · exact congrArg Value.width ((keep 5 (by decide)).trans h.rbp)
      · exact congrArg Value.width ptr
      · exact congrArg Value.width ((keep 13 (by decide)).trans size)
      · exact congrArg Value.width ((keep 14 (by decide)).trans key)
      · exact congrArg Value.width ((keep 15 (by decide)).trans sig)
    · exact congrArg Value.width ((keep 39 (by decide)).trans h.mxcsr)
    · exact congrArg Value.width ((keep 50 (by decide)).trans h.ftw)
    · exact congrArg Value.width ((keep 51 (by decide)).trans h.fcw)
  have staged := digestProductStageFrame e m
  have within : RegionsWithin (digestProductStageWrites (localSp fr)) [fr.region] := by
    intro rg hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [digestProductStageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change fr.low.toNat ≤ (localSp fr - 8).toNat ∧
        (localSp fr - 8).toNat + 48 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
    · change fr.low.toNat ≤ (slot fr 288).toNat ∧
        (slot fr 288).toNat + 32 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
  have outsideStage {off len : Nat} (fits : off + len ≤ 488) (above : 40 ≤ off)
      (apart : off + len ≤ 288 ∨ 320 ≤ off) :
      Outside (digestProductStageWrites (localSp fr)) (slot fr off) len := by
    have addr := slotNat e (off := off) (by omega)
    refine ⟨by omega, ?_⟩
    intro rg hr
    simp only [digestProductStageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (localSp fr - 8).toNat + 48 ≤ (slot fr off).toNat
      omega
    · change (slot fr off).toNat + len ≤ (slot fr 288).toNat ∨
        (slot fr 288).toNat + 32 ≤ (slot fr off).toNat
      omega
  have frame := h.frame.trans staged within
  have tag : memLoad (digestProductStage m (localSp fr)) (localSp fr - 8) 64 = 0x105216 := by
    unfold digestProductStage
    exact memLoad_memStore_same _ _ _ rfl (by decide)
  have wx := h.digestAt.of_frame staged (by decide)
    (outsideStage (off := 352) (len := 32) (by decide) (by decide) (by decide))
  obtain ⟨wy, backup⟩ := digestProductStagedWords h.inverseAt
  have order : 0 < domain.n := Nat.zero_lt_of_lt e.bounds.2.1
  obtain ⟨d, n, run, post⟩ := invoke e call regs frame tag (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.mod_lt _ order) (inverseBound s) wx wy
  have keep' (i : Fin 53) (hi : i.val ∈ [3, 5, 13, 14, 15, 22, 39, 50, 51]) :
      d[i] = b[i] :=
    (post.keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans (keep i hi)
  have saved {off : Nat} (lower : 8 ≤ off) (upper : off ≤ 40) :
      memLoad n (fr.rsp - BitVec.ofNat 64 off) 64 =
        memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
    have addr : fr.rsp - BitVec.ofNat 64 off = slot fr (488 - off) := by
      unfold slot localSp
      rw [← BitVec.ofNat_sub_ofNat_of_le 488 off (by omega) (by omega)]
      bv_omega
    rw [addr]
    exact (post.frame.memLoad_eq (outsideWrites e (len := 8) (by omega) (by decide) (Or.inr (by omega)))).trans
      (staged.memLoad_eq (outsideStage (len := 8) (by omega) (by omega) (Or.inr (by omega))))
  have rStaged := h.rAt.of_frame staged (by decide)
    (outsideStage (off := 256) (len := 32) (by decide) (by decide) (by decide))
  refine ⟨d, n, run, ?_⟩
  exact {
    sp := post.sp
    dst := (keep' 3 (by decide)).trans h.dst
    rbp := (keep' 5 (by decide)).trans h.rbp
    df := (keep' 22 (by decide)).trans h.df
    mxcsr := (keep' 39 (by decide)).trans h.mxcsr
    ftw := (keep' 50 (by decide)).trans h.ftw
    fcw := (keep' 51 (by decide)).trans h.fcw
    rbx := (saved (off := 40) (by decide) (by decide)).trans h.rbx
    r12 := (saved (off := 32) (by decide) (by decide)).trans h.r12
    r13 := (saved (off := 24) (by decide) (by decide)).trans h.r13
    r14 := (saved (off := 16) (by decide) (by decide)).trans h.r14
    r15 := (saved (off := 8) (by decide) (by decide)).trans h.r15
    frame := post.whole
    key := (keep' 14 (by decide)).trans key
    sig := (keep' 15 (by decide)).trans sig
    uPtr := (post.keep 12 (by decide)).trans ptr
    uAt := post.words
    inverseAt := backup.of_frame post.frame (by decide)
      (outsideWrites e (dst := 384) (off := 288) (len := 32) (by decide) (by decide) (by decide))
    rAt := rStaged.of_frame post.frame (by decide)
      (outsideWrites e (dst := 384) (off := 256) (len := 32) (by decide) (by decide) (by decide))
    sizeReg := (keep' 13 (by decide)).trans size
    widths := post.widths }

end K256.Proofs.Verify.Core
