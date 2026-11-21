import K256.Proofs.Signing.Affine.State
import K256.Proofs.Generate.Generator.Affine.Normalize.Saved
import K256.Proofs.Generate.Generator.Affine.NormalizeCall
import K256.Proofs.Sec1.Serialize.Normalize.Correct
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Affine

open K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

private theorem pushGuard {m : Ram} {addr pc : Word} {len : Nat}
    (w : Writable Extracted.programImage m addr 8)
    (within : (pc - 0x10ece0).toNat + len ≤ bytes_l10ece0.length) :
    StoreOk Extracted.programImage m addr 8 pc len := by
  have h := ParseSignature.storeOk_of_codeRange w
    (fun v hv => Common.fnCode_subset_programImage v (code_l10ece0 v hv)) within
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show 0x10ece0 + (pc - 0x10ece0) = pc by bv_omega] at h

private theorem normalizeEntry {a : Registers} {m : Ram} {fr : Activation}
    (s : CallState .l10fe50 fr a m) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10ece0, a, m⟩ =
      .call ⟨.l114930, b, normalizeMemory fr m⟩ normalizeReturn ∧
      b[4] = ⟨64, fr.rsp - 240⟩ ∧ b[6] = ⟨64, fr.rsi + 80⟩ ∧
      b[7] = ⟨64, fr.rsp - 144⟩ ∧ b[3] = ⟨64, fr.rdi⟩ ∧ b[14] = ⟨64, fr.rsi⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,15,22,39,50,51] → b[i] = a[i]) := by
  obtain ⟨sp, _, _, _, bx, bp, si, di, _, _, r12, r13, r14, r15, _, _, _, _, _, _, win, _⟩ := s.atoms
  change a[4] = ⟨64, fr.rsp⟩ at sp
  change a[3] = ⟨64, fr.rbx⟩ at bx
  change a[5] = ⟨64, fr.rbp⟩ at bp
  change a[6] = ⟨64, fr.rsi⟩ at si
  change a[7] = ⟨64, fr.rdi⟩ at di
  change a[12] = ⟨64, fr.r12⟩ at r12
  change a[13] = ⟨64, fr.r13⟩ at r13
  change a[14] = ⟨64, fr.r14⟩ at r14
  change a[15] = ⟨64, fr.r15⟩ at r15
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  refine ⟨?regs, ?run, ?post⟩
  case run =>
    cfg_eval
    simp only [sp, bx, bp, si, di, r12, r13, r14, r15, Value.get_mk]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_
             apply pushGuard _ (by decide)
             repeat' apply Writable.memStore
             apply win.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
    · rfl
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact bp.symm | exact r12.symm | exact r13.symm | exact r15.symm

private theorem normalizePath {a b : Registers} {m : Ram} {fr : Activation}
    {out : Output Value Ram Reg.count}
    (call : program.runBlock (dialect Extracted.programImage) ⟨.l10ece0, a, m⟩ =
      .call ⟨.l114930, b, normalizeMemory fr m⟩ normalizeReturn)
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l114930, b, normalizeMemory fr m⟩, []⟩ out)
    (tag : out.tag = some ⟨64, 0x10ed05⟩) :
    Reaches .l10fe50 a m .l10ed05 out.values out.store := by
  refine .step (b := ⟨⟨.l10ece0, a, m⟩, []⟩) ?_ ?_
  · have jump : program.runBlock (dialect Extracted.programImage) ⟨.l10fe50, a, m⟩ =
        .jump ⟨.l10ece0, a, m⟩ := by
      cfg_eval
      congr 2
      apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
        fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
      intro i
      finite_cases i <;> rfl
    simp only [Program.sem, Program.step, jump, Transfer.next]
  · refine .step (b := ⟨⟨.l114930, b, normalizeMemory fr m⟩, [normalizeReturn]⟩) ?_ ?_
    · simp only [Program.sem, Program.step, call, Transfer.next]
    · exact ParseSignature.exec_reaches_resume run normalizeReturn [] (by rw [tag]; rfl)

theorem normalizeZ {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10fe50 fr a m)
    (h : Coordinates m fr.rsi x y z) :
    ∃ b m', Reaches .l10fe50 a m .l10ed05 b m' ∧ CallState .l10ed05 fr b m' ∧
      Coordinates m' fr.rsi x y z ∧ Normalized fr m' z := by
  obtain ⟨_, df, _, _, _, bp, _, _, _, _, r12, r13, _, r15, mx, ft, fc, stackRead, ret,
    retLow, win, space, align, gotRead, got, slotRead, slot, gotApart, _⟩ := s.atoms
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at space
  change fr.rsp.toNat % 16 = 8 at align
  have room : 976 ≤ fr.rsp.toNat := by omega
  have high := s.source.low
  have srcAbove := s.srcAbove
  have offset (k : Word) (hk : k.toNat ≤ 976) := sub_toNat room k hk
  have off144 : (fr.rsp - 144).toNat = fr.rsp.toNat - 144 := offset 144 (by decide)
  have off240 : (fr.rsp - 240).toNat = fr.rsp.toNat - 240 := offset 240 (by decide)
  have off353 : (fr.rsp - 240 - 113).toNat = fr.rsp.toNat - 353 := by
    rw [BitVec.sub_sub]; exact offset 353 (by decide)
  have off976 : (fr.rsp - 976).toNat = fr.rsp.toNat - 976 := offset 976 (by decide)
  have srcZ : (fr.rsi + 80).toNat = fr.rsi.toNat + 80 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change _ + 80 < _; omega)]
    rfl
  have above : Outside [scratch fr.rsp] fr.rsi 120 := by
    simp only [Outside, scratch, List.mem_singleton, forall_eq, off976]; omega
  obtain ⟨b, call, bs, bz, bd, bx, b14, preserve⟩ := normalizeEntry s
  have saved := normalizeMemory_frame (fr := fr) m room
  obtain ⟨s48, s40, s32, s24, s16, s8, returnZ⟩ := normalizeMemory_saved fr m
  have coord := h.of_frame saved above
  obtain ⟨_, _, v, _, _, words, _, _, rz⟩ := coord
  have regWidth (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :
      b[i] = ⟨64, b[i].get 64⟩ := by
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      apply (show ∀ {v : Value} {w : Word}, v = ⟨64, w⟩ → v = ⟨64, v.get 64⟩ from
        fun e => e ▸ rfl)
    · exact bx
    · exact (preserve 5 (by decide)).trans bp
    · exact (preserve 12 (by decide)).trans r12
    · exact (preserve 13 (by decide)).trans r13
    · exact b14
    · exact (preserve 15 (by decide)).trans r15
  have childWin := win.of_frame saved
  have dest : Writable Extracted.programImage (normalizeMemory fr m) (fr.rsp - 144) 40 := by slot_state region
  have child : Writable Extracted.programImage (normalizeMemory fr m) (fr.rsp - 240 - 113) 121 := by slot_state region
  have sourceWindow := s.source.of_frame saved
  have source : Readable (normalizeMemory fr m) (fr.rsi + 80) 40 := by slot_state region
  obtain ⟨out, run, tag, sp, kept, body, result⟩ := normalizeCall bs bz bd
    ((preserve 22 (by decide)).trans df) regWidth child source dest
    (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)
    returnZ (by decide) words
  have wrote := saved.trans body (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl <;> refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
      dsimp only [scratch] <;> omega)
  have sameSaved (k : Word) (hk : k.toNat ≤ 48) :
      memLoad out.store (fr.rsp - k) 64 = memLoad (normalizeMemory fr m) (fr.rsp - k) 64 := by
    apply body.memLoad_eq
    have subK := offset k (by omega)
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Nat.reduceDiv, off144, off353, subK]
    omega
  have retEq : memLoad out.store fr.rsp 64 = memLoad m fr.rsp 64 := by
    apply wrote.memLoad_eq
    simp only [Outside, List.mem_singleton, forall_eq, scratch, off976, Nat.reduceDiv]; omega
  have codeSlot (p : Word) (pLow : 0x203de0 ≤ p.toNat) (pHigh : p.toNat + 8 ≤ 0x203e28) :
      memLoad out.store p 64 = memLoad m p 64 := by
    apply wrote.memLoad_eq
    change 0x2041f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0 at gotApart
    simp only [Outside, scratch, List.mem_singleton, forall_eq, Nat.reduceDiv, off976]; omega
  have full : RamWriteFrame fr.original out.store (writes fr) := s.frame.trans wrote (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨fr.region, List.mem_cons_self, by change fr.low.toNat ≤ (fr.rsp - 976).toNat; omega,
      by change (fr.rsp - 976).toNat + 976 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat); omega⟩)
  have keep (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,15,22,39,50,51]) : out.values[i] = a[i] :=
    (kept i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with h|h|h|h|h|h|h|h <;> simp [h])).trans (preserve i hi)
  refine ⟨_, _, normalizePath call run tag, ?_, h.of_frame wrote above, _,
    result, Sec1.Serialize.Normalize.normalize_correct _ _ _ rz (by decide)⟩
  refine ⟨?_, scratch_image win wrote s.image, s.source.of_frame wrote, s.dest.of_frame wrote,
    s.srcAbove, s.dstAbove, full⟩
  rw [show fr.rsp - 240 + 8 = fr.rsp - 232 by bv_omega] at sp
  exact ⟨sp,
    (keep 22 (by decide)).trans df, (kept 3 (by decide)).trans bx, (keep 5 (by decide)).trans bp,
    (keep 12 (by decide)).trans r12, (keep 13 (by decide)).trans r13,
    (kept 14 (by decide)).trans b14, (keep 15 (by decide)).trans r15,
    (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc,
    (sameSaved 48 (by decide)).trans s48, (sameSaved 40 (by decide)).trans s40,
    (sameSaved 32 (by decide)).trans s32, (sameSaved 24 (by decide)).trans s24,
    (sameSaved 16 (by decide)).trans s16, (sameSaved 8 (by decide)).trans s8,
    Readable.of_frame stackRead wrote, retEq.trans ret, retLow, win.of_frame wrote, space, align,
    Readable.of_frame gotRead wrote, (codeSlot _ (by decide) (by decide)).trans got,
    Readable.of_frame slotRead wrote, (codeSlot _ (by decide) (by decide)).trans slot, gotApart, trivial⟩

end K256.Proofs.Signing.Affine
