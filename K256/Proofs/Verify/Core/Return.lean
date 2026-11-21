import K256.Proofs.Verify.Core.Epilogue

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

structure Result (fr : Activation) (out : Output Value Ram Reg.count) (accepts : Bool) : Prop where
  tag : out.tag = some ⟨64, fr.ret⟩
  atoms : Atom.All Extracted.programImage out.values out.store (Fn104f20.doneAt fr)
  writes : RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 16⟩]
  status : memLoad out.store fr.rdi 64 = if accepts then 0 else 1
  null : accepts = false → memLoad out.store (fr.rdi + 8) 64 = 0

inductive Exit where
  | highS | mismatch | verified

def Exit.label : Exit → Label
  | .highS => .l1050ad
  | .mismatch => .l10536f
  | .verified => .l10536b

def Exit.accepts : Exit → Bool
  | .verified => true
  | _ => false

private def resultMemory (fr : Activation) (m : Ram) (ok : Bool) : Ram :=
  if ok then memStore m fr.rdi (0 : BitVec 64)
  else memStore (memStore m (fr.rdi + 8) (0 : BitVec 64)) fr.rdi (1 : BitVec 64)

private theorem resultMemory_post {fr : Activation} {a b : Registers} {p : Curve.Point}
    {digest : ByteArray} {r s : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Phase fr b m)
    (ok : Bool) :
    RamWriteFrame fr.original (resultMemory fr m ok) (writes fr) ∧
      memLoad (resultMemory fr m ok) fr.rdi 64 = (if ok then 0 else 1) ∧
      (ok = false → memLoad (resultMemory fr m ok) (fr.rdi + 8) 64 = 0) := by
  have wf := (RamWriteFrame.refl fr.original (writes fr)).trans h.frame (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, .head _, Nat.le_refl _, Nat.le_refl _⟩)
  have hi := e.low
  have dst : fr.rdi.toNat = fr.rsp.toNat + 168 := by
    rw [e.dst, BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rsp.toNat + 168 < 2^64; omega)]
    rfl
  have dst8 : (fr.rdi + 8).toNat = fr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rdi.toNat + 8 < 2^64; omega)]
    rfl
  have inside₀ : InRegions (writes fr) fr.rdi 8 :=
    ⟨_, .tail _ (.head _), Nat.le_refl _, by change fr.rdi.toNat + 8 ≤ fr.rdi.toNat + 16; omega, by omega⟩
  have inside₈ : InRegions (writes fr) (fr.rdi + 8) 8 :=
    ⟨_, .tail _ (.head _), by change fr.rdi.toNat ≤ _; omega,
      by change _ ≤ fr.rdi.toNat + 16; omega, by omega⟩
  cases ok with
  | true =>
    exact ⟨wf.memStore _ inside₀, memLoad_memStore_same _ _ _ (by decide) (by decide), by intro h; contradiction⟩
  | false =>
    refine ⟨(wf.memStore _ inside₈).memStore _ inside₀,
      memLoad_memStore_same _ _ _ (by decide) (by decide), fun _ => ?_⟩
    simp (disch := store_disch) only [resultMemory, Bool.false_eq_true, ↓reduceIte,
      memLoad_memStore_same, memLoad_memStore_of_rangeApart]

private theorem resultMemory_slot (fr : Activation) (m : Ram) (ok : Bool)
    (dst : fr.rdi = fr.rsp + 168) (off : Nat) (slot : off ∈ [8, 16, 24, 32, 40]) :
    memLoad (resultMemory fr m ok) (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
  have nullAddr : fr.rsp + 168 + 8 = fr.rsp + 176 := by bv_omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at slot
  rcases slot with rfl | rfl | rfl | rfl | rfl <;> cases ok <;>
    simp (disch := store_disch) only [resultMemory, Bool.false_eq_true, ↓reduceIte, dst, nullAddr,
      memLoad_memStore_of_rangeApart]

private theorem included : ∀ x ∈ LIR.fnCode, x ∈ Extracted.programImage := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨LIR.textSection, by simp [Extracted.programSections, LIR.textSection], ?_⟩
  simpa only [LIR.fnCode, LIR.sections, ImageSections.toCodeMap, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] using hx

private theorem exitBlocks {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Phase fr b m) (exit : Exit) :
    ∃ c, Reaches exit.label b m .l10537f c (resultMemory fr m exit.accepts) ∧
      Saved fr c (resultMemory fr m exit.accepts) := by
  have area := e.upper.of_frame h.frame
  have writable : Writable Extracted.programImage m fr.rdi 16 :=
    area.of_offsets e.dst rfl (by decide)
  have di : b[3].get 64 = fr.rdi := congrArg (Value.get 64) h.dst
  have saved {c : Registers}
      (eq : ∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 22, 39, 50, 51] → c[i] = b[i]) :
      Saved fr c (resultMemory fr m exit.accepts) := by
    refine ⟨(eq 4 (by decide)).trans h.sp, (eq 3 (by decide)).trans h.dst,
      (eq 5 (by decide)).trans h.rbp, (eq 22 (by decide)).trans h.df,
      (eq 39 (by decide)).trans h.mxcsr, (eq 50 (by decide)).trans h.ftw,
      (eq 51 (by decide)).trans h.fcw, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | exact (resultMemory_slot fr m exit.accepts e.dst 40 (by decide)).trans h.rbx
      | exact (resultMemory_slot fr m exit.accepts e.dst 32 (by decide)).trans h.r12
      | exact (resultMemory_slot fr m exit.accepts e.dst 24 (by decide)).trans h.r13
      | exact (resultMemory_slot fr m exit.accepts e.dst 16 (by decide)).trans h.r14
      | exact (resultMemory_slot fr m exit.accepts e.dst 8 (by decide)).trans h.r15
  cases exit <;> simp only [Exit.label, Exit.accepts, resultMemory, Bool.false_eq_true, ↓reduceIte]
  case highS =>
    refine ⟨?regs, Semantics.Reaches.single ?step, saved ?keep⟩
    case step =>
      change program.step _ _ = _
      unfold Program.step
      cfg_eval
      simp only [di]
      simp (disch := slot_guard using (fun x hx => included x (code_l1050ad x hx))) only [ite_eq_left]
      rfl
    case keep =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case mismatch =>
    refine ⟨?regsMismatch, Star.step (b := ⟨⟨.l10537c, ?midMismatch, memStore m (fr.rdi + 8) (0 : BitVec 64)⟩, []⟩)
      ?firstMismatch (Semantics.Reaches.single ?lastMismatch), saved ?keepMismatch⟩
    case firstMismatch =>
      change program.step _ _ = _
      unfold Program.step
      cfg_eval
      simp only [di]
      simp (disch := slot_guard using (fun x hx => included x (code_l10536f x hx))) only [ite_eq_left]
      rfl
    case lastMismatch =>
      change program.step _ _ = _
      unfold Program.step
      cfg_eval
      simp only [di]
      simp (disch := slot_guard using (fun x hx => included x (code_l10537c x hx))) only [ite_eq_left]
      rfl
    case keepMismatch =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case verified =>
    refine ⟨?regsVerified, Star.step (b := ⟨⟨.l10537c, ?midVerified, m⟩, []⟩) ?firstVerified (Semantics.Reaches.single ?lastVerified), saved ?keepVerified⟩
    case firstVerified =>
      change program.step _ _ = _
      unfold Program.step
      cfg_eval
      rfl
    case lastVerified =>
      change program.step _ _ = _
      unfold Program.step
      cfg_eval
      simp only [di]
      simp (disch := slot_guard using (fun x hx => included x (code_l10537c x hx))) only [ite_eq_left]
      rfl
    case keepVerified =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem returnPath {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m : Ram} (e : Entry fr a p digest r s) (exit : Exit) (h : Phase fr b m) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨exit.label, b, m⟩, []⟩ out ∧
      Result fr out exit.accepts := by
  obtain ⟨c, path, saved⟩ := exitBlocks e h exit
  obtain ⟨wf, status, null⟩ := resultMemory_post e h exit.accepts
  obtain ⟨out, run, tag, mem, done⟩ := epilogue e saved wf
  exact ⟨out, Program.Exec.of_sem (path.exec run.sem),
    ⟨tag, mem ▸ done, mem ▸ wf, mem ▸ status, mem ▸ null⟩⟩

end K256.Proofs.Verify.Core
