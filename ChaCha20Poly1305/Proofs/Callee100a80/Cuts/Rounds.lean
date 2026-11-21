import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.ChaCha20.Refinement
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Dec.Generated.M.Triple
import X86Proofs.Instructions.Branch.Triple
namespace ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.ChaCha20

structure RFrame (stack : BitVec 64) (s : RamState) : Prop where
  rsp : rspOf s = stack
  writable : MemWritable s stack 0x80
  code : ∀ i < 0x80, ¬ InProgram (stack + BitVec.ofNat 64 i)

theorem w_slice {s : RamState} {a : BitVec 64} {n : Nat} (h : MemWritable s a n) (off len : Nat)
    (hn : off + len ≤ n) : MemWritable s (a + BitVec.ofNat 64 off) len := by
  have hl := h.low
  have ha : (a + BitVec.ofNat 64 off).toNat = a.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, fun i hi => ?_, ?_⟩
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.mem _ (by omega)
  · rw [ha]; exact h.tables.sub (by omega) (by omega)

theorem textBytes_size_eq : Extracted.textBytes.size = 11759 := by decide

theorem ap_code {stack q : BitVec 64} (hc : ∀ i < 0x80, ¬ InProgram (stack + BitVec.ofNat 64 i))
    (off len : Nat) (hn : off + len ≤ 0x80) (ilen : Nat) (hq : 0x100000 ≤ q.toNat)
    (hq2 : q.toNat + ilen ≤ 0x1014bc) : RangeApart (stack + BitVec.ofNat 64 off) len q ilen := by
  intro i hi j hj he
  apply hc (off + i) (by omega)
  have hk : q + BitVec.ofNat 64 j =
      Extracted.textAddress + BitVec.ofNat 64 (q.toNat - 0x100000 + j) := by
    apply BitVec.eq_of_toNat_eq
    have := q.isLt
    have ht : Extracted.textAddress.toNat = 0x100000 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_add, ht, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h1 : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
    have h2 : (q.toNat - 0x100000 + j) % 2 ^ 64 = q.toNat - 0x100000 + j :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    congr 1
    omega
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, he, hk]
  exact text_address_in_program _ (by rw [textBytes_size_eq]; omega)

theorem ne_boundary {boundary : ReturnBoundary}
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) {p : BitVec 64}
    (h1 : 0x100a80 ≤ p.toNat) (h2 : p.toNat < 0x1014bc) : p ≠ boundary.rip := by
  rintro rfl; omega

macro "rr_frame " hP:ident : tactic => `(tactic| (
  have hF := ($hP).2
  have hS := hF.rsp
  try x86_norm at hS
  try x86_norm
  try simp only [hS]
  first
  | exact (w_slice hF.writable _ _ (by decide)).readable
  | exact w_slice hF.writable _ _ (by decide)
  | exact ap_code hF.code _ _ (by decide) _ (by decide) (by decide)))

open Lean Meta Elab Tactic in
elab "rr_sub" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let (small, large) ← g.withContext do
    forallBoundedTelescope ty (some 2) fun xs body => do
      unless xs.size == 2 do throwError "expected code containment"
      let range? (e : Expr) : Option Expr :=
        if e.isAppOfArity ``List.Mem 3 then some e.appArg!
        else if e.isAppOfArity ``Membership.mem 5 then some e.getAppArgs[3]!
        else none
      let some small := range? (← inferType xs[1]!) | throwError "expected code membership"
      let some large := range? body | throwError "expected code membership"
      return (small, large)
  unless small.isAppOfArity ``codeRange 2 && large.isAppOfArity ``codeRange 2 do
    throwError "expected code ranges"
  let q := small.getAppArgs[0]!
  let p := large.getAppArgs[0]!
  let some ⟨_, qv⟩ ← getBitVecValue? q | throwError "expected a literal instruction address"
  let some ⟨_, pv⟩ ← getBitVecValue? p | throwError "expected a literal block address"
  let off := (qv.toNat + 2 ^ 64 - pv.toNat) % 2 ^ 64
  let offExpr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit off)
  let addr ← g.withContext do mkAppM ``HAdd.hAdd #[p, offExpr]
  let small' := mkApp2 (mkConst ``codeRange) addr small.appArg!
  let ty' := ty.replace fun e ↦ if e == small then some small' else none
  replaceMainGoal [← g.change ty']
  evalTactic (← `(tactic| x86_sub))

macro "rr_bd" : tactic => `(tactic| (
  intro _ _; exact ne_boundary (by assumption) (by x86_norm) (by x86_norm)))

macro "rr_begin " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => first | x86_sub | rr_sub
  case pre =>
    intro s hP
    first
    | exact hP.1
    | exact ⟨hP.1⟩
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
         (by x86_addr_obs) ?_
       rr_frame hP)
    | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
         (by x86_addr_obs) ?_ ?_ <;> rr_frame hP)
  case av =>
    intro s hP
    first
    | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
    | (x86_avoid
       all_goals rr_frame hP)
  case boundary => rr_bd
  case' k => skip))

macro "rr_then " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => first | x86_sub | rr_sub
  case full =>
    first
    | (intro s _
       apply Effect.Local.full
       repeat' first
         | (solve | x86_local)
         | apply Effect.Local.seq
       done)
    | x86_full
  case mid =>
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · first
      | exact hH.rip_of (by first | rfl | x86_norm)
      | exact ⟨hH.rip_of (by first | rfl | x86_norm)⟩
      | (refine LoadPre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs) ?_
         rr_frame hP)
      | (refine StorePre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs)
           ?_ ?_ <;> rr_frame hP)
    · first
      | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
      | (x86_avoid
         all_goals rr_frame hP)
  case boundary => rr_bd
  case' k => skip))

macro "rr_finish" : tactic => `(tactic| (intro h; exact h))

inductive Loc where
  | reg (r : BitVec 5)
  | slot (off : BitVec 64)

def Loc.op (stack : BitVec 64) : Loc → Operand 32
  | .reg r => .reg r
  | .slot off => .mem (stack + off)

def cut (stack : BitVec 64) (layout : List (Fin 16 × Loc)) (x : Vector UInt32 16) : List Write :=
  layout.map fun e => ⟨e.2.op stack, x[e.1].toBitVec⟩

def mainBase : List (Fin 16 × Loc) :=
  [(0, .reg 3), (1, .reg 13), (2, .reg 12), (3, .reg 10), (4, .reg 5), (5, .reg 1), (6, .reg 2),
    (7, .reg 11), (8, .slot 4), (9, .reg 0), (10, .reg 6), (11, .reg 8), (12, .reg 9),
    (13, .reg 7), (14, .reg 14), (15, .reg 15)]

def mainAlias : List (Fin 16 × Loc) := mainBase ++ [(9, .slot 8)]

def tailBase : List (Fin 16 × Loc) :=
  [(0, .slot 8), (1, .reg 13), (2, .reg 0), (3, .reg 7), (4, .reg 9), (5, .reg 5), (6, .reg 15),
    (7, .reg 6), (8, .slot 4), (9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1),
    (13, .reg 2), (14, .reg 8), (15, .reg 11)]

def tailB : List (Fin 16 × Loc) :=
  [(0, .reg 3), (1, .reg 13), (2, .reg 0), (3, .reg 7), (4, .reg 9), (5, .reg 5), (6, .reg 15),
    (7, .reg 6), (8, .slot 4), (9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1),
    (13, .reg 2), (14, .reg 8), (15, .reg 11)]

def tailC : List (Fin 16 × Loc) := tailB ++ [(9, .slot 0x14)]

def tailD : List (Fin 16 × Loc) := tailBase ++ [(9, .slot 0x14)]

def regScratch : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip]

def mainQR (stack : BitVec 64) : List Component :=
  regScratch ++ [.mem (stack + 4) 4, .mem (stack + 8) 4, .mem (stack + 0x14) 4]

def mainScratch (stack : BitVec 64) : List Component :=
  mainQR stack ++ [.mem (stack + 0x78) 8]

def tailQR (stack : BitVec 64) : List Component :=
  regScratch ++ [.mem (stack + 4) 4, .mem (stack + 8) 4, .mem (stack + 0x14) 4,
    .mem (stack + 0x78) 4]

def tailScratch (stack : BitVec 64) : List Component :=
  tailQR stack ++ [.mem (stack + 0x58) 8]

def Good (stack : BitVec 64) (cs : List Component) : Prop :=
  Component.reg 4 ∉ cs ∧ ∀ c ∈ cs, ∀ x, c.Covers x → ∃ i < 0x80, x = stack + BitVec.ofNat 64 i

theorem mem_good {stack x o : BitVec 64} {n : Nat} (h : o.toNat + n ≤ 0x80)
    (hc : (Component.mem (stack + o) n).Covers x) : ∃ i < 0x80, x = stack + BitVec.ofNat 64 i := by
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨o.toNat + i, by omega, ?_⟩
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

macro "good_tac" : tactic => `(tactic| (
  refine ⟨by simp [mainScratch, mainQR, tailScratch, tailQR, regScratch], ?_⟩
  simp only [mainScratch, mainQR, tailScratch, tailQR, regScratch, List.cons_append,
    List.nil_append, List.forall_mem_cons, List.forall_mem_nil, and_true]
  repeat' apply And.intro
  all_goals (intro x hx; first | exact hx.elim | exact mem_good (by decide) hx | simp at hx)))

theorem mainQR_good (stack : BitVec 64) : Good stack (mainQR stack) := by good_tac

theorem mainScratch_good (stack : BitVec 64) : Good stack (mainScratch stack) := by good_tac

theorem tailQR_good (stack : BitVec 64) : Good stack (tailQR stack) := by good_tac

theorem tailScratch_good (stack : BitVec 64) : Good stack (tailScratch stack) := by good_tac

theorem RFrame.of_agrees {stack : BitVec 64} {cs : List Component} {s t : RamState}
    (h : RFrame stack s) (hg : Good stack cs) (ha : AgreesExcept cs s t) : RFrame stack t :=
  ⟨(ha.read hg.1).trans h.rsp,
    ⟨h.writable.low, fun i hi => ha.grow _ (h.writable.mem i hi), h.writable.tables⟩, h.code⟩

theorem RFrame.codeIn {stack : BitVec 64} {cs : List Component} {s t : RamState}
    (h : RFrame stack s) (hg : Good stack cs) (ha : AgreesExcept cs s t)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept ha _ hc
  intro x hx c hc' hcov
  obtain ⟨i, hi, he⟩ := hg.2 c hc' x.1 hcov
  exact h.code i hi (he ▸ inProgram_of_mem hx)

def Seg [Bindings] (boundary : ReturnBoundary) (p q : BitVec 64)
    (scratch : BitVec 64 → List Component) (pre post : List (Fin 16 × Loc))
    (f : Vector UInt32 16 → Vector UInt32 16) : Prop :=
  ∀ stack x s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = p → RFrame stack s →
    Write.AllHold s (cut stack pre x) →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = q ∧ RFrame stack t ∧ Write.AllHold t (cut stack post (f x)) ∧
      AgreesExcept (scratch stack) s t

theorem Seg.seq [Bindings] {boundary : ReturnBoundary} {p q r : BitVec 64}
    {scratch : BitVec 64 → List Component} {l₁ l₂ l₃ : List (Fin 16 × Loc)}
    {f g : Vector UInt32 16 → Vector UInt32 16}
    (h₁ : Seg boundary p q scratch l₁ l₂ f) (h₂ : Seg boundary q r scratch l₂ l₃ g) :
    Seg boundary p r scratch l₁ l₃ (fun x => g (f x)) := by
  intro stack x s hr hc hp hf hw
  obtain ⟨n, t, ha, hr', hc', hq, hf', hw', hag⟩ := h₁ stack x s hr hc hp hf hw
  obtain ⟨m, u, ha', hr'', hc'', hq', hf'', hw'', hag'⟩ := h₂ stack (f x) t hr' hc' hq hf' hw'
  exact ⟨n + m, u, ha.trans ha', hr'', hc'', hq', hf'', hw'',
    (hag.trans hag').mono (by simp only [List.mem_append, or_self]; exact fun _ h => h)⟩

theorem Seg.of_block [Bindings] {boundary : ReturnBoundary} {p q : BitVec 64} {bytes : List UInt8}
    {eff : RamState → Effect} {scratch : BitVec 64 → List Component}
    {pre post : List (Fin 16 × Loc)} {f : Vector UInt32 16 → Vector UInt32 16}
    (hBlock : ∀ stack, AdvancesBlock boundary (fun s => s.RIP = p ∧ RFrame stack s)
      (codeRange p bytes) eff)
    (hText : ∀ s, CodeIn Extracted.programImage s → CodeIn (codeRange p bytes) s)
    (hGood : ∀ stack, Good stack (scratch stack))
    (hRip : ∀ s t, (eff s).Holds s t → t.RIP = q)
    (hAgree : ∀ stack s t, rspOf s = stack → (eff s).Holds s t →
      AgreesExcept (scratch stack) s t)
    (hWords : ∀ stack x s t, rspOf s = stack → Write.AllHold s (cut stack pre x) →
      (eff s).Holds s t → Write.AllHold t (cut stack post (f x))) :
    Seg boundary p q scratch pre post f := by
  intro stack x s hr hc hp hf hw
  obtain ⟨fuel, t, ha, hr', _, he⟩ := hBlock stack s hr (hText s hc) ⟨hp, hf⟩
  have hag := hAgree stack s t hf.rsp he
  exact ⟨fuel, t, ha, hr', hf.codeIn (hGood stack) hag hc, hRip s t he,
    hf.of_agrees (hGood stack) hag, hWords stack x s t hf.rsp hw he, hag⟩

def main0Bytes : List UInt8 :=
  [0x89, 0x74, 0x24, 0x14, 0x1, 0xeb, 0x41, 0x31, 0xd9, 0x41, 0xc1, 0xc1, 0x10, 0x8b, 0x74, 0x24, 0x4, 0x44, 0x1, 0xce, 0x31, 0xf5, 0xc1, 0xc5, 0xc, 0x1, 0xeb, 0x41, 0x31, 0xd9, 0x41, 0xc1, 0xc1, 0x8, 0x44, 0x1, 0xce, 0x89, 0x74, 0x24, 0x4, 0x31, 0xf5, 0x8b, 0x74, 0x24, 0x14, 0xc1, 0xc5, 0x7]

def main0Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movM32R32LowEffect 0x100cd0 6 (.sib 4 none 0 (.d8 0x14))) (addR32R32Effect 0x100cd4 2 3 5)) (xorR32R32Effect 0x100cd6 3 9 3)) (rolR32Effect 0x100cd9 4 9 16)) (movR32M32LowEffect 0x100cdd 6 (.sib 4 none 0 (.d8 0x4)))) (addR32R32Effect 0x100ce1 3 6 9)) (xorR32R32Effect 0x100ce4 2 5 6)) (rolR32Effect 0x100ce6 3 5 12)) (addR32R32Effect 0x100ce9 2 3 5)) (xorR32R32Effect 0x100ceb 3 9 3)) (rolR32Effect 0x100cee 4 9 8)) (addR32R32Effect 0x100cf2 3 6 9)) (movM32R32LowEffect 0x100cf5 6 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x100cf9 2 5 6)) (movR32M32LowEffect 0x100cfb 6 (.sib 4 none 0 (.d8 0x14)))) (rolR32Effect 0x100cff 3 5 7))

theorem main0Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100cd0 ∧ RFrame stack s)
      (codeRange 0x100cd0 main0Bytes) main0Effect := by
  unfold main0Bytes
  rr_begin (mov_m32_r32_low_effect_step 0x100cd0 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100cd4 0xeb (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100cd6 0x41 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100cd9 0x41 0xc1 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100cdd 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100ce1 0x44 0xce (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100ce4 0xf5 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100ce6 0xc5 0xc (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100ce9 0xeb (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100ceb 0x41 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100cee 0x41 0xc1 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100cf2 0x44 0xce (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x100cf5 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100cf9 0xf5 (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100cfb 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100cff 0xc5 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main0Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainBase x))
    (he : (main0Effect s).Holds s t) :
    Write.AllHold t (cut stack mainBase (qroundRol x 0 4 8 12)) := by
  have hfull : ∀ w ∈ (main0Effect s).writes, w.Full := by x86_norm [main0Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainBase, List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main0Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main0Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100cd0 0x100d02 mainQR mainBase mainBase
      (fun x => qroundRol x 0 4 8 12) := by
  apply Seg.of_block (main0Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xcd0 50 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xcd0 50 = main0Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xcd0 = 0x100cd0 from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main0Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main0Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main0Words hs hw he

def main1Bytes : List UInt8 :=
  [0x41, 0x1, 0xcd, 0x44, 0x31, 0xef, 0xc1, 0xc7, 0x10, 0x1, 0xf8, 0x31, 0xc1, 0xc1, 0xc1, 0xc, 0x41, 0x1, 0xcd, 0x44, 0x31, 0xef, 0xc1, 0xc7, 0x8, 0x1, 0xf8, 0x89, 0x44, 0x24, 0x8, 0x31, 0xc1, 0xc1, 0xc1, 0x7]

def main1Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100d02 3 13 1) (xorR32R32Effect 0x100d05 3 7 13)) (rolR32Effect 0x100d08 3 7 16)) (addR32R32Effect 0x100d0b 2 0 7)) (xorR32R32Effect 0x100d0d 2 1 0)) (rolR32Effect 0x100d0f 3 1 12)) (addR32R32Effect 0x100d12 3 13 1)) (xorR32R32Effect 0x100d15 3 7 13)) (rolR32Effect 0x100d18 3 7 8)) (addR32R32Effect 0x100d1b 2 0 7)) (movM32R32LowEffect 0x100d1d 0 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect 0x100d21 2 1 0)) (rolR32Effect 0x100d23 3 1 7))

theorem main1Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100d02 ∧ RFrame stack s)
      (codeRange 0x100d02 main1Bytes) main1Effect := by
  unfold main1Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x100d02 0x41 0xcd (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d05 0x44 0xef (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d08 0xc7 0x10 (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100d0b 0xf8 (by decide))
  rr_then (xor_r32_r32_effect_step 0x100d0d 0xc1 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d0f 0xc1 0xc (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d12 0x41 0xcd (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d15 0x44 0xef (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d18 0xc7 0x8 (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100d1b 0xf8 (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x100d1d 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100d21 0xc1 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d23 0xc1 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main1Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainBase x))
    (he : (main1Effect s).Holds s t) :
    Write.AllHold t (cut stack mainAlias (qroundRol x 1 5 9 13)) := by
  have hfull : ∀ w ∈ (main1Effect s).writes, w.Full := by x86_norm [main1Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainBase, mainAlias, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main1Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main1Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100d02 0x100d26 mainQR mainBase mainAlias
      (fun x => qroundRol x 1 5 9 13) := by
  apply Seg.of_block (main1Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xd02 36 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xd02 36 = main1Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xd02 = 0x100d02 from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main1Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main1Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main1Words hs hw he

def main2Bytes : List UInt8 :=
  [0x41, 0x1, 0xd4, 0x45, 0x31, 0xe6, 0x41, 0xc1, 0xc6, 0x10, 0x44, 0x1, 0xf6, 0x31, 0xf2, 0xc1, 0xc2, 0xc, 0x41, 0x1, 0xd4, 0x45, 0x31, 0xe6, 0x41, 0xc1, 0xc6, 0x8, 0x44, 0x1, 0xf6, 0x31, 0xf2, 0xc1, 0xc2, 0x7]

def main2Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100d26 3 12 2) (xorR32R32Effect 0x100d29 3 14 12)) (rolR32Effect 0x100d2c 4 14 16)) (addR32R32Effect 0x100d30 3 6 14)) (xorR32R32Effect 0x100d33 2 2 6)) (rolR32Effect 0x100d35 3 2 12)) (addR32R32Effect 0x100d38 3 12 2)) (xorR32R32Effect 0x100d3b 3 14 12)) (rolR32Effect 0x100d3e 4 14 8)) (addR32R32Effect 0x100d42 3 6 14)) (xorR32R32Effect 0x100d45 2 2 6)) (rolR32Effect 0x100d47 3 2 7))

theorem main2Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100d26 ∧ RFrame stack s)
      (codeRange 0x100d26 main2Bytes) main2Effect := by
  unfold main2Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x100d26 0x41 0xd4 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d29 0x45 0xe6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d2c 0x41 0xc6 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d30 0x44 0xf6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100d33 0xf2 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d35 0xc2 0xc (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d38 0x41 0xd4 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d3b 0x45 0xe6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d3e 0x41 0xc6 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d42 0x44 0xf6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100d45 0xf2 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d47 0xc2 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main2Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainAlias x))
    (he : (main2Effect s).Holds s t) :
    Write.AllHold t (cut stack mainAlias (qroundRol x 2 6 10 14)) := by
  have hfull : ∀ w ∈ (main2Effect s).writes, w.Full := by x86_norm [main2Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainAlias, mainBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main2Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main2Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100d26 0x100d4a mainQR mainAlias mainAlias
      (fun x => qroundRol x 2 6 10 14) := by
  apply Seg.of_block (main2Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xd26 36 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xd26 36 = main2Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xd26 = 0x100d26 from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main2Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main2Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main2Words hs hw he

def main3Bytes : List UInt8 :=
  [0x45, 0x1, 0xda, 0x45, 0x31, 0xd7, 0x41, 0xc1, 0xc7, 0x10, 0x45, 0x1, 0xf8, 0x45, 0x31, 0xc3, 0x41, 0xc1, 0xc3, 0xc, 0x45, 0x1, 0xda, 0x45, 0x31, 0xd7, 0x41, 0xc1, 0xc7, 0x8, 0x45, 0x1, 0xf8, 0x45, 0x31, 0xc3, 0x41, 0xc1, 0xc3, 0x7]

def main3Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100d4a 3 10 11) (xorR32R32Effect 0x100d4d 3 15 10)) (rolR32Effect 0x100d50 4 15 16)) (addR32R32Effect 0x100d54 3 8 15)) (xorR32R32Effect 0x100d57 3 11 8)) (rolR32Effect 0x100d5a 4 11 12)) (addR32R32Effect 0x100d5e 3 10 11)) (xorR32R32Effect 0x100d61 3 15 10)) (rolR32Effect 0x100d64 4 15 8)) (addR32R32Effect 0x100d68 3 8 15)) (xorR32R32Effect 0x100d6b 3 11 8)) (rolR32Effect 0x100d6e 4 11 7))

theorem main3Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100d4a ∧ RFrame stack s)
      (codeRange 0x100d4a main3Bytes) main3Effect := by
  unfold main3Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x100d4a 0x45 0xda (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d4d 0x45 0xd7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d50 0x41 0xc7 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d54 0x45 0xf8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d57 0x45 0xc3 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d5a 0x41 0xc3 0xc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d5e 0x45 0xda (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d61 0x45 0xd7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d64 0x41 0xc7 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d68 0x45 0xf8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d6b 0x45 0xc3 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d6e 0x41 0xc3 0x7 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main3Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainAlias x))
    (he : (main3Effect s).Holds s t) :
    Write.AllHold t (cut stack mainAlias (qroundRol x 3 7 11 15)) := by
  have hfull : ∀ w ∈ (main3Effect s).writes, w.Full := by x86_norm [main3Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainAlias, mainBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main3Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main3Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100d4a 0x100d72 mainQR mainAlias mainAlias
      (fun x => qroundRol x 3 7 11 15) := by
  apply Seg.of_block (main3Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xd4a 40 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xd4a 40 = main3Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xd4a = 0x100d4a from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main3Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main3Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main3Words hs hw he

def main4Bytes : List UInt8 :=
  [0x1, 0xcb, 0x41, 0x31, 0xdf, 0x41, 0xc1, 0xc7, 0x10, 0x44, 0x1, 0xfe, 0x31, 0xf1, 0xc1, 0xc1, 0xc, 0x1, 0xcb, 0x41, 0x31, 0xdf, 0x41, 0xc1, 0xc7, 0x8, 0x44, 0x1, 0xfe, 0x31, 0xf1, 0xc1, 0xc1, 0x7]

def main4Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100d72 2 3 1) (xorR32R32Effect 0x100d74 3 15 3)) (rolR32Effect 0x100d77 4 15 16)) (addR32R32Effect 0x100d7b 3 6 15)) (xorR32R32Effect 0x100d7e 2 1 6)) (rolR32Effect 0x100d80 3 1 12)) (addR32R32Effect 0x100d83 2 3 1)) (xorR32R32Effect 0x100d85 3 15 3)) (rolR32Effect 0x100d88 4 15 8)) (addR32R32Effect 0x100d8c 3 6 15)) (xorR32R32Effect 0x100d8f 2 1 6)) (rolR32Effect 0x100d91 3 1 7))

theorem main4Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100d72 ∧ RFrame stack s)
      (codeRange 0x100d72 main4Bytes) main4Effect := by
  unfold main4Bytes
  rr_begin (add_r32_r32_effect_step 0x100d72 0xcb (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d74 0x41 0xdf (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d77 0x41 0xc7 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d7b 0x44 0xfe (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100d7e 0xf1 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d80 0xc1 0xc (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100d83 0xcb (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d85 0x41 0xdf (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d88 0x41 0xc7 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d8c 0x44 0xfe (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100d8f 0xf1 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100d91 0xc1 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main4Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainAlias x))
    (he : (main4Effect s).Holds s t) :
    Write.AllHold t (cut stack mainAlias (qroundRol x 0 5 10 15)) := by
  have hfull : ∀ w ∈ (main4Effect s).writes, w.Full := by x86_norm [main4Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainAlias, mainBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main4Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main4Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100d72 0x100d94 mainQR mainAlias mainAlias
      (fun x => qroundRol x 0 5 10 15) := by
  apply Seg.of_block (main4Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xd72 34 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xd72 34 = main4Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xd72 = 0x100d72 from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main4Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main4Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main4Words hs hw he

def main5Bytes : List UInt8 :=
  [0x41, 0x1, 0xd5, 0x45, 0x31, 0xe9, 0x41, 0xc1, 0xc1, 0x10, 0x45, 0x1, 0xc8, 0x44, 0x31, 0xc2, 0xc1, 0xc2, 0xc, 0x41, 0x1, 0xd5, 0x45, 0x31, 0xe9, 0x41, 0xc1, 0xc1, 0x8, 0x45, 0x1, 0xc8, 0x44, 0x31, 0xc2, 0xc1, 0xc2, 0x7]

def main5Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100d94 3 13 2) (xorR32R32Effect 0x100d97 3 9 13)) (rolR32Effect 0x100d9a 4 9 16)) (addR32R32Effect 0x100d9e 3 8 9)) (xorR32R32Effect 0x100da1 3 2 8)) (rolR32Effect 0x100da4 3 2 12)) (addR32R32Effect 0x100da7 3 13 2)) (xorR32R32Effect 0x100daa 3 9 13)) (rolR32Effect 0x100dad 4 9 8)) (addR32R32Effect 0x100db1 3 8 9)) (xorR32R32Effect 0x100db4 3 2 8)) (rolR32Effect 0x100db7 3 2 7))

theorem main5Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100d94 ∧ RFrame stack s)
      (codeRange 0x100d94 main5Bytes) main5Effect := by
  unfold main5Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x100d94 0x41 0xd5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100d97 0x45 0xe9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100d9a 0x41 0xc1 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100d9e 0x45 0xc8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100da1 0x44 0xc2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100da4 0xc2 0xc (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100da7 0x41 0xd5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100daa 0x45 0xe9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100dad 0x41 0xc1 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100db1 0x45 0xc8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100db4 0x44 0xc2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100db7 0xc2 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main5Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainAlias x))
    (he : (main5Effect s).Holds s t) :
    Write.AllHold t (cut stack mainAlias (qroundRol x 1 6 11 12)) := by
  have hfull : ∀ w ∈ (main5Effect s).writes, w.Full := by x86_norm [main5Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainAlias, mainBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main5Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main5Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100d94 0x100dba mainQR mainAlias mainAlias
      (fun x => qroundRol x 1 6 11 12) := by
  apply Seg.of_block (main5Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xd94 38 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xd94 38 = main5Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xd94 = 0x100d94 from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main5Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main5Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main5Words hs hw he

def main6Bytes : List UInt8 :=
  [0x45, 0x1, 0xdc, 0x44, 0x31, 0xe7, 0xc1, 0xc7, 0x10, 0x8b, 0x44, 0x24, 0x4, 0x1, 0xf8, 0x41, 0x31, 0xc3, 0x41, 0xc1, 0xc3, 0xc, 0x45, 0x1, 0xdc, 0x44, 0x31, 0xe7, 0xc1, 0xc7, 0x8, 0x1, 0xf8, 0x89, 0x44, 0x24, 0x4, 0x41, 0x31, 0xc3, 0x8b, 0x44, 0x24, 0x8, 0x41, 0xc1, 0xc3, 0x7]

def main6Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100dba 3 12 11) (xorR32R32Effect 0x100dbd 3 7 12)) (rolR32Effect 0x100dc0 3 7 16)) (movR32M32LowEffect 0x100dc3 0 (.sib 4 none 0 (.d8 0x4)))) (addR32R32Effect 0x100dc7 2 0 7)) (xorR32R32Effect 0x100dc9 3 11 0)) (rolR32Effect 0x100dcc 4 11 12)) (addR32R32Effect 0x100dd0 3 12 11)) (xorR32R32Effect 0x100dd3 3 7 12)) (rolR32Effect 0x100dd6 3 7 8)) (addR32R32Effect 0x100dd9 2 0 7)) (movM32R32LowEffect 0x100ddb 0 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x100ddf 3 11 0)) (movR32M32LowEffect 0x100de2 0 (.sib 4 none 0 (.d8 0x8)))) (rolR32Effect 0x100de6 4 11 7))

theorem main6Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100dba ∧ RFrame stack s)
      (codeRange 0x100dba main6Bytes) main6Effect := by
  unfold main6Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x100dba 0x45 0xdc (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100dbd 0x44 0xe7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100dc0 0xc7 0x10 (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100dc3 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100dc7 0xf8 (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100dc9 0x41 0xc3 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100dcc 0x41 0xc3 0xc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100dd0 0x45 0xdc (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100dd3 0x44 0xe7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100dd6 0xc7 0x8 (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x100dd9 0xf8 (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x100ddb 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100ddf 0x41 0xc3 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100de2 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100de6 0x41 0xc3 0x7 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main6Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainAlias x))
    (he : (main6Effect s).Holds s t) :
    Write.AllHold t (cut stack mainBase (qroundRol x 2 7 8 13)) := by
  have hfull : ∀ w ∈ (main6Effect s).writes, w.Full := by x86_norm [main6Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainAlias, mainBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main6Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main6Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100dba 0x100dea mainQR mainAlias mainBase
      (fun x => qroundRol x 2 7 8 13) := by
  apply Seg.of_block (main6Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xdba 48 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xdba 48 = main6Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xdba = 0x100dba from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main6Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main6Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main6Words hs hw he

def main7Bytes : List UInt8 :=
  [0x41, 0x1, 0xea, 0x45, 0x31, 0xd6, 0x41, 0xc1, 0xc6, 0x10, 0x44, 0x1, 0xf0, 0x31, 0xc5, 0xc1, 0xc5, 0xc, 0x41, 0x1, 0xea, 0x45, 0x31, 0xd6, 0x41, 0xc1, 0xc6, 0x8, 0x44, 0x1, 0xf0, 0x31, 0xc5, 0xc1, 0xc5, 0x7]

def main7Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x100dea 3 10 5) (xorR32R32Effect 0x100ded 3 14 10)) (rolR32Effect 0x100df0 4 14 16)) (addR32R32Effect 0x100df4 3 0 14)) (xorR32R32Effect 0x100df7 2 5 0)) (rolR32Effect 0x100df9 3 5 12)) (addR32R32Effect 0x100dfc 3 10 5)) (xorR32R32Effect 0x100dff 3 14 10)) (rolR32Effect 0x100e02 4 14 8)) (addR32R32Effect 0x100e06 3 0 14)) (xorR32R32Effect 0x100e09 2 5 0)) (rolR32Effect 0x100e0b 3 5 7))

theorem main7Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100dea ∧ RFrame stack s)
      (codeRange 0x100dea main7Bytes) main7Effect := by
  unfold main7Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x100dea 0x41 0xea (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100ded 0x45 0xd6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100df0 0x41 0xc6 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100df4 0x44 0xf0 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100df7 0xc5 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100df9 0xc5 0xc (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100dfc 0x41 0xea (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x100dff 0x45 0xd6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x100e02 0x41 0xc6 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x100e06 0x44 0xf0 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_effect_step 0x100e09 0xc5 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x100e0b 0xc5 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem main7Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack mainBase x))
    (he : (main7Effect s).Holds s t) :
    Write.AllHold t (cut stack mainBase (qroundRol x 3 4 9 14)) := by
  have hfull : ∀ w ∈ (main7Effect s).writes, w.Full := by x86_norm [main7Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, mainBase, List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [main7Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem main7Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100dea 0x100e0e mainQR mainBase mainBase
      (fun x => qroundRol x 3 4 9 14) := by
  apply Seg.of_block (main7Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0xdea 36 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xdea 36 = main7Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xdea = 0x100dea from by decide] at h
  · exact mainQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [main7Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [main7Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainQR, regScratch])
  · intro stack x s t hs hw he
    exact main7Words hs hw he

def tail0Bytes : List UInt8 :=
  [0x44, 0x89, 0x74, 0x24, 0x78, 0x44, 0x8b, 0x74, 0x24, 0x8, 0x45, 0x1, 0xce, 0x44, 0x31, 0xf1, 0xc1, 0xc1, 0x10, 0x8b, 0x5c, 0x24, 0x4, 0x1, 0xcb, 0x41, 0x31, 0xd9, 0x41, 0xc1, 0xc1, 0xc, 0x45, 0x1, 0xce, 0x44, 0x31, 0xf1, 0xc1, 0xc1, 0x8, 0x1, 0xcb, 0x89, 0x5c, 0x24, 0x4, 0x41, 0x31, 0xd9, 0x44, 0x89, 0xf3, 0x44, 0x8b, 0x74, 0x24, 0x78, 0x41, 0xc1, 0xc1, 0x7]

def tail0Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movM32R32Effect 0x101180 14 (.sib 4 none 0 (.d8 0x78))) (movR32M32Effect 0x101185 14 (.sib 4 none 0 (.d8 0x8)))) (addR32R32Effect 0x10118a 3 14 9)) (xorR32R32Effect 0x10118d 3 1 14)) (rolR32Effect 0x101190 3 1 16)) (movR32M32LowEffect 0x101193 3 (.sib 4 none 0 (.d8 0x4)))) (addR32R32Effect 0x101197 2 3 1)) (xorR32R32Effect 0x101199 3 9 3)) (rolR32Effect 0x10119c 4 9 12)) (addR32R32Effect 0x1011a0 3 14 9)) (xorR32R32Effect 0x1011a3 3 1 14)) (rolR32Effect 0x1011a6 3 1 8)) (addR32R32Effect 0x1011a9 2 3 1)) (movM32R32LowEffect 0x1011ab 3 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x1011af 3 9 3)) (movR32R32Effect 0x1011b2 3 3 14)) (movR32M32Effect 0x1011b5 14 (.sib 4 none 0 (.d8 0x78)))) (rolR32Effect 0x1011ba 4 9 7))

theorem tail0Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x101180 ∧ RFrame stack s)
      (codeRange 0x101180 tail0Bytes) tail0Effect := by
  unfold tail0Bytes
  rr_begin (mov_m32_r32_effect_step 0x101180 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x101185 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x10118a 0x45 0xce (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10118d 0x44 0xf1 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101190 0xc1 0x10 (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x101193 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x101197 0xcb (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101199 0x41 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x10119c 0x41 0xc1 0xc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1011a0 0x45 0xce (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011a3 0x44 0xf1 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x1011a6 0xc1 0x8 (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x1011a9 0xcb (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x1011ab 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011af 0x41 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_r32_r32_rex_effect_step 0x1011b2 0x44 0xf3 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x1011b5 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1011ba 0x41 0xc1 0x7 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail0Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailBase x))
    (he : (tail0Effect s).Holds s t) :
    Write.AllHold t (cut stack tailB (qroundRol x 0 4 8 12)) := by
  have hfull : ∀ w ∈ (tail0Effect s).writes, w.Full := by x86_norm [tail0Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailBase, tailB, List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail0Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail0Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x101180 0x1011be tailQR tailBase tailB
      (fun x => qroundRol x 0 4 8 12) := by
  apply Seg.of_block (tail0Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x1180 62 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x1180 62 = tail0Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x1180 = 0x101180 from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail0Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail0Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail0Words hs hw he

def tail1Bytes : List UInt8 :=
  [0x41, 0x1, 0xed, 0x44, 0x31, 0xea, 0xc1, 0xc2, 0x10, 0x41, 0x1, 0xd2, 0x44, 0x31, 0xd5, 0xc1, 0xc5, 0xc, 0x41, 0x1, 0xed, 0x44, 0x31, 0xea, 0xc1, 0xc2, 0x8, 0x41, 0x1, 0xd2, 0x44, 0x89, 0x54, 0x24, 0x14, 0x44, 0x31, 0xd5, 0xc1, 0xc5, 0x7]

def tail1Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x1011be 3 13 5) (xorR32R32Effect 0x1011c1 3 2 13)) (rolR32Effect 0x1011c4 3 2 16)) (addR32R32Effect 0x1011c7 3 10 2)) (xorR32R32Effect 0x1011ca 3 5 10)) (rolR32Effect 0x1011cd 3 5 12)) (addR32R32Effect 0x1011d0 3 13 5)) (xorR32R32Effect 0x1011d3 3 2 13)) (rolR32Effect 0x1011d6 3 2 8)) (addR32R32Effect 0x1011d9 3 10 2)) (movM32R32Effect 0x1011dc 10 (.sib 4 none 0 (.d8 0x14)))) (xorR32R32Effect 0x1011e1 3 5 10)) (rolR32Effect 0x1011e4 3 5 7))

theorem tail1Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1011be ∧ RFrame stack s)
      (codeRange 0x1011be tail1Bytes) tail1Effect := by
  unfold tail1Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x1011be 0x41 0xed (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011c1 0x44 0xea (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x1011c4 0xc2 0x10 (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1011c7 0x41 0xd2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011ca 0x44 0xd5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x1011cd 0xc5 0xc (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1011d0 0x41 0xed (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011d3 0x44 0xea (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x1011d6 0xc2 0x8 (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1011d9 0x41 0xd2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x1011dc 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011e1 0x44 0xd5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x1011e4 0xc5 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail1Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailB x))
    (he : (tail1Effect s).Holds s t) :
    Write.AllHold t (cut stack tailC (qroundRol x 1 5 9 13)) := by
  have hfull : ∀ w ∈ (tail1Effect s).writes, w.Full := by x86_norm [tail1Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailB, tailC, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail1Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail1Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x1011be 0x1011e7 tailQR tailB tailC
      (fun x => qroundRol x 1 5 9 13) := by
  apply Seg.of_block (tail1Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x11be 41 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x11be 41 = tail1Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x11be = 0x1011be from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail1Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail1Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail1Words hs hw he

def tail2Bytes : List UInt8 :=
  [0x44, 0x1, 0xf8, 0x41, 0x31, 0xc0, 0x41, 0xc1, 0xc0, 0x10, 0x45, 0x1, 0xc6, 0x45, 0x31, 0xf7, 0x41, 0xc1, 0xc7, 0xc, 0x44, 0x1, 0xf8, 0x41, 0x31, 0xc0, 0x41, 0xc1, 0xc0, 0x8, 0x45, 0x1, 0xc6, 0x45, 0x31, 0xf7, 0x41, 0xc1, 0xc7, 0x7]

def tail2Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x1011e7 3 0 15) (xorR32R32Effect 0x1011ea 3 8 0)) (rolR32Effect 0x1011ed 4 8 16)) (addR32R32Effect 0x1011f1 3 14 8)) (xorR32R32Effect 0x1011f4 3 15 14)) (rolR32Effect 0x1011f7 4 15 12)) (addR32R32Effect 0x1011fb 3 0 15)) (xorR32R32Effect 0x1011fe 3 8 0)) (rolR32Effect 0x101201 4 8 8)) (addR32R32Effect 0x101205 3 14 8)) (xorR32R32Effect 0x101208 3 15 14)) (rolR32Effect 0x10120b 4 15 7))

theorem tail2Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1011e7 ∧ RFrame stack s)
      (codeRange 0x1011e7 tail2Bytes) tail2Effect := by
  unfold tail2Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x1011e7 0x44 0xf8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011ea 0x41 0xc0 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1011ed 0x41 0xc0 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1011f1 0x45 0xc6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011f4 0x45 0xf7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1011f7 0x41 0xc7 0xc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1011fb 0x44 0xf8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1011fe 0x41 0xc0 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x101201 0x41 0xc0 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x101205 0x45 0xc6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101208 0x45 0xf7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x10120b 0x41 0xc7 0x7 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail2Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailC x))
    (he : (tail2Effect s).Holds s t) :
    Write.AllHold t (cut stack tailC (qroundRol x 2 6 10 14)) := by
  have hfull : ∀ w ∈ (tail2Effect s).writes, w.Full := by x86_norm [tail2Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailC, tailB, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail2Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail2Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x1011e7 0x10120f tailQR tailC tailC
      (fun x => qroundRol x 2 6 10 14) := by
  apply Seg.of_block (tail2Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x11e7 40 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x11e7 40 = tail2Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x11e7 = 0x1011e7 from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail2Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail2Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail2Words hs hw he

def tail3Bytes : List UInt8 :=
  [0x1, 0xf7, 0x41, 0x31, 0xfb, 0x41, 0xc1, 0xc3, 0x10, 0x45, 0x1, 0xdc, 0x44, 0x31, 0xe6, 0xc1, 0xc6, 0xc, 0x1, 0xf7, 0x41, 0x31, 0xfb, 0x41, 0xc1, 0xc3, 0x8, 0x45, 0x1, 0xdc, 0x44, 0x31, 0xe6, 0xc1, 0xc6, 0x7]

def tail3Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x10120f 2 7 6) (xorR32R32Effect 0x101211 3 11 7)) (rolR32Effect 0x101214 4 11 16)) (addR32R32Effect 0x101218 3 12 11)) (xorR32R32Effect 0x10121b 3 6 12)) (rolR32Effect 0x10121e 3 6 12)) (addR32R32Effect 0x101221 2 7 6)) (xorR32R32Effect 0x101223 3 11 7)) (rolR32Effect 0x101226 4 11 8)) (addR32R32Effect 0x10122a 3 12 11)) (xorR32R32Effect 0x10122d 3 6 12)) (rolR32Effect 0x101230 3 6 7))

theorem tail3Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x10120f ∧ RFrame stack s)
      (codeRange 0x10120f tail3Bytes) tail3Effect := by
  unfold tail3Bytes
  rr_begin (add_r32_r32_effect_step 0x10120f 0xf7 (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101211 0x41 0xfb (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x101214 0x41 0xc3 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x101218 0x45 0xdc (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10121b 0x44 0xe6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x10121e 0xc6 0xc (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x101221 0xf7 (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101223 0x41 0xfb (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x101226 0x41 0xc3 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x10122a 0x45 0xdc (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10122d 0x44 0xe6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101230 0xc6 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail3Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailC x))
    (he : (tail3Effect s).Holds s t) :
    Write.AllHold t (cut stack tailC (qroundRol x 3 7 11 15)) := by
  have hfull : ∀ w ∈ (tail3Effect s).writes, w.Full := by x86_norm [tail3Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailC, tailB, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail3Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail3Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x10120f 0x101233 tailQR tailC tailC
      (fun x => qroundRol x 3 7 11 15) := by
  apply Seg.of_block (tail3Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x120f 36 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x120f 36 = tail3Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x120f = 0x10120f from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail3Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail3Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail3Words hs hw he

def tail4Bytes : List UInt8 :=
  [0x1, 0xeb, 0x41, 0x31, 0xdb, 0x41, 0xc1, 0xc3, 0x10, 0x45, 0x1, 0xde, 0x44, 0x31, 0xf5, 0xc1, 0xc5, 0xc, 0x1, 0xeb, 0x89, 0x5c, 0x24, 0x8, 0x41, 0x31, 0xdb, 0x41, 0xc1, 0xc3, 0x8, 0x45, 0x1, 0xde, 0x44, 0x31, 0xf5, 0xc1, 0xc5, 0x7]

def tail4Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x101233 2 3 5) (xorR32R32Effect 0x101235 3 11 3)) (rolR32Effect 0x101238 4 11 16)) (addR32R32Effect 0x10123c 3 14 11)) (xorR32R32Effect 0x10123f 3 5 14)) (rolR32Effect 0x101242 3 5 12)) (addR32R32Effect 0x101245 2 3 5)) (movM32R32LowEffect 0x101247 3 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect 0x10124b 3 11 3)) (rolR32Effect 0x10124e 4 11 8)) (addR32R32Effect 0x101252 3 14 11)) (xorR32R32Effect 0x101255 3 5 14)) (rolR32Effect 0x101258 3 5 7))

theorem tail4Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x101233 ∧ RFrame stack s)
      (codeRange 0x101233 tail4Bytes) tail4Effect := by
  unfold tail4Bytes
  rr_begin (add_r32_r32_effect_step 0x101233 0xeb (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101235 0x41 0xdb (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x101238 0x41 0xc3 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x10123c 0x45 0xde (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10123f 0x44 0xf5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101242 0xc5 0xc (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x101245 0xeb (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101247 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10124b 0x41 0xdb (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x10124e 0x41 0xc3 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x101252 0x45 0xde (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101255 0x44 0xf5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101258 0xc5 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail4Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailC x))
    (he : (tail4Effect s).Holds s t) :
    Write.AllHold t (cut stack tailD (qroundRol x 0 5 10 15)) := by
  have hfull : ∀ w ∈ (tail4Effect s).writes, w.Full := by x86_norm [tail4Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailC, tailB, tailD, tailBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail4Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail4Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x101233 0x10125b tailQR tailC tailD
      (fun x => qroundRol x 0 5 10 15) := by
  apply Seg.of_block (tail4Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x1233 40 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x1233 40 = tail4Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x1233 = 0x101233 from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail4Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail4Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail4Words hs hw he

def tail5Bytes : List UInt8 :=
  [0x45, 0x1, 0xfd, 0x44, 0x31, 0xe9, 0xc1, 0xc1, 0x10, 0x41, 0x1, 0xcc, 0x45, 0x31, 0xe7, 0x41, 0xc1, 0xc7, 0xc, 0x45, 0x1, 0xfd, 0x44, 0x31, 0xe9, 0xc1, 0xc1, 0x8, 0x41, 0x1, 0xcc, 0x45, 0x31, 0xe7, 0x41, 0xc1, 0xc7, 0x7]

def tail5Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x10125b 3 13 15) (xorR32R32Effect 0x10125e 3 1 13)) (rolR32Effect 0x101261 3 1 16)) (addR32R32Effect 0x101264 3 12 1)) (xorR32R32Effect 0x101267 3 15 12)) (rolR32Effect 0x10126a 4 15 12)) (addR32R32Effect 0x10126e 3 13 15)) (xorR32R32Effect 0x101271 3 1 13)) (rolR32Effect 0x101274 3 1 8)) (addR32R32Effect 0x101277 3 12 1)) (xorR32R32Effect 0x10127a 3 15 12)) (rolR32Effect 0x10127d 4 15 7))

theorem tail5Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x10125b ∧ RFrame stack s)
      (codeRange 0x10125b tail5Bytes) tail5Effect := by
  unfold tail5Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x10125b 0x45 0xfd (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10125e 0x44 0xe9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101261 0xc1 0x10 (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x101264 0x41 0xcc (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101267 0x45 0xe7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x10126a 0x41 0xc7 0xc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x10126e 0x45 0xfd (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101271 0x44 0xe9 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101274 0xc1 0x8 (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x101277 0x41 0xcc (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x10127a 0x45 0xe7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x10127d 0x41 0xc7 0x7 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail5Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailD x))
    (he : (tail5Effect s).Holds s t) :
    Write.AllHold t (cut stack tailD (qroundRol x 1 6 11 12)) := by
  have hfull : ∀ w ∈ (tail5Effect s).writes, w.Full := by x86_norm [tail5Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailD, tailBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail5Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail5Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x10125b 0x101281 tailQR tailD tailD
      (fun x => qroundRol x 1 6 11 12) := by
  apply Seg.of_block (tail5Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x125b 38 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x125b 38 = tail5Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x125b = 0x10125b from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail5Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail5Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail5Words hs hw he

def tail6Bytes : List UInt8 :=
  [0x1, 0xf0, 0x31, 0xc2, 0xc1, 0xc2, 0x10, 0x44, 0x8b, 0x54, 0x24, 0x4, 0x41, 0x1, 0xd2, 0x44, 0x31, 0xd6, 0xc1, 0xc6, 0xc, 0x1, 0xf0, 0x31, 0xc2, 0xc1, 0xc2, 0x8, 0x41, 0x1, 0xd2, 0x44, 0x89, 0x54, 0x24, 0x4, 0x44, 0x31, 0xd6, 0x44, 0x8b, 0x54, 0x24, 0x14, 0xc1, 0xc6, 0x7]

def tail6Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x101281 2 0 6) (xorR32R32Effect 0x101283 2 2 0)) (rolR32Effect 0x101285 3 2 16)) (movR32M32Effect 0x101288 10 (.sib 4 none 0 (.d8 0x4)))) (addR32R32Effect 0x10128d 3 10 2)) (xorR32R32Effect 0x101290 3 6 10)) (rolR32Effect 0x101293 3 6 12)) (addR32R32Effect 0x101296 2 0 6)) (xorR32R32Effect 0x101298 2 2 0)) (rolR32Effect 0x10129a 3 2 8)) (addR32R32Effect 0x10129d 3 10 2)) (movM32R32Effect 0x1012a0 10 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x1012a5 3 6 10)) (movR32M32Effect 0x1012a8 10 (.sib 4 none 0 (.d8 0x14)))) (rolR32Effect 0x1012ad 3 6 7))

theorem tail6Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x101281 ∧ RFrame stack s)
      (codeRange 0x101281 tail6Bytes) tail6Effect := by
  unfold tail6Bytes
  rr_begin (add_r32_r32_effect_step 0x101281 0xf0 (by decide))
  rr_then (xor_r32_r32_effect_step 0x101283 0xc2 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101285 0xc2 0x10 (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x101288 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x10128d 0x41 0xd2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x101290 0x44 0xd6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x101293 0xc6 0xc (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x101296 0xf0 (by decide))
  rr_then (xor_r32_r32_effect_step 0x101298 0xc2 (by decide))
  rr_then (rol_r32_imm8_effect_step 0x10129a 0xc2 0x8 (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x10129d 0x41 0xd2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x1012a0 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1012a5 0x44 0xd6 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x1012a8 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide))
  rr_then (rol_r32_imm8_effect_step 0x1012ad 0xc6 0x7 (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail6Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailD x))
    (he : (tail6Effect s).Holds s t) :
    Write.AllHold t (cut stack tailBase (qroundRol x 2 7 8 13)) := by
  have hfull : ∀ w ∈ (tail6Effect s).writes, w.Full := by x86_norm [tail6Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailD, tailBase, List.cons_append, List.nil_append,
    List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail6Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail6Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x101281 0x1012b0 tailQR tailD tailBase
      (fun x => qroundRol x 2 7 8 13) := by
  apply Seg.of_block (tail6Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x1281 47 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x1281 47 = tail6Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x1281 = 0x101281 from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail6Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail6Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail6Words hs hw he

def tail7Bytes : List UInt8 :=
  [0x44, 0x1, 0xcf, 0x41, 0x31, 0xf8, 0x41, 0xc1, 0xc0, 0x10, 0x45, 0x1, 0xc2, 0x45, 0x31, 0xd1, 0x41, 0xc1, 0xc1, 0xc, 0x44, 0x1, 0xcf, 0x41, 0x31, 0xf8, 0x41, 0xc1, 0xc0, 0x8, 0x45, 0x1, 0xc2, 0x45, 0x31, 0xd1, 0x41, 0xc1, 0xc1, 0x7]

def tail7Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32R32Effect 0x1012b0 3 7 9) (xorR32R32Effect 0x1012b3 3 8 7)) (rolR32Effect 0x1012b6 4 8 16)) (addR32R32Effect 0x1012ba 3 10 8)) (xorR32R32Effect 0x1012bd 3 9 10)) (rolR32Effect 0x1012c0 4 9 12)) (addR32R32Effect 0x1012c4 3 7 9)) (xorR32R32Effect 0x1012c7 3 8 7)) (rolR32Effect 0x1012ca 4 8 8)) (addR32R32Effect 0x1012ce 3 10 8)) (xorR32R32Effect 0x1012d1 3 9 10)) (rolR32Effect 0x1012d4 4 9 7))

theorem tail7Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1012b0 ∧ RFrame stack s)
      (codeRange 0x1012b0 tail7Bytes) tail7Effect := by
  unfold tail7Bytes
  rr_begin (add_r32_r32_rex_effect_step 0x1012b0 0x44 0xcf (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1012b3 0x41 0xf8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1012b6 0x41 0xc0 0x10 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1012ba 0x45 0xc2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1012bd 0x45 0xd1 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1012c0 0x41 0xc1 0xc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1012c4 0x44 0xcf (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1012c7 0x41 0xf8 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1012ca 0x41 0xc0 0x8 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_then (add_r32_r32_rex_effect_step 0x1012ce 0x45 0xc2 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (xor_r32_r32_rex_effect_step 0x1012d1 0x45 0xd1 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (rol_r32_imm8_rex_effect_step 0x1012d4 0x41 0xc1 0x7 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  rr_finish

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem tail7Words {stack : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack) (hw : Write.AllHold s (cut stack tailBase x))
    (he : (tail7Effect s).Holds s t) :
    Write.AllHold t (cut stack tailBase (qroundRol x 3 4 9 14)) := by
  have hfull : ∀ w ∈ (tail7Effect s).writes, w.Full := by x86_norm [tail7Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [cut, tailBase, List.map, Loc.op, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [tail7Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp (config := {decide := true}) only [qroundRol, quarterRoundRol, rotl, Fin.getElem_fin,
    Vector.getElem_set, Fin.isValue, ite_true, ite_false, UInt32.toBitVec_add,
    UInt32.toBitVec_xor, UInt32.toBitVec_ofBitVec, and_true]

theorem tail7Seg [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x1012b0 0x1012d8 tailQR tailBase tailBase
      (fun x => qroundRol x 3 4 9 14) := by
  apply Seg.of_block (tail7Block boundary hb)
  · intro s hc
    have h := program_text_slice hc 0x12b0 40 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x12b0 40 = tail7Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x12b0 = 0x1012b0 from by decide] at h
  · exact tailQR_good
  · intro s t he
    exact he.rip.trans (by x86_norm [tail7Effect])
  · intro stack s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [tail7Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailQR, regScratch])
  · intro stack x s t hs hw he
    exact tail7Words hs hw he


theorem read_mem_agrees {cs : List Component} {s t : RamState} {a : BitVec 64} {n : Nat}
    (ha : AgreesExcept cs s t) (h : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  simp only [Operand.read]
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  congr 1
  exact ha.byte (h i hi)

theorem allHold_congr {s t : RamState} {ws : List Write}
    (h : ∀ w ∈ ws, w.dst.read t = w.dst.read s) (hw : Write.AllHold s ws) :
    Write.AllHold t ws := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    cases ws with
    | nil => exact (h w (by simp)).trans hw
    | cons w' ws' =>
      exact ⟨(h w (by simp)).trans hw.1,
        ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) hw.2⟩

theorem cut_rip {stack : BitVec 64} {L : List (Fin 16 × Loc)} {x : Vector UInt32 16}
    {t u : RamState} (ha : AgreesExcept [.rip] t u) (hw : Write.AllHold t (cut stack L x)) :
    Write.AllHold u (cut stack L x) := by
  apply allHold_congr _ hw
  intro w hw
  simp only [cut, List.mem_map] at hw
  obtain ⟨e, -, rfl⟩ := hw
  cases e.2 with
  | reg r => exact ha.read (by simp)
  | slot o => exact read_mem_agrees ha (by simp [Component.Covers])


theorem mainCount [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat)
    {stack : BitVec 64} {x : Vector UInt32 16} {n : Nat} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hp : s.RIP = 0x100e0e)
    (hf : RFrame stack s) (hw : Write.AllHold s (cut stack mainBase x))
    (hn : (Operand.mem (stack + 0x78) : Operand 64).read s = BitVec.ofNat 64 (n + 1))
    (hn' : n + 1 < 2 ^ 64) :
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = (if n = 0 then 0x100e19 else 0x100cd0) ∧ RFrame stack u ∧
      Write.AllHold u (cut stack mainBase x) ∧
      (Operand.mem (stack + 0x78) : Operand 64).read u = BitVec.ofNat 64 n ∧
      AgreesExcept (mainScratch stack) s u := by
  have hP : s.RIP = 0x100e0e ∧ RFrame stack s := ⟨hp, hf⟩
  have hc1 : CodeIn (codeRange 0x100e0e [0x48, 0xff, 0x4c, 0x24, 0x78]) s := by
    have h := program_text_slice hc 0xe0e 5 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xe0e 5 = [0x48, 0xff, 0x4c, 0x24, 0x78] from by
        decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xe0e = 0x100e0e from by decide] at h
  obtain ⟨t, ha1, hr1, he1⟩ := (dec_m64_effect_step 0x100e0e 0x48 (by unfold RexWPrefix; decide)
    (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)).advances
    (boundary := boundary) hr hc1
    (by refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
          (by x86_addr_obs) ?_ ?_ <;> rr_frame hP)
    (ne_boundary hb (by x86_norm) (by x86_norm))
  have hs := hf.rsp
  have hag1 : AgreesExcept (mainScratch stack) s t := by
    have ha := he1.agrees
    x86_norm at hs
    x86_norm [hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [mainScratch, mainQR, regScratch])
  have hf1 := hf.of_agrees (mainScratch_good stack) hag1
  have hct := hf.codeIn (mainScratch_good stack) hag1 hc
  have hzf := he1.flags
  have hfull1 : ∀ w ∈ (decMEffect 0x100e0e (3 + (AddrMode.sib 4 none 0 (.d8 0x78)).tail.length) 64
      (.sib 4 none 0 (.d8 0x78)) s).writes, w.Full := by x86_norm
  have ho1 := he1.obsAfter hfull1 true
  have hs' := hs
  x86_norm at hs'
  have hw1 : Write.AllHold t (cut stack mainBase x) := by
    simp only [cut, mainBase, List.map, Loc.op, Write.AllHold] at hw ⊢
    simp only [← ho1.read_reg, ← ho1.read_mem]
    x86_norm [hs']
    exact hw
  have hn1 : (Operand.mem (stack + 0x78) : Operand 64).read t = BitVec.ofNat 64 n := by
    rw [← ho1.read_mem]
    x86_norm [hs']
    x86_norm at hn
    rw [hn, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hc2 : CodeIn (codeRange 0x100e13 (0x0F :: jccOpcode32 5 :: immBytes 32 0xfffffeb7)) t := by
    have h := program_text_slice hct 0xe13 6 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xe13 6 = 0x0F :: jccOpcode32 5 :: immBytes 32 0xfffffeb7
        from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xe13 = 0x100e13 from by decide] at h
  have hz : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = (BitVec.ofNat 64 n == 0) := by
    simp only [Effect.FlagsHold, decMEffect, StatusFlagsOutcome.Allows,
      StatusFlagsOutcome.ofStatusFlags, FlagAllows, decSpec] at hzf
    have h4 := hzf.2.2.2.1
    x86_norm [hs'] at h4
    x86_norm at hn
    rw [h4, hn, BitVec.ofNat_add, BitVec.add_sub_cancel]
    rfl
  obtain ⟨u, ha2, hr2, he2⟩ := (jcc_rel32_effect_step 0x100e13 5 0xfffffeb7).advances
    (boundary := boundary) hr1 hc2 ⟨he1.rip.trans (by x86_norm), fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect]; split <;> exact ne_boundary hb (by decide) (by decide))
  have hag2 : AgreesExcept [.rip] t u := he2.agrees.mono (by simp [jccEffect, Effect.components, branchEffect])
  refine ⟨1 + 1, u, ha1.trans ha2, hr2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf1.codeIn (cs := [.rip]) ⟨by simp, by simp [Component.Covers]⟩ hag2 hct
  · rw [he2.rip]
    simp only [jccEffect, branchEffect, branchTarget]
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS t.RFLAGS) = !(BitVec.ofNat 64 n == 0) := by
      rw [← hz]; rfl
    rw [hcond]
    by_cases h0 : n = 0
    · subst h0; decide
    · have hne : (BitVec.ofNat 64 n == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        apply h0
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega
      simp only [hne, h0, Bool.not_false, ite_true, ite_false]
      decide
  · exact hf1.of_agrees (cs := [.rip]) ⟨by simp, by simp [Component.Covers]⟩ hag2
  · exact cut_rip hag2 hw1
  · rw [read_mem_agrees hag2 (by simp [Component.Covers])]; exact hn1
  · exact (hag1.trans hag2).mono (by simp [mainScratch, mainQR, regScratch])

theorem tailCount [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat)
    {stack : BitVec 64} {x : Vector UInt32 16} {n : Nat} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hp : s.RIP = 0x1012d8)
    (hf : RFrame stack s) (hw : Write.AllHold s (cut stack tailBase x))
    (hn : (Operand.mem (stack + 0x58) : Operand 64).read s = BitVec.ofNat 64 (n + 1))
    (hn' : n + 1 < 2 ^ 64) :
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = (if n = 0 then 0x1012e3 else 0x101180) ∧ RFrame stack u ∧
      Write.AllHold u (cut stack tailBase x) ∧
      (Operand.mem (stack + 0x58) : Operand 64).read u = BitVec.ofNat 64 n ∧
      AgreesExcept (tailScratch stack) s u := by
  have hP : s.RIP = 0x1012d8 ∧ RFrame stack s := ⟨hp, hf⟩
  have hc1 : CodeIn (codeRange 0x1012d8 [0x48, 0xff, 0x4c, 0x24, 0x58]) s := by
    have h := program_text_slice hc 0x12d8 5 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x12d8 5 = [0x48, 0xff, 0x4c, 0x24, 0x58] from by
        decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x12d8 = 0x1012d8 from by decide] at h
  obtain ⟨t, ha1, hr1, he1⟩ := (dec_m64_effect_step 0x1012d8 0x48 (by unfold RexWPrefix; decide)
    (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)).advances
    (boundary := boundary) hr hc1
    (by refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
          (by x86_addr_obs) ?_ ?_ <;> rr_frame hP)
    (ne_boundary hb (by x86_norm) (by x86_norm))
  have hs := hf.rsp
  have hag1 : AgreesExcept (tailScratch stack) s t := by
    have ha := he1.agrees
    x86_norm at hs
    x86_norm [hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [tailScratch, tailQR, regScratch])
  have hf1 := hf.of_agrees (tailScratch_good stack) hag1
  have hct := hf.codeIn (tailScratch_good stack) hag1 hc
  have hzf := he1.flags
  have hfull1 : ∀ w ∈ (decMEffect 0x1012d8 (3 + (AddrMode.sib 4 none 0 (.d8 0x58)).tail.length) 64
      (.sib 4 none 0 (.d8 0x58)) s).writes, w.Full := by x86_norm
  have ho1 := he1.obsAfter hfull1 true
  have hs' := hs
  x86_norm at hs'
  have hw1 : Write.AllHold t (cut stack tailBase x) := by
    simp only [cut, tailBase, List.map, Loc.op, Write.AllHold] at hw ⊢
    simp only [← ho1.read_reg, ← ho1.read_mem]
    x86_norm [hs']
    exact hw
  have hn1 : (Operand.mem (stack + 0x58) : Operand 64).read t = BitVec.ofNat 64 n := by
    rw [← ho1.read_mem]
    x86_norm [hs']
    x86_norm at hn
    rw [hn, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hc2 : CodeIn (codeRange 0x1012dd (0x0F :: jccOpcode32 5 :: immBytes 32 0xfffffe9d)) t := by
    have h := program_text_slice hct 0x12dd 6 (by rw [textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x12dd 6 = 0x0F :: jccOpcode32 5 :: immBytes 32 0xfffffe9d
        from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x12dd = 0x1012dd from by decide] at h
  have hz : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = (BitVec.ofNat 64 n == 0) := by
    simp only [Effect.FlagsHold, decMEffect, StatusFlagsOutcome.Allows,
      StatusFlagsOutcome.ofStatusFlags, FlagAllows, decSpec] at hzf
    have h4 := hzf.2.2.2.1
    x86_norm [hs'] at h4
    x86_norm at hn
    rw [h4, hn, BitVec.ofNat_add, BitVec.add_sub_cancel]
    rfl
  obtain ⟨u, ha2, hr2, he2⟩ := (jcc_rel32_effect_step 0x1012dd 5 0xfffffe9d).advances
    (boundary := boundary) hr1 hc2 ⟨he1.rip.trans (by x86_norm), fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect]; split <;> exact ne_boundary hb (by decide) (by decide))
  have hag2 : AgreesExcept [.rip] t u := he2.agrees.mono (by simp [jccEffect, Effect.components, branchEffect])
  refine ⟨1 + 1, u, ha1.trans ha2, hr2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf1.codeIn (cs := [.rip]) ⟨by simp, by simp [Component.Covers]⟩ hag2 hct
  · rw [he2.rip]
    simp only [jccEffect, branchEffect, branchTarget]
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS t.RFLAGS) = !(BitVec.ofNat 64 n == 0) := by
      rw [← hz]; rfl
    rw [hcond]
    by_cases h0 : n = 0
    · subst h0; decide
    · have hne : (BitVec.ofNat 64 n == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        apply h0
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega
      simp only [hne, h0, Bool.not_false, ite_true, ite_false]
      decide
  · exact hf1.of_agrees (cs := [.rip]) ⟨by simp, by simp [Component.Covers]⟩ hag2
  · exact cut_rip hag2 hw1
  · rw [read_mem_agrees hag2 (by simp [Component.Covers])]; exact hn1
  · exact (hag1.trans hag2).mono (by simp [tailScratch, tailQR, regScratch])


def CountStep [Bindings] (boundary : ReturnBoundary) (p head exit cnt : BitVec 64)
    (scratch : BitVec 64 → List Component) (L : List (Fin 16 × Loc)) : Prop :=
  ∀ stack x n s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = p → RFrame stack s →
    Write.AllHold s (cut stack L x) →
    (Operand.mem (stack + cnt) : Operand 64).read s = BitVec.ofNat 64 (n + 1) → n + 1 < 2 ^ 64 →
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = (if n = 0 then exit else head) ∧ RFrame stack u ∧ Write.AllHold u (cut stack L x) ∧
      (Operand.mem (stack + cnt) : Operand 64).read u = BitVec.ofNat 64 n ∧
      AgreesExcept (scratch stack) s u

def Iter [Bindings] (boundary : ReturnBoundary) (head exit cnt : BitVec 64)
    (scratch : BitVec 64 → List Component) (L : List (Fin 16 × Loc)) : Prop :=
  ∀ stack x n s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = head →
    RFrame stack s → Write.AllHold s (cut stack L x) →
    (Operand.mem (stack + cnt) : Operand 64).read s = BitVec.ofNat 64 (n + 1) → n + 1 < 2 ^ 64 →
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = (if n = 0 then exit else head) ∧ RFrame stack u ∧
      Write.AllHold u (cut stack L (doubleRound x)) ∧
      (Operand.mem (stack + cnt) : Operand 64).read u = BitVec.ofNat 64 n ∧
      AgreesExcept (scratch stack) s u

def Loop [Bindings] (boundary : ReturnBoundary) (head exit cnt : BitVec 64)
    (scratch : BitVec 64 → List Component) (L : List (Fin 16 × Loc)) : Prop :=
  ∀ n stack x s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = head →
    RFrame stack s → Write.AllHold s (cut stack L x) →
    (Operand.mem (stack + cnt) : Operand 64).read s = BitVec.ofNat 64 (n + 1) → n + 1 < 2 ^ 64 →
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = exit ∧ RFrame stack u ∧
      Write.AllHold u (cut stack L (Nat.repeat doubleRound (n + 1) x)) ∧
      (Operand.mem (stack + cnt) : Operand 64).read u = 0 ∧
      AgreesExcept (scratch stack) s u

theorem Iter.of_seg [Bindings] {boundary : ReturnBoundary} {head p exit cnt : BitVec 64}
    {qr full : BitVec 64 → List Component} {L : List (Fin 16 × Loc)}
    (hseg : Seg boundary head p qr L L doubleRound) (hcount : CountStep boundary p head exit cnt full L)
    (hsub : ∀ stack, ∀ c ∈ qr stack, c ∈ full stack)
    (hcnt : ∀ stack, ∀ i < 8, ∀ c ∈ qr stack, ¬ c.Covers (stack + cnt + BitVec.ofNat 64 i)) :
    Iter boundary head exit cnt full L := by
  intro stack x n s hr hc hp hf hw hn hn'
  obtain ⟨f₁, t, ha, hr', hc', hq, hf', hw', hag⟩ := hseg stack x s hr hc hp hf hw
  have hnt : (Operand.mem (stack + cnt) : Operand 64).read t = BitVec.ofNat 64 (n + 1) := by
    rw [read_mem_agrees hag (fun i hi => hcnt stack i (by omega)), hn]
  obtain ⟨f₂, u, ha', hr'', hc'', hq', hf'', hw'', hnu, hag'⟩ :=
    hcount stack (doubleRound x) n t hr' hc' hq hf' hw' hnt hn'
  exact ⟨f₁ + f₂, u, ha.trans ha', hr'', hc'', hq', hf'', hw'', hnu,
    (hag.trans hag').mono (by
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact hsub stack c hc
      · exact hc)⟩

theorem Seg.congr [Bindings] {boundary : ReturnBoundary} {p q : BitVec 64}
    {scratch : BitVec 64 → List Component} {l₁ l₂ : List (Fin 16 × Loc)}
    {f g : Vector UInt32 16 → Vector UInt32 16} (h : Seg boundary p q scratch l₁ l₂ f)
    (hfg : ∀ x, f x = g x) : Seg boundary p q scratch l₁ l₂ g := by
  intro stack x s hr hc hp hf hw
  rw [← hfg]
  exact h stack x s hr hc hp hf hw

theorem doubleRound_eq (x : Vector UInt32 16) :
    doubleRound x = qroundRol (qroundRol (qroundRol (qroundRol (qroundRol (qroundRol (qroundRol
      (qroundRol x 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12) 2 7 8 13)
      3 4 9 14 := rfl

theorem repeat_succ' {α : Type} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f n (f a) = Nat.repeat f (n + 1) a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih]

theorem Loop.of_iter [Bindings] {boundary : ReturnBoundary} {head exit cnt : BitVec 64}
    {scratch : BitVec 64 → List Component} {L : List (Fin 16 × Loc)}
    (hiter : Iter boundary head exit cnt scratch L) : Loop boundary head exit cnt scratch L := by
  intro n
  induction n with
  | zero =>
    intro stack x s hr hc hp hf hw hn hn'
    obtain ⟨f, u, ha, hr', hc', hq, hf', hw', hnu, hag⟩ := hiter stack x 0 s hr hc hp hf hw hn hn'
    exact ⟨f, u, ha, hr', hc', by simpa using hq, hf', hw', hnu, hag⟩
  | succ m ih =>
    intro stack x s hr hc hp hf hw hn hn'
    obtain ⟨f, t, ha, hr', hc', hq, hf', hw', hnt, hag⟩ :=
      hiter stack x (m + 1) s hr hc hp hf hw hn hn'
    obtain ⟨f', u, ha', hr'', hc'', hq', hf'', hw'', hnu, hag'⟩ :=
      ih stack (doubleRound x) t hr' hc' (by simpa using hq) hf' hw' hnt (by omega)
    refine ⟨f + f', u, ha.trans ha', hr'', hc'', hq', hf'', ?_, hnu,
      (hag.trans hag').mono (by simp only [List.mem_append, or_self]; exact fun _ h => h)⟩
    rwa [repeat_succ'] at hw''

theorem slot_ne {stack o o' : BitVec 64} {i j : Nat} (hi : o.toNat + i < 2 ^ 64)
    (hj : o'.toNat + j < 2 ^ 64) (h : o.toNat + i ≠ o'.toNat + j) :
    stack + o + BitVec.ofNat 64 i ≠ stack + o' + BitVec.ofNat 64 j := by
  intro he
  rw [BitVec.add_assoc, BitVec.add_assoc] at he
  have := congrArg BitVec.toNat ((BitVec.add_right_inj stack).mp he)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

macro "cnt_tac" : tactic => `(tactic| (
  intro stack i hi
  simp only [mainQR, tailQR, regScratch, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  repeat' apply And.intro
  all_goals first
    | (intro c hm; exact absurd hm List.not_mem_nil)
    | (intro hcov; simp only [Component.Covers] at hcov; done)
    | (intro hcov
       simp only [Component.Covers] at hcov
       obtain ⟨j, hj, he⟩ := hcov
       exact slot_ne (by simp; omega) (by simp; omega) (by simp; omega) he)))

theorem mainRounds [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x100cd0 0x100e0e mainQR mainBase mainBase doubleRound :=
  Seg.congr ((((((((main0Seg boundary hb).seq (main1Seg boundary hb)).seq (main2Seg boundary hb)).seq
    (main3Seg boundary hb)).seq (main4Seg boundary hb)).seq (main5Seg boundary hb)).seq
    (main6Seg boundary hb)).seq (main7Seg boundary hb))
    (fun x => (doubleRound_eq x).symm)

theorem tailRounds [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Seg boundary 0x101180 0x1012d8 tailQR tailBase tailBase doubleRound :=
  Seg.congr ((((((((tail0Seg boundary hb).seq (tail1Seg boundary hb)).seq (tail2Seg boundary hb)).seq
    (tail3Seg boundary hb)).seq (tail4Seg boundary hb)).seq (tail5Seg boundary hb)).seq
    (tail6Seg boundary hb)).seq (tail7Seg boundary hb))
    (fun x => (doubleRound_eq x).symm)

theorem mainIter [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Iter boundary 0x100cd0 0x100e19 0x78 mainScratch mainBase :=
  Iter.of_seg (mainRounds boundary hb)
    (fun _ _ _ _ hr hc hp hf hw hn hn' => mainCount boundary hb hr hc hp hf hw hn hn')
    (fun _ _ hc => by simp only [mainScratch, List.mem_append]; exact Or.inl hc)
    (by cnt_tac)

theorem tailIter [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Iter boundary 0x101180 0x1012e3 0x58 tailScratch tailBase :=
  Iter.of_seg (tailRounds boundary hb)
    (fun _ _ _ _ hr hc hp hf hw hn hn' => tailCount boundary hb hr hc hp hf hw hn hn')
    (fun _ _ hc => by simp only [tailScratch, List.mem_append]; exact Or.inl hc)
    (by cnt_tac)

theorem mainLoop [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Loop boundary 0x100cd0 0x100e19 0x78 mainScratch mainBase :=
  Loop.of_iter (mainIter boundary hb)

theorem tailLoop [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    Loop boundary 0x101180 0x1012e3 0x58 tailScratch tailBase :=
  Loop.of_iter (tailIter boundary hb)

end ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
