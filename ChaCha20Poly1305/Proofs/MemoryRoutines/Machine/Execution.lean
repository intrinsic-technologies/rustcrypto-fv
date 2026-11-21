import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import X86Proofs.Program.Execution
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def AdvancesBlock [Bindings] (boundary : ReturnBoundary) (pre : RamState → Prop)
    (code : CodeMap) (effect : RamState → Effect) : Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      (effect s).Holds s t

namespace AdvancesBlock

variable [Bindings] {boundary : ReturnBoundary} {P pre₁ pre₂ : RamState → Prop}
  {code code₁ code₂ : CodeMap} {E e₁ e₂ E' : RamState → Effect}

theorem first (hStep : StepEffect pre₁ code₁ e₁)
    (hSub : ∀ x ∈ code₁, x ∈ code) (hPre : ∀ s, P s → pre₁ s)
    (hAvoid : ∀ s, P s → (e₁ s).Avoids code)
    (hBoundary : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code e₁ := by
  intro s hReady hCode hP
  obtain ⟨t, hAdvance, hReady', hEffect⟩ := hStep.advances hReady (hCode.mono hSub)
    (hPre s hP) (hBoundary s hP)
  exact ⟨1, t, hAdvance, hReady', hEffect.codeIn (hAvoid s hP) hCode, hEffect⟩

theorem seq_step (hBlock : AdvancesBlock boundary P code E)
    (hStep : StepEffect pre₂ code₂ e₂) (hLocal : Effect.Local e₂)
    (hSub : ∀ x ∈ code₂, x ∈ code)
    (hFull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hMid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code)
    (hBoundary : ∀ t, pre₂ t → (e₂ t).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code (Effect.seq E e₂) := by
  intro s hReady hCode hP
  obtain ⟨fuel, t, hAdvance, hReady', hCode', hEffect⟩ := hBlock s hReady hCode hP
  obtain ⟨hPre, hAvoid⟩ := hMid s t hP hEffect (hEffect.obsAfter (hFull s hP))
  obtain ⟨u, hAdvance', hReady'', hEffect'⟩ := hStep.advances hReady' (hCode'.mono hSub)
    hPre (hBoundary t hPre)
  exact ⟨fuel + 1, u, hAdvance.trans hAdvance', hReady'',
    hEffect'.codeIn hAvoid hCode', hEffect.seq hLocal (hFull s hP) hEffect'⟩

theorem seq_block (hBlock : AdvancesBlock boundary P code E)
    (hNext : AdvancesBlock boundary pre₂ code₂ e₂) (hLocal : Effect.Local e₂)
    (hSub : ∀ x ∈ code₂, x ∈ code)
    (hFull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hMid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code) :
    AdvancesBlock boundary P code (Effect.seq E e₂) := by
  intro s hReady hCode hP
  obtain ⟨fuel, t, hAdvance, hReady', hCode', hEffect⟩ := hBlock s hReady hCode hP
  obtain ⟨hPre, hAvoid⟩ := hMid s t hP hEffect (hEffect.obsAfter (hFull s hP))
  obtain ⟨fuel', u, hAdvance', hReady'', _, hEffect'⟩ := hNext t hReady' (hCode'.mono hSub) hPre
  exact ⟨fuel + fuel', u, hAdvance.trans hAdvance', hReady'',
    hEffect'.codeIn hAvoid hCode', hEffect.seq hLocal (hFull s hP) hEffect'⟩

theorem block_first
    (k : AdvancesBlock boundary P code e₁ → AdvancesBlock boundary P code E')
    (hStep : StepEffect pre₁ code₁ e₁) (hSub : ∀ x ∈ code₁, x ∈ code)
    (hPre : ∀ s, P s → pre₁ s) (hAvoid : ∀ s, P s → (e₁ s).Avoids code)
    (hBoundary : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code E' :=
  k (first hStep hSub hPre hAvoid hBoundary)

theorem block_then
    (k : AdvancesBlock boundary P code (Effect.seq E e₂) → AdvancesBlock boundary P code E')
    (hStep : StepEffect pre₂ code₂ e₂) (hLocal : Effect.Local e₂)
    (hSub : ∀ x ∈ code₂, x ∈ code)
    (hFull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hMid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code)
    (hBoundary : ∀ t, pre₂ t → (e₂ t).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code E → AdvancesBlock boundary P code E' :=
  fun hBlock ↦ k (hBlock.seq_step hStep hLocal hSub hFull hMid hBoundary)

theorem block_end
    (hEffect : ∀ s t, P s → (E s).Holds s t → (E' s).Holds s t) :
    AdvancesBlock boundary P code E → AdvancesBlock boundary P code E' := by
  intro hBlock s hReady hCode hP
  obtain ⟨fuel, t, hAdvance, hReady', hCode', hOld⟩ := hBlock s hReady hCode hP
  exact ⟨fuel, t, hAdvance, hReady', hCode', hEffect s t hP hOld⟩

end AdvancesBlock

macro "routine_run_begin " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  try (case sub => x86_sub)
  try (case pre => intro s hP; (first
    | exact hP.rip | exact ⟨hP.rip⟩ | exact hP | exact hP.1
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip
         (by x86_addr_obs) ?_
       x86_norm; x86_frame)
    | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip
         (by x86_addr_obs) ?_ ?_ <;>
       x86_norm <;> x86_frame)))
  try (case av => intro _ _; x86_avoid)
  case' k => x86_norm))

macro "routine_run_then " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case mid =>
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · first
      | exact hH.rip_of (by x86_norm)
      | exact ⟨hH.rip_of (by x86_norm)⟩
      | (refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
         x86_norm; x86_frame)
      | (refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_ <;>
         x86_norm <;> x86_frame)
    · x86_avoid)
  case' k => x86_norm))

syntax "routine_run_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| routine_run_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      apply AdvancesBlock.block_end
      intro s s' _ hH
      apply hH.weaken
      · x86_norm [$ls,*]
      · x86_norm [$ls,*]
      · intro i; cases i <;> x86_norm [$ls,*]
      · x86_norm [$ls,*]))

theorem ne_boundary_of_range {boundary : ReturnBoundary} {lo hi : Nat}
    (hb : boundary.rip.toNat < lo ∨ hi ≤ boundary.rip.toNat) {p : BitVec 64}
    (h1 : lo ≤ p.toNat) (h2 : p.toNat < hi) : p ≠ boundary.rip := by
  rintro rfl; omega

open Lean Meta Elab Tactic in
elab "code_sub" : tactic => do
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

macro "blk_boundary" : tactic => `(tactic| (
  intro _ _; exact ne_boundary_of_range (by assumption) (by x86_norm) (by x86_norm)))

syntax "blk_begin " term " using " ident " => " "(" tacticSeq ")" "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| blk_begin $t using $h => ($fr) ($bd)) => `(tactic| (
    refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
    case sub => first | x86_sub | code_sub
    case pre =>
      intro s $h:ident
      first
      | exact ($h).1
      | exact ⟨($h).1⟩
      | exact ($h).rip
      | exact ⟨($h).rip⟩
      | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s)
           (by first | exact ($h).1 | exact ($h).rip) (by x86_addr_obs) ?_
         ($fr))
      | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s)
           (by first | exact ($h).1 | exact ($h).rip) (by x86_addr_obs) ?_ ?_ <;> ($fr))
    case av =>
      intro s $h:ident
      first
      | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
      | (x86_avoid
         all_goals ($fr))
    case boundary => ($bd)
    case' k => skip))

syntax "blk_then " term " using " ident " => " "(" tacticSeq ")" "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| blk_then $t using $h => ($fr) ($bd)) => `(tactic| (
    refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
    case loc => x86_local
    case sub => first | x86_sub | code_sub
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
      intro s s' $h:ident hH hO
      refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · first
        | exact hH.rip_of (by first | rfl | x86_norm)
        | exact ⟨hH.rip_of (by first | rfl | x86_norm)⟩
        | (refine LoadPre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs) ?_
           ($fr))
        | (refine StorePre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs)
             ?_ ?_ <;> ($fr))
      · first
        | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
        | (x86_avoid
           all_goals ($fr))
    case boundary => ($bd)
    case' k => skip))

macro "blk_finish" : tactic => `(tactic| (intro h; exact h))

end ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
