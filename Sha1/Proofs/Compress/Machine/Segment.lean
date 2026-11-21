import Sha1.Proofs.Compress.Machine.Frame
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Compress.Machine.Execution

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program

abbrev Snapshot := (stack input : BitVec 64) → (H : Vector (BitVec 32) 5) →
  (M : Vector (BitVec 32) 16) → List Write

def Segment [Bindings] (boundary : ReturnBoundary) (p q : BitVec 64)
    (before after : Snapshot) : Prop :=
  ∀ stack input H M s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = p →
    FrameData stack input M s → Write.AllHold s (before stack input H M) →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = q ∧ FrameData stack input M t ∧
      Write.AllHold t (after stack input H M) ∧ AgreesExcept (scratchComponents stack) s t

theorem Segment.seq [Bindings] {boundary : ReturnBoundary} {p q r : BitVec 64}
    {before middle after : Snapshot} (hFirst : Segment boundary p q before middle)
    (hSecond : Segment boundary q r middle after) : Segment boundary p r before after := by
  intro stack input H M s hReady hCode hRip hFrame hWords
  obtain ⟨n, t, hAdvance, hReady', hCode', hRip', hFrame', hWords', hAgree⟩ :=
    hFirst stack input H M s hReady hCode hRip hFrame hWords
  obtain ⟨m, u, hAdvance', hReady'', hCode'', hRip'', hFrame'', hWords'', hAgree'⟩ :=
    hSecond stack input H M t hReady' hCode' hRip' hFrame' hWords'
  exact ⟨n + m, u, hAdvance.trans hAdvance', hReady'', hCode'', hRip'', hFrame'', hWords'',
    (hAgree.trans hAgree').mono (by simp only [List.mem_append, or_self]; exact fun _ h ↦ h)⟩

theorem Segment.of_block [Bindings] {boundary : ReturnBoundary} {p q : BitVec 64}
    {before after : Snapshot} {bytes : List UInt8}
    (effect : (stack input : BitVec 64) → Vector (BitVec 32) 5 →
      Vector (BitVec 32) 16 → RamState → Effect)
    (hBlock : ∀ stack input H M, AdvancesBlock boundary
      (fun s ↦ s.RIP = p ∧ FrameData stack input M s ∧ Write.AllHold s (before stack input H M))
      (codeRange p bytes) (effect stack input H M))
    (hSub : ∀ x ∈ codeRange p bytes, x ∈ Extracted.programImage)
    (hRip : ∀ stack input H M s t, s.RIP = p → FrameData stack input M s →
      Write.AllHold s (before stack input H M) → (effect stack input H M s).Holds s t →
      t.RIP = q)
    (hAgree : ∀ stack input H M s t, s.RIP = p → FrameData stack input M s →
      Write.AllHold s (before stack input H M) → (effect stack input H M s).Holds s t →
      AgreesExcept (scratchComponents stack) s t)
    (hWords : ∀ stack input H M s t, s.RIP = p → FrameData stack input M s →
      Write.AllHold s (before stack input H M) → (effect stack input H M s).Holds s t →
      Write.AllHold t (after stack input H M)) : Segment boundary p q before after := by
  intro stack input H M s hReady hCode hEntry hFrame hBefore
  obtain ⟨fuel, t, hAdvance, hReady', _, hEffect⟩ :=
    hBlock stack input H M s hReady (hCode.mono hSub) ⟨hEntry, hFrame, hBefore⟩
  have ha := hAgree stack input H M s t hEntry hFrame hBefore hEffect
  exact ⟨fuel, t, hAdvance, hReady', hFrame.codeIn_of_agrees ha hCode,
    hRip stack input H M s t hEntry hFrame hBefore hEffect, hFrame.of_agrees ha,
    hWords stack input H M s t hEntry hFrame hBefore hEffect, ha⟩

theorem FrameData.apart_stack_text {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s : RamState}
    (h : FrameData stack input M s) {p : BitVec 64} (offset length codeLen : Nat)
    (hBound : offset + length ≤ 160)
    (hLow : Extracted.textAddress.toNat ≤ p.toNat)
    (hHigh : p.toNat - Extracted.textAddress.toNat + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (stack + BitVec.ofNat 64 offset) length p codeLen := by
  have he : Extracted.textAddress +
      BitVec.ofNat 64 (p.toNat - Extracted.textAddress.toNat) = p := by
    apply BitVec.eq_of_toNat_eq
    have hd : p.toNat - Extracted.textAddress.toNat < 2 ^ 64 := by
      have := p.isLt
      omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd,
      Nat.add_sub_of_le hLow, Nat.mod_eq_of_lt p.isLt]
  have hCode := program_text_range (p.toNat - Extracted.textAddress.toNat) codeLen hHigh
  rw [he] at hCode
  intro i hi j hj heq
  apply h.code (offset + i) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, heq]
  exact hCode j hj

theorem FrameData.stack_tables {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s : RamState}
    (h : FrameData stack input M s) (offset length : Nat) (hb : offset + length ≤ 160) :
    ∀ i < length, ¬ InPageTables (stack + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  have hw := memoryWritable_slice h.writable offset length hb
  exact fun i hi ht ↦ hw.tables i hi ht

syntax "sha1_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sha1_norm $[[$ls,*]]? $[$loc]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| simp (config := { decide := true, implicitDefEqProofs := false }) only [x86_compose, $ls,*] $[$loc]?)
macro "sha1_avoid" : tactic => `(tactic| (
  apply Effect.avoids_codeRange
  try sha1_norm
  try simp only [x86_pre_simp]
  repeat' apply And.intro
  all_goals (try first
    | with_reducible assumption
    | x86_frame
    | with_reducible_and_instances (exact RangeApart.sub0 (by assumption) _ (by decide +kernel)))))

open Lean Meta Elab Tactic in
elab "sha1_frame_prepare " hP:ident : tactic => do
  let g ← getMainGoal
  let some hd := (← g.getDecl).lctx.findFromUserName? hP.getId | throwError "no {hP}"
  let fs ← X86Proofs.Carry.splitHypAux (mkFVar hd.fvarId) 0
  for f in fs do
    let g ← getMainGoal
    let ty ← g.withContext do whnf (← inferType (mkFVar f))
    if ty.isAppOfArity ``Eq 3 then
      let g' ← g.assert (← mkFreshUserName `hSnapshot) ty (mkFVar f)
      let (f', g'') ← g'.intro1P
      replaceMainGoal [g'']
      X86Proofs.Carry.simpHyps
        (← `(tactic| simp (config := { decide := true, implicitDefEqProofs := false }) only [x86_compose])) #[f']
  evalTactic (← `(tactic| (
    have hStack : (Operand.reg 4 : Operand 64).read _ = _ :=
      (by assumption : FrameData _ _ _ _).stackPointer
    sha1_norm at hStack)))

open Lean Meta Elab Tactic in
elab "sha1_frame_norm" : tactic => withMainContext do
  let mut args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← whnfR d.type
    if ty.isAppOfArity ``Eq 3 then
      let α := ty.getAppArgs[0]!
      if ← isDefEq α (mkApp (mkConst ``BitVec) (mkNatLit 64)) then
        args := args.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):ident))
  evalTactic (← `(tactic| simp only [$args,*]))

macro "sha1_frame" : tactic => `(tactic| (
  try sha1_norm
  try sha1_frame_norm
  try simp only [← BitVec.add_assoc]
  first
  | with_reducible_and_instances
      exact FrameData.readable_stack (by assumption) _ _ (by decide +kernel)
  | with_reducible_and_instances
      exact FrameData.readable_input (by assumption) _ _ (by decide +kernel)
  | with_reducible_and_instances
      simpa only [BitVec.add_zero] using
        FrameData.readable_stack (by assumption) 0 _ (by decide +kernel)
  | with_reducible_and_instances
      simpa only [BitVec.add_zero] using
        FrameData.readable_input (by assumption) 0 _ (by decide +kernel)
  | with_reducible_and_instances
      exact memoryWritable_slice
        (by assumption : FrameData _ _ _ _).writable _ _ (by decide +kernel)
  | with_reducible_and_instances
      simpa only [BitVec.add_zero] using memoryWritable_slice
        (by assumption : FrameData _ _ _ _).writable 0 _ (by decide +kernel)
  | with_reducible_and_instances
      exact FrameData.apart_stack_text (by assumption) _ _ _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | with_reducible_and_instances
      simpa only [BitVec.add_zero] using FrameData.apart_stack_text (by assumption) 0 _ _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | with_reducible_and_instances
      exact FrameData.stack_tables (by assumption) _ _ (by decide +kernel)
  | with_reducible_and_instances
      simpa only [BitVec.add_zero] using
        FrameData.stack_tables (by assumption) 0 _ (by decide +kernel)))

open Lean Meta Elab Tactic in
elab "sha1_run_boundary" : tactic => do
  evalTactic (← `(tactic| sha1_norm))
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let lhs? (e : Expr) : Option Expr :=
      if e.isAppOfArity ``Ne 3 then some e.getAppArgs[1]!
      else if e.isAppOfArity ``Not 1 && e.appArg!.isAppOfArity ``Eq 3 then
        some e.appArg!.getAppArgs[1]!
      else none
    let some pc := lhs? target | throwError "expected an instruction boundary goal"
    let some ⟨_, pcVal⟩ ← getBitVecValue? pc | throwError "expected a literal instruction address"
    for hd in ← getLCtx do
      if !hd.type.isForall then continue
      let offset? ← forallBoundedTelescope hd.type (some 2) fun xs body => do
        if xs.size != 2 then return none
        unless ← isDefEq (← inferType xs[0]!) (mkConst ``Nat) do return none
        let some lhs := lhs? body | return none
        let args := lhs.getAppArgs
        if args.size < 2 then return none
        let some ⟨_, start⟩ ← getBitVecValue? args[args.size - 2]! | return none
        return some ((pcVal.toNat + 2 ^ 64 - start.toNat) % 2 ^ 64)
      if let some off := offset? then
        let saved ← saveState
        try
          evalTactic (← `(tactic| exact $(mkIdent hd.userName):ident
            $(quote off) (by decide +kernel)))
          return
        catch _ => saved.restore
    throwError "no boundary range hypothesis covers this instruction"

open Lean Meta Elab Tactic in
elab "sha1_run_sub" : tactic => do
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

macro "sha1_run_begin " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => first | x86_sub | sha1_run_sub
  case pre =>
    intro s hP
    first
    | exact hP.1
    | exact ⟨hP.1⟩
    | (sha1_frame_prepare hP
       first
       | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
            (by x86_addr_obs) ?_
          sha1_frame)
       | (refine storePre_of_holds
            (Effect.start_holds s) (Effect.start_obs s) hP.1 (by x86_addr_obs) ?_ ?_ <;>
          sha1_frame))
  case av =>
    intro s hP
    sha1_avoid
    all_goals (sha1_frame_prepare hP; sha1_frame)
  case boundary => intro _ _; sha1_run_boundary
  case' k => skip))

macro "sha1_run_then " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => first | x86_sub | sha1_run_sub
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
      | exact hH.rip_of (by first | rfl | sha1_norm)
      | exact ⟨hH.rip_of (by first | rfl | sha1_norm)⟩
      | (sha1_frame_prepare hP
         first
         | (refine LoadPre.of_holds hH (hO true) (by first | rfl | sha1_norm) (by x86_addr_obs) ?_
            sha1_frame)
         | (refine storePre_of_holds
              hH (hO true) (by first | rfl | sha1_norm) (by x86_addr_obs) ?_ ?_ <;> sha1_frame))
    · first
      | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
      | (sha1_avoid
         all_goals (sha1_frame_prepare hP; sha1_frame))
  case boundary => intro _ _; sha1_run_boundary
  case' k => skip))

macro "sha1_run_begin_manual " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => first | x86_sub | sha1_run_sub
  case boundary => intro _ _; sha1_run_boundary
  case' k => skip))

macro "sha1_run_then_manual " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => first | x86_sub | sha1_run_sub
  case full =>
    first
    | (intro s _
       apply Effect.Local.full
       repeat' first
         | (solve | x86_local)
         | apply Effect.Local.seq
       done)
    | x86_full
  case boundary => intro _ _; sha1_run_boundary
  case' k => skip))

syntax "sha1_run_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sha1_run_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| first
      | (intro h; exact h)
      | (
      apply AdvancesBlock.block_end
      intro s s' _ hH
      apply hH.weaken
      · sha1_norm [$ls,*]
      · sha1_norm [$ls,*]
        all_goals repeat' first | exact Or.inl rfl | apply And.intro | apply Or.inr | rfl
      · intro i; cases i <;> sha1_norm [$ls,*]
      · sha1_norm [$ls,*]))

end Sha1.Proofs.Compress.Machine
