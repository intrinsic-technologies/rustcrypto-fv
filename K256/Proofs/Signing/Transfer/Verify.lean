import K256.Proofs.Signing.Transfer.Verify.Blocks

namespace K256.Proofs.Signing.Transfer

open X86.Machine X86.UserProcess X86Proofs CFG Lift Generate.Serialize VerifyProgram

def sharedLabels : List (Verify.LIR.Label × Signing.LIR.Label) :=
  [(.l106dd0,.l106dd0), (.l10ee80,.l10ee80), (.l10fe50,.l10fe50),
   (.l1054a6,.l1054a6), (.l105758,.l105758), (.l105886,.l105886),
   (.l100a40,.l100a40), (.l100ab0,.l100ab0), (.l100ac0,.l100ac0),
   (.l1058d0,.l1058d0), (.l105870,.l105870), (.l105d62,.l105d62),
   (.l104c90,.l104c90), (.l105e11,.l105e11)]

private abbrev VerifyState := State Value Ram Verify.LIR.Label signature Reg.count
private abbrev SigningState := State Value Ram Signing.LIR.Label signature Reg.count

private theorem verifyStep {code : CodeMap} {x : VerifyState} {y : SigningState}
    (h : Relabel.state target x = Relabel.state some y) :
    Relabel.outcome target (Verify.LIR.program.step (dialect code) x) =
      Relabel.outcome some (Signing.LIR.program.step (dialect code) y) := by
  rcases x with ⟨⟨a,u,m⟩,st⟩
  rcases y with ⟨⟨b,v,n⟩,tt⟩
  simp only [Relabel.state, Relabel.location, State.mk.injEq, Location.mk.injEq] at h
  obtain ⟨⟨hl, rfl, rfl⟩, hs⟩ := h
  simp only [Program.step, Program.runBlock, ← Relabel.next_transfer, ← Relabel.eval_block,
    blocks a b hl, hs]

private theorem verifyTrace {code : CodeMap} {x z : VerifyState}
    (run : (Verify.LIR.program.sem (dialect code)).Reaches x z)
    {y : SigningState} (entry : Relabel.state target x = Relabel.state some y) :
    ∃ w : SigningState, (Signing.LIR.program.sem (dialect code)).Reaches y w ∧
      Relabel.state target z = Relabel.state some w := by
  induction run generalizing y with
  | refl => exact ⟨y, .refl _, entry⟩
  | step hs _ ih =>
    have eq := verifyStep (code := code) entry
    change Verify.LIR.program.step (dialect code) _ = .next _ at hs
    rw [hs] at eq
    cases e : Signing.LIR.program.step (dialect code) y <;> rw [e] at eq
    case next =>
      obtain ⟨w, run, finish⟩ := ih (Outcome.next.inj eq)
      exact ⟨w, .step e run, finish⟩
    all_goals cases eq

private theorem sameEmptyState {y : SigningState} {dst : Signing.LIR.Label}
    {b : Values Value Reg.count} {n : Ram}
    (h : Relabel.state some y = Relabel.state some (⟨⟨dst,b,n⟩,[]⟩ : SigningState)) :
    y = ⟨⟨dst,b,n⟩,[]⟩ := by
  rcases y with ⟨⟨l,a,m⟩,stack⟩
  cases stack <;> simp_all only [Relabel.state, Relabel.location, List.map_nil, List.map_cons,
    State.mk.injEq, Location.mk.injEq, Option.some.injEq, List.cons_ne_nil, and_true, and_false]

private theorem sharedTarget {src dst} (entry : (src, dst) ∈ sharedLabels) :
    target src = some dst := by
  suffices allShared : ∀ pair ∈ sharedLabels, target pair.1 = some pair.2 from
    allShared (src, dst) entry
  simp only [sharedLabels, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  repeat' first | rfl | constructor

private theorem mappedEmptyState {src dst} (entry : target src = some dst)
    {a : Values Value Reg.count} {m : Ram} :
    Relabel.state target (⟨⟨src, a, m⟩, []⟩ : VerifyState) =
      Relabel.state some (⟨⟨dst, a, m⟩, []⟩ : SigningState) := by
  simp only [Relabel.state, Relabel.location, entry, List.map_nil]

theorem verifyExecAt {src dst} (entry : VerifyProgram.target src = some dst)
    {code : CodeMap} {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Verify.LIR.program.Exec (dialect code) ⟨⟨src, a, m⟩, []⟩ out) :
    Signing.LIR.program.Exec (dialect code) ⟨⟨dst, a, m⟩, []⟩ out :=
  Relabel.exec blocks run (mappedEmptyState entry)

theorem verifyReachesAt {src dst src' dst'} (entry : VerifyProgram.target src = some dst)
    (finish : VerifyProgram.target src' = some dst')
    {code : CodeMap} {a b : Values Value Reg.count} {m n : Ram}
    (run : (Verify.LIR.program.sem (dialect code)).Reaches ⟨⟨src, a, m⟩, []⟩ ⟨⟨src', b, n⟩, []⟩) :
    (Signing.LIR.program.sem (dialect code)).Reaches ⟨⟨dst, a, m⟩, []⟩ ⟨⟨dst', b, n⟩, []⟩ := by
  obtain ⟨w, trace, reached⟩ := verifyTrace run (mappedEmptyState entry)
  rwa [sameEmptyState (reached.symm.trans (mappedEmptyState finish))] at trace

theorem verifyExec {src dst} (entry : (src,dst) ∈ sharedLabels)
    {code : CodeMap} {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Verify.LIR.program.Exec (dialect code) ⟨⟨src,a,m⟩,[]⟩ out) :
    Signing.LIR.program.Exec (dialect code) ⟨⟨dst,a,m⟩,[]⟩ out :=
  verifyExecAt (sharedTarget entry) run

theorem verifyReaches {src dst src' dst'} (entry : (src,dst) ∈ sharedLabels)
    (finish : (src',dst') ∈ sharedLabels)
    {code : CodeMap} {a b : Values Value Reg.count} {m n : Ram}
    (run : (Verify.LIR.program.sem (dialect code)).Reaches ⟨⟨src,a,m⟩,[]⟩ ⟨⟨src',b,n⟩,[]⟩) :
    (Signing.LIR.program.sem (dialect code)).Reaches ⟨⟨dst,a,m⟩,[]⟩ ⟨⟨dst',b,n⟩,[]⟩ :=
  verifyReachesAt (sharedTarget entry) (sharedTarget finish) run

theorem attemptCalleesCovered :
    ∀ pair : Verify.LIR.Label × Signing.LIR.Label,
      pair ∈ [(.l109e60, .l109e60), (.l10a220, .l10a220), (.l10a280, .l10a280),
        (.l127d50, .l127d50), (.l127d70, .l127d70), (.l109f80, .l109f80),
        (.l109d80, .l109d80), (.l120350, .l120350), (.l109f70, .l109f70),
        (.l10a2e0, .l10a2e0), (.l109f60, .l109f60), (.l103450, .l103450),
        (.l109e30, .l109e30), (.l1203b0, .l1203b0), (.l10a170, .l10a170)] →
      VerifyProgram.target pair.1 = some pair.2 := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' first | rfl | constructor

end K256.Proofs.Signing.Transfer
