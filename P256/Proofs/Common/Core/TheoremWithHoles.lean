import Lean

namespace P256.Proofs

open Lean Elab Command Term Meta

syntax (name := theoremBy)
  declModifiers "theorem_by " declId ppIndent(declSig) " := " ppIndent(term) : command

@[command_elab theoremBy]
def elabTheoremBy : CommandElab := fun stx => do
  let `($mods:declModifiers theorem_by $declId:declId $sig:declSig := $proof) := stx
    | throwUnsupportedSyntax
  let modifiers ← elabModifiers mods
  let (binders, typeStx) := expandDeclSig sig
  runTermElabM fun vars => do
    let scopeLevelNames ← Term.getLevelNames
    let ⟨_, declName, allUserLevelNames, docString?⟩ ←
      Term.expandDeclId (← getCurrNamespace) scopeLevelNames declId modifiers
    addDeclarationRangesFromSyntax declName stx declId
    Term.withDeclName declName <| Term.withLevelNames allUserLevelNames <|
      Term.elabBinders binders.getArgs fun xs => do
        Term.applyAttributesAt declName modifiers.attrs .beforeElaboration
        let type ← Term.elabType typeStx
        Term.synthesizeSyntheticMVarsNoPostponing
        let type ← elimMVarDeps (vars ++ xs) (← instantiateMVars type)
        let value ← Term.elabTermEnsuringType proof type
        Term.synthesizeSyntheticMVarsNoPostponing
        let type ← instantiateMVars type
        let value ← instantiateMVars value
        unless ← isProp type do
          throwErrorAt typeStx "theorem_by: the statement is not a proposition{indentExpr type}"
        let used := (collectFVars (collectFVars {} type) value)
        let (_, _, vars) ← removeUnused vars used
        let xs := vars ++ xs
        let type ← Term.levelMVarToParam (← mkForallFVars xs type)
        let value ← Term.levelMVarToParam (← mkLambdaFVars xs value)
        let type ← instantiateMVars type
        let value ← instantiateMVars value
        let usedParams := collectLevelParams (collectLevelParams {} type) value |>.params
        let levelParams ← match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
          | .ok ps => pure ps
          | .error msg => throwErrorAt stx msg
        let decl := Declaration.thmDecl { name := declName, levelParams, type, value }
        Term.ensureNoUnassignedMVars decl
        addDecl decl
        Term.applyAttributesAt declName modifiers.attrs .afterTypeChecking
        addDocString' declName binders docString?
        Term.applyAttributesAt declName modifiers.attrs .afterCompilation
        withSaveInfoContext do
          Term.addTermInfo' declId (← mkConstWithLevelParams declName) (isBinder := true)
        enableRealizationsForConst declName

end P256.Proofs
