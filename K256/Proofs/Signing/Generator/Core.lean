import K256.Proofs.Generate.Generator.Multiply.Core

namespace K256.Proofs.Signing.Generator

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

open K256.Proofs.Generate K256.Proofs.Generate.Generator K256.Proofs.Generate.Generator.Multiply
  Standards.SECG.DomainParameters.Secp256k1

structure CoreEntry (fr : Activation) (a : Registers) (d : Nat) : Prop where
  atoms : Atom.All Extracted.programImage a fr.original (Fn11c880.frameAt .l11c880 fr)
  loaded : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  low : fr.low = fr.rsp - 0xed8
  room : 0xed8 ≤ fr.rsp.toNat
  high : fr.rsp.toNat + 6320 ≤ 2^32
  pairPtr : fr.rsi = fr.rsp + 0xf10
  tablePtr : fr.rcx = fr.rsp + 0xfa8
  digitPtr : fr.r9 = fr.rsp + 16
  outputAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat
  pairCount : fr.rdx = 1
  tableCount : fr.r8 = 1
  digitCount : memLoad fr.original (fr.rsp + 8) 64 = 1
  countRead : Readable fr.original (fr.rsp + 8) 8
  pairRead : Readable fr.original fr.rsi 152
  tableWrite : Writable Extracted.programImage fr.original fr.rcx 1920
  digitWrite : Writable Extracted.programImage fr.original fr.r9 66
  outputWrite : Writable Extracted.programImage fr.original fr.rdi 120
  generator : ∀ i : Fin 15, memLoad fr.original (wordAddr fr.rsi 64 i.val) 64 =
    memLoad fr.original (wordAddr 0x202bc8 64 i.val) 64
  scalar : WordsAt fr.original (fr.rsi + 120) 64 (scalarWords d)

open Lean Meta Elab Command in
private def useOutputSeparation (proof : Expr) : CommandElabM Expr := liftTermElabM do
  let proof := proof.replace fun
    | .const ``Multiply.CoreEntry ls => some (.const ``CoreEntry ls)
    | _ => none
  lambdaTelescope proof fun args body => do
    for arg in args do
      let type ← inferType arg
      if type.isAppOf ``CoreEntry then
        let separated ← mkAppM ``CoreEntry.outputAbove #[arg]
        let required ← inferType separated
        let body := body.replace fun
          | .letE n t _ b nondep => if t == required then some (.letE n t separated b nondep) else none
          | _ => none
        return ← mkLambdaFVars args body
    throwError "generator entry missing from window loop"

open Lean Elab Command in
private partial def specializeCoreProof (name : Name) : CommandElabM Name := do
  let multiply := `K256.Proofs.Generate.Generator.Multiply
  let signing := `K256.Proofs.Signing.Generator.Specialized
  let source := ``Multiply.CoreEntry
  let target := `K256.Proofs.Signing.Generator.CoreEntry
  if name == source then return target
  unless multiply.isPrefixOf (privateToUserName name) do return name
  let info ← getConstInfo name
  if source.isPrefixOf name then
    let replacement := name.replacePrefix source target
    if (← getEnv).contains replacement then return replacement
  let specialized := if isPrivateName name then signing ++ name else name.replacePrefix multiply signing
  if (← getEnv).contains specialized then return specialized
  unless info.type.getUsedConstants.contains source do return name
  let .thmInfo theoremInfo := info | throwError "expected a theorem at {name}"
  let proof ← if name == ``Multiply.windowLoop then useOutputSeparation theoremInfo.value
    else pure theoremInfo.value
  let mut names : NameMap Name := {}
  for dep in proof.getUsedConstants ++ info.type.getUsedConstants do
    let dep' ← specializeCoreProof dep
    if dep' != dep then names := names.insert dep dep'
  let relocate (e : Expr) := e.replace fun
    | .const n ls => names.find? n |>.map fun n' => .const n' ls
    | _ => none
  try liftCoreM <| addDecl (.thmDecl { theoremInfo with
    name := specialized, all := [specialized]
    type := relocate theoremInfo.type, value := relocate proof })
  catch e => throwError "specializing {name}: {e.toMessageData}"
  return specialized

set_option Elab.async false in
open Lean Elab Command in
run_cmd do
  discard <| specializeCoreProof ``Multiply.coreExecution

end K256.Proofs.Signing.Generator
