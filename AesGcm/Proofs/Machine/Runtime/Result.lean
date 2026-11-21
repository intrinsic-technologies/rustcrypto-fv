import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

def CallResultContract (P : Lifted) (code : CodeMap) (label : P.Label) (frame : FrameInfo)
    (footprint : Activation → List MemoryRegion)
    (pre : Activation → Ram → Prop) (post : Activation → Output Value Ram Reg.count → Prop) : Prop :=
  ∀ (fr : Activation) (loc : P.Location), loc.label = label →
    loc.store = fr.original →
    Atom.All code loc.arguments loc.store (frame.entryAtoms fr) →
    GPRsTyped loc.arguments →
    pre fr loc.store →
    ∃ output : Output Value Ram Reg.count,
      P.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store (frame.doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame fr.original output.store (fr.region :: footprint fr) ∧
      post fr output

theorem CallResultContract.toCallContract
    {P : Lifted} {code : CodeMap} {label : P.Label} {frame : FrameInfo}
    {footprint : Activation → List MemoryRegion} {pre : Activation → Ram → Prop}
    {post : Activation → Output Value Ram Reg.count → Prop} {memoryPost : Activation → Ram → Prop}
    (h : CallResultContract P code label frame footprint pre post)
    (hpost : ∀ fr output, post fr output → memoryPost fr output.store) :
    CallContract P code label frame footprint pre memoryPost := by
  intro fr loc hl hm he ht hp
  obtain ⟨output, hx, hr, hf, htypes, hw, ho⟩ := h fr loc hl hm he ht hp
  exact ⟨output, hx, hr, hf, htypes, hw, hpost fr output ho⟩

end AesGcm.Proofs.Machine.Runtime
