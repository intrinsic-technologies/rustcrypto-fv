import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Generate.LIR.Fn127d50.Frame
import K256.Proofs.ParseSignature.BlackBox
import K256.Proofs.ParseSignature.Compare

namespace K256.Proofs.Generate.Generator.Sample

open Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

private def target : K256.Proofs.LIR.Label → Option Generate.LIR.Label
  | .l127d50 => some .l127d50
  | .l127f50 => some .l127f50
  | .l127f55 => some .l127f55
  | .l127f5a => some .l127f5a
  | .l127f70 => some .l127f70
  | .l127f8a => some .l127f8a
  | .l127f9a => some .l127f9a
  | .l127fa9 => some .l127fa9
  | _ => none

set_option maxRecDepth 4096 in
private theorem matchesBlocks (a : K256.Proofs.LIR.Label) (b : Generate.LIR.Label)
    (h : target a = some b) :
    Serialize.Relabel.block target (K256.Proofs.LIR.program.blocks a) =
      Serialize.Relabel.block some (Generate.LIR.program.blocks b) := by
  rcases a with ⟨a⟩
  cases a <;> cases h <;> rfl

def Call (code : CodeMap) (label : Generate.LIR.Label) (frame : FrameInfo)
    (fr : Activation) (footprint : List MemoryRegion) (post : Output Value Ram Reg.count → Prop) : Prop :=
  ∀ args : Values Value Reg.count, Atom.All code args fr.original (frame.entryAtoms fr) →
    ∃ out, Generate.LIR.program.Exec (dialect code) ⟨⟨label, args, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (frame.doneAtoms fr) ∧
      RamWriteFrame fr.original out.store (fr.region :: footprint) ∧
      ParseSignature.ArgumentWidths out.values ∧ post out

private theorem transferCall {code : CodeMap} {a : K256.Proofs.LIR.Label} {b : Generate.LIR.Label}
    {frame : FrameInfo} {fr : Activation} {footprint : List MemoryRegion}
    {post : Output Value Ram Reg.count → Prop}
    (h : target a = some b) (run : ParseSignature.Call code a frame fr footprint post) :
    Call code b frame fr footprint post := by
  intro args atoms
  obtain ⟨out, steps, result⟩ := run args atoms
  refine ⟨out, Serialize.Relabel.exec matchesBlocks steps ?_, result⟩
  simp only [Serialize.Relabel.state, Serialize.Relabel.location, h, List.map_nil]

theorem blackBox_call {code : CodeMap} (hcode : ∀ x ∈ Generate.LIR.fnCode, x ∈ code)
    (fr : Activation) :
    Call code .l127d50 Generate.LIR.Fn127d50.frameInfo fr [] fun out =>
      out.values[0] = ⟨64, (fr.rdi.setWidth 8).zeroExtend 64⟩ :=
  transferCall (a := .l127d50) rfl (ParseSignature.blackBox_call hcode fr)

theorem ctEq_call {code : CodeMap} (hcode : ∀ x ∈ Generate.LIR.fnCode, x ∈ code)
    (fr : Activation) (hn : fr.rsi = 4) (hm : fr.rcx = 4)
    (hl : Readable fr.original fr.rdi 32) (hr : Readable fr.original fr.rdx 32) :
    Call code .l127f50 K256.Proofs.LIR.Fn127f50.frameInfo fr [] fun out =>
      out.store = fr.original ∧
      (out.values[0].get 8 = 1 ↔ ∀ i < 4,
        memLoad fr.original (wordAddr fr.rdi 64 i) 64 =
        memLoad fr.original (wordAddr fr.rdx 64 i) 64) ∧
      (out.values[0].get 8 = 0 ∨ out.values[0].get 8 = 1) :=
  transferCall (a := .l127f50) rfl (ParseSignature.ctEq_call hcode fr hn hm hl hr)

end K256.Proofs.Generate.Generator.Sample
