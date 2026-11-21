import K256.Proofs.Verify.Transfer.Signature.Relabel
import K256.Proofs.Verify.Core.Scalars.State
import K256.Proofs.Verify.LIR.Fn127d70.Frame
import K256.Proofs.Verify.Transfer.SignatureWords
import K256.Proofs.ParseSignature.Fill
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR ParseSignature Generate.Generator.Multiply

theorem fillScalar {fr : Activation} {a : Registers}
    (entry : Atom.All Extracted.programImage a fr.original (Fn127d70.frameAt .l127d70 fr))
    (hn : fr.rsi = 32) (hk : fr.rcx = 4) (hwid : fr.r8 = 256)
    (hr : Readable fr.original fr.rdi 32) (hw : Writable Extracted.programImage fr.original fr.rdx 32)
    (hin : Outside [callStack fr] fr.rdi 32) (hout : Outside [callStack fr] fr.rdx 32)
    (hdisj : Outside [buffer fr.rdx 32] fr.rdi 32)
    (hslot : Outside [buffer fr.rdx 32] 0x203dd0 8) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l127d70,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn127d70.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, buffer fr.rdx 32] ∧ ArgumentWidths out.values ∧
      out.values[0].get 8 = 255 ∧ WordsAt out.store fr.rdx 64 (scalarWords (scalarValue fr.original fr.rdi)) := by
  obtain ⟨old,run,tag,done_,frame,widths,status,limbs⟩ :=
    fill_call Common.fnCode_subset_programImage fr hn hk hwid hr hw hin hout hdisj hslot a entry
  obtain ⟨out,exec,mem,ret,regs⟩ :=
    Verify.Transfer.Signature.transferAt (y := .l127d70) (by decide +kernel) run
  refine ⟨out,exec,ret.trans tag,?_,mem ▸ frame,?_,(congrArg (Value.get 8) (regs 0 (by decide))).trans status,
    mem ▸ Verify.Transfer.wordsAt_of_scalarLimbsAt limbs⟩
  · change Atom.All Extracted.programImage old.values old.store (Fn127d70.doneAt fr) at done_
    simp only [Fn127d70.doneAt, Atom.All, Atom.Holds] at done_ ⊢
    simpa only [regs 4 (by decide), regs 22 (by decide), regs 3 (by decide), regs 5 (by decide),
      regs 12 (by decide), regs 13 (by decide), regs 14 (by decide), regs 15 (by decide),
      regs 39 (by decide), regs 50 (by decide), regs 51 (by decide)] using done_
  · intro i hi
    rw [regs i (by
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)]
    exact widths i hi

end K256.Proofs.Verify.Core
