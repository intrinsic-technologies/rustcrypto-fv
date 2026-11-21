import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.Ecdh.Decode.Convert

open X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Refine K256.Proofs.Lift Ecdh.LIR

theorem convertBarrier {b : Values Value Reg.count} {m : Ram} {sp addr : BitVec 64}
    (rsp : b[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp - 1) 1)
    (slot : Readable m sp 8) (ret : memLoad m sp 64 = addr) (retLow : addr.toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,b,m⟩, []⟩ out ∧
      out.tag = some ⟨64,addr⟩ ∧ out.values[4] = ⟨64,sp+8⟩ ∧
      out.values[0] = ⟨64, ((b[7].get 64).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame m out.store [⟨(sp - 1).toNat,1⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        out.values[i] = b[i] := by
  obtain ⟨out, step, tag, hsp, flag, frame, kept⟩ := Sec1.Serialize.choiceBlock
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l127d50 x hx))
    rsp stack slot (by simpa only [ret] using retLow)
  refine ⟨out, .done ?_, by simpa only [ret] using tag, hsp, flag, frame, kept⟩
  let f : Sec1.LIR.Label → Label := fun _ => .l127d50
  have blocks : Generate.Serialize.Relabel.block f (Sec1.LIR.program.blocks .l127d50) =
      program.blocks .l127d50 := by rfl
  have run : program.runBlock (dialect Extracted.programImage) ⟨.l127d50,b,m⟩ = .returned out := by
    change (program.blocks _).eval _ _ _ = _
    rw [← blocks, Generate.Serialize.Relabel.eval_block]
    exact congrArg (Generate.Serialize.Relabel.transfer f) step
  simp only [Program.step, run, Transfer.next]

end K256.Proofs.Ecdh.Decode.Convert
