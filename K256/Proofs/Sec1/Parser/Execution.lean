import K256.Proofs.Sec1.Affine.Contract
import K256.Proofs.Sec1.Parser.Packing.FromHeader
import K256.Proofs.Sec1.Parser.Frame.AfterDecode
import K256.Proofs.Sec1.Parser.CalleeMemory

namespace K256.Proofs.Sec1.Parser

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR K256.Proofs.Refine K256.Spec.Program

theorem parserCall_of_affine {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (affine : Affine.DecodeCall s bytes) :
    Wrapper.ParserCall s bytes := by
  rcases parserCall_or_validHeader call with done | ⟨regs, headerRegs, entry, pos, valid, len⟩
  · exact done
  let sp := s.regValue .rsp - 600
  let tag := bytes[0]'pos
  have head : bytes.data[0]? = some tag := by rw [Array.getElem?_eq_getElem (by exact pos)]; rfl
  obtain ⟨args, m, pack, packed⟩ := Packing.fromHeader call headerRegs pos valid len []
  have atEntry := Affine.entryAt_of_packing headerRegs packed
  obtain ⟨out, run, ret, rsp, kept, writes, decoded⟩ := affine args m pos valid len atEntry
  have resume := ParseSignature.exec_reaches_resume run Packing.affineResume [] (by rw [ret]; rfl)
  have arguments := ParseSignature.resume_arguments Packing.affineResume out
  dsimp only [StackFrame.resume] at arguments
  simp only [List.nil_append, StackFrame.resume, arguments] at resume
  have reached : Reaches Extracted.programImage .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s)
      .l1064f4 out.values out.store := entry.trans (pack.trans resume)
  have saved := affineSavedSlots call (packingSavedSlots call atEntry.frame) writes
  have tagBefore : memLoad m (sp + 4) 8 = tag.toBitVec := by
    rw [memLoad_8]
    apply congrArg UInt8.toBitVec
    have h := atEntry.input 0 (by decide)
    simpa only [BitVec.add_zero, head, Option.getD_some] using h
  apply Frame.parserCall_afterDecode call saved reached (congrArg (Value.get 64) rsp)
    (congrArg (Value.get 64) ((kept 3 (by decide)).trans atEntry.base))
    (congrArg (Value.get 64) ((kept 12 (by decide)).trans atEntry.r12))
    (congrArg (Value.get 64) ((kept 15 (by decide)).trans atEntry.r15)) ?_
    ((affineTagUnchanged call sp rfl writes).trans tagBefore) head valid
  · simp only [head, Option.getD_some] at decoded
    cases hp : K256.Spec.Secp256k1.decodePublicKey bytes <;> rw [hp] at decoded <;> exact decoded
  · intro i hi
    have eq : out.values[i] = (Wrapper.parserArgs s)[i] := (kept i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (atEntry.kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
    have initial := Wrapper.parserArgs_get s i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [ite_eq_right (show i.val ≠ 14 by omega), ite_eq_right (show i.val ≠ 7 by omega),
      ite_eq_right (show i.val ≠ 4 by omega)] at initial
    exact eq.trans initial

end K256.Proofs.Sec1.Parser
