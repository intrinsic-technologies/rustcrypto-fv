import K256.Proofs.Sec1.Parser.Header
import K256.Proofs.Sec1.Parser.Packing.CopyInput
import K256.Proofs.Sec1.Parser.Affine

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

structure EntryAt (s : RamState) (bytes : ByteArray) (args : Values Value Reg.count) (mem : Ram) : Prop where
  stack : args[4] = ⟨64, s.regValue .rsp - 600 - 8⟩
  source : args[6] = ⟨64, s.regValue .rsp - 600 + 4⟩
  output : args[7] = ⟨64, s.regValue .rsp - 600 + 160⟩
  base : args[3] = ⟨64, s.regValue .rsp - 600 + 160⟩
  r12 : args[12] = ⟨64, 0⟩
  r14 : args[14] = ⟨64, s.regValue .rdx⟩
  r15 : args[15] = ⟨64, s.regValue .rsp - 112⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [5, 13, 22, 39, 50, 51] → args[i] = (Wrapper.parserArgs s)[i]
  input : ∀ i < 65, memByte mem (s.regValue .rsp - 600 + 4 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0
  ret : memLoad mem (s.regValue .rsp - 600 - 8) 64 = 0x1064f4
  frame : RamWriteFrame (Parser.headerMemory s) mem [Parser.Packing.packingWindow (s.regValue .rsp - 600)]

theorem entryAt_of_packing {s : RamState} {bytes : ByteArray} {args regs : Values Value Reg.count} {mem : Ram}
    (header : Parser.HeaderRegisters s regs)
    (packed : let sp := s.regValue .rsp - 600
      args[3] = ⟨64, sp + 160⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧
      args[6] = ⟨64, sp + 4⟩ ∧ args[7] = ⟨64, sp + 160⟩ ∧ args[12] = ⟨64, 0⟩ ∧
      args[14] = ⟨64, s.regValue .rdx⟩ ∧ args[15] = ⟨64, s.regValue .rsp - 112⟩ ∧
      (s.regValue .rdx).toNat = bytes.size ∧ (sp - 8).toNat % 16 = 8 ∧
      (∀ i < 65, memByte mem (sp + 4 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0) ∧
      memLoad mem (sp - 8) 64 = 0x1064f4 ∧ RamWriteFrame (Parser.headerMemory s) mem [Parser.Packing.packingWindow sp] ∧
      (∀ r ∈ [5, 13, 22, 39, 50, 51], ∀ hr : r < Reg.count, args[r] = regs[r])) :
    EntryAt s bytes args mem := by
  obtain ⟨base, sp, src, dst, r12, r14, r15, _, _, input, ret, frame, kept⟩ := packed
  refine ⟨sp, src, dst, base, r12, r14, r15, ?_, input, ret, frame⟩
  intro i hi
  exact (kept i.val hi i.isLt).trans (header.kept i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega))

def ReturnAt (sp : BitVec 64) (bytes : ByteArray) (args : Values Value Reg.count) (mem : Ram)
    (out : Output Value Ram Reg.count) : Prop :=
  out.tag = some ⟨64, 0x1064f4⟩ ∧ out.values[4] = ⟨64, sp⟩ ∧
  (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
  RamWriteFrame mem out.store [⟨(sp - 1200).toNat, 1192⟩, ⟨(sp + 160).toNat, 89⟩] ∧
  (if bytes.data[0]?.getD 0 = 0 then memLoad out.store (sp + 248) 8 = 1 else
    match K256.Spec.Secp256k1.decodePublicKey bytes with
    | none => memLoad out.store (sp + 248) 8 = 0
    | some p => memLoad out.store (sp + 248) 8 = 1 ∧ Parser.PublicKeyAt out.store (sp + 160) p)

def DecodeCall (s : RamState) (bytes : ByteArray) : Prop :=
  ∀ (args : Values Value Reg.count) (mem : Ram) (pos : 0 < bytes.size)
    (valid : Parser.validTag (bytes[0]'pos).toBitVec),
    s.regValue .rdx = Parser.lengthTable.get ⟨(bytes[0]'pos).toNat, Parser.validTag_lt valid⟩ →
    EntryAt s bytes args mem →
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480, args, mem⟩, []⟩ out ∧
      ReturnAt (s.regValue .rsp - 600) bytes args mem out

end K256.Proofs.Sec1.Affine
