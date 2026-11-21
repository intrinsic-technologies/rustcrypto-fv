import X86Proofs.Step.Decode

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem selectLegacy0OpcodeD3_run_of_shr_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_D3 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_D3, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0OpcodeD3_run_of_shr_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D3 ip context).run s =
      (X86.Instructions.SHR_GPRv_CL (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D3
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD3_run_of_shr_register context a b c d e f modrm hmod hreg)

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount
