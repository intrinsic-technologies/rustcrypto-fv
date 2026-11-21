import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem selectLegacy0Opcode80_run_of_r0_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0Opcode80_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADD_GPR8_IMMb_80r0 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r0_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_80_r0 [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP (rex :: 0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.ADD_GPR8_IMMb_80r0 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x80, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow' 2 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode80 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode80_run_of_r0_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

end P256.Proofs.Common.Instructions.AddByte
