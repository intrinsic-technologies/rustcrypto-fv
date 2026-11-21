import X86Proofs.Instructions.MovStore.Decode

set_option autoImplicit false

open X86Proofs

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode88_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_88 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_88, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode88_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_88 ip context).run s =
      (X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_88
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode88_run_of_memory context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_opcode88 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x88, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_88 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0_run_of_pfx_88_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (pfx modrm : UInt8) (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pfx :: 0x88 :: modrm :: rest))
    (hlow : s.RIP.toNat + (pfx :: 0x88 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) ctx).run (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP 3#64) ctx (modrmMod modrm)
        (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode88 _ _ _ _ hrex2 f2 (hmode 3),
    decodeLegacy0Opcode88_run_of_memory _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions
