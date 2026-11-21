import X86Proofs.Instructions.MovStore.Decode

namespace Md5.Proofs.Buffered.Update.Counter

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem selectLegacy0OpcodeFF_run_of_inc_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hlock : context.lock_prefix_present = false) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0OpcodeFF_run_of_inc_memory [Bindings] (s t : RamState)
    (ip : BitVec 64) (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hlock : context.lock_prefix_present = false) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.INC_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦
      selectLegacy0OpcodeFF_run_of_inc_memory context a b c d e f modrm hmod hreg hlock)

theorem decodeLegacy0_run_of_rex_FF_inc_memory [Bindings] (s : RamState)
    (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (tail : List UInt8)
    (hcode : BytesAt s s.RIP (rex :: 0xFF :: modrm :: tail))
    (hlow : s.RIP.toNat + (rex :: 0xFF :: modrm :: tail).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.INC_MEMv (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmMod modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [decodeLegacy0_run_of_opcodeFF _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeFF_run_of_inc_memory _ _ _ _ _ hmod hreg rfl
      (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem selectLegacy0Opcode01_run_of_add_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hlock : context.lock_prefix_present = false) :
    Select_Legacy_0_Opcode_01 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_01, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode01_run_of_add_memory [Bindings] (s t : RamState)
    (ip : BitVec 64) (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_01 ip context).run s =
      (X86.Instructions.ADD_MEMv_GPRv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_01
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦
      selectLegacy0Opcode01_run_of_add_memory context a b c d e f modrm hmod hlock)

theorem decodeLegacy0_run_of_rex_01_add_memory [Bindings] (s : RamState)
    (h : ReadyToStep s) (rex modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (tail : List UInt8) (hcode : BytesAt s s.RIP (rex :: 0x01 :: modrm :: tail))
    (hlow : s.RIP.toNat + (rex :: 0x01 :: modrm :: tail).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.ADD_MEMv_GPRv (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [decodeLegacy0_run_of_opcode01 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode01_run_of_add_memory _ _ _ _ _ hmod rfl (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

end Md5.Proofs.Buffered.Update.Counter
