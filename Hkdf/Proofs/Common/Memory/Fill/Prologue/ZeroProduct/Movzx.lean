import X86Proofs.Step.Decode.Legacy1OpcodeB6
import X86Proofs.Instructions.Movzx.Generated.RM8.Decode
import X86Proofs.Instructions.Movzx.Operation
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Memory.Fill

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem movzx_r32_r8_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) (hrex : ctx.rex_prefix_present = true) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movzxSpec 32 ((src.read s).setWidth 8)) ip) := by
  have hcontext :
      {ctx with operand_size := 32, lock_prefix_present := false, rex_prefix_present := true} =
        ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.read_reg64, Operand.write_reg32]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.MOVZX => movzx_operation _ 32 (.inr rfl) _,
    Write_GPR => by
      rw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
      simp only [movzxSpec, BitVec.ofNat_toNat, gprNumber, Int.reduceToNat, Int.reduceAdd]]

theorem movzx_ecx_sil_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x40, 0x0f, 0xb6, 0xce])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg 1 : Operand 32)
        (movzxSpec 32 (((Operand.reg 6 : Operand 64).read t).setWidth 8))
        (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x40, 0x0f, 0xb6, 0xce] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok 0xce, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_opcodeB6 _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS 0x40) rfl (hmode 4) f1
  rw [decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ rfl (hmode 5) hf f2,
    movzx_r32_r8_form _ _ _ _ _ (hmode 5) rfl rfl rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h 0x40 0xb6 [0xce] (by simp [RexPrefix])
    (by decide) hcode hlow hd ((hmode 5).of_cs_lma_eq rfl rfl)

def movzxEcxsilEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 1 : Operand 64),
      ((Operand.reg 6 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

theorem movzx_ecx_sil_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x40, 0x0f, 0xb6, 0xce])
      (movzxEcxsilEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_ecx_sil_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

end Hkdf.Proofs.Common.Memory.Fill
