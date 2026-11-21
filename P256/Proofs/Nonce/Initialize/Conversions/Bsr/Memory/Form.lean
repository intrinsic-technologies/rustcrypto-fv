import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Form
import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Load

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem bsr_r64_m64_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hread : MemReadable t addr 8) :
    (X86.Instructions.BSR_GPRv_MEMv_0 ip ctx mod reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src := (Operand.mem addr : Operand 64).read t
      (.ok (), writeOutputs (dataAccess t "load") dst (bsrSpec64 (dst.read t) src)
        (bsrOracleUsed src) next) := by
  have hcontext :
      {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hmem := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hread.low hread.mem
  unfold X86.Instructions.BSR_GPRv_MEMv_0
  spec_bind_with hea
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hmem,
    X86.Instructions.Operations.BSR => bsr64_operation _ _]
  dsimp only []
  change (if !(((Operand.mem addr : Operand 64).read t) == (0 : BitVec 64)) then
    Write_GPR (size := 64) (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (if (Operand.mem addr : Operand 64).read t = 0 then
        ((dataAccess t "load").oracle.take 64).1
      else bsrValue64 ((Operand.mem addr : Operand 64).read t))
    else pure ()).run
      (setFlags {(dataAccess t "load") with
        Next_IP := next, oracle := oracleSkip (dataAccess t "load").oracle
          (bsrOracleUsed ((Operand.mem addr : Operand 64).read t))}
        (bsrFlags64 ((Operand.mem addr : Operand 64).read t))) = _
  by_cases hx : (Operand.mem addr : Operand 64).read t = 0
  · have hb : (((Operand.mem addr : Operand 64).read t) == (0 : BitVec 64)) = true :=
      by simpa using hx
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [hx, bsrOracleUsed, ↓reduceIte]
    change (Except.ok (), writeFlagsOutputs (dataAccess t "load") (bsrFlags64 0) 64 next) = _
    simp only [bsrSpec64, ↓reduceIte]
    exact congrArg (fun u => (Except.ok (), u))
      (writeOutputs_read_self64 (dataAccess t "load")
        (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (bsrFlags64 0) 64 next).symm
  · have hb : (((Operand.mem addr : Operand 64).read t) == (0 : BitVec 64)) = false :=
      by simpa using hx
    simp only [hb, Bool.not_false, ↓reduceIte, hx]
    have hm : In64BitMode (setFlags {(dataAccess t "load") with
        Next_IP := next, oracle := oracleSkip (dataAccess t "load").oracle
          (bsrOracleUsed ((Operand.mem addr : Operand 64).read t))}
        (bsrFlags64 ((Operand.mem addr : Operand 64).read t))) :=
      hmode.of_cs_lma_eq rfl rfl
    rw [writeGPR64_run _ _ _ hm]
    simp only [bsrSpec64, hx, ↓reduceIte]
    simp only [writeOutputs, Operand.write_reg64]

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
