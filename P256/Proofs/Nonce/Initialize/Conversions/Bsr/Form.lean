import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Operation
import X86Proofs.Program.Agrees

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def bsrSpec64 (dst src : BitVec 64) : BitVec 64 × StatusFlags :=
  (if src = 0 then dst else bsrValue64 src, bsrFlags64 src)

theorem writeOutputs_read_self64 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (flags : StatusFlags) (used : Nat) (ip : BitVec 64) :
    writeOutputs s (.reg r : Operand 64) ((Operand.reg r : Operand 64).read s, flags) used ip =
      writeFlagsOutputs s flags used ip := by
  simp [writeOutputs, writeFlagsOutputs, Operand.read_reg64, Operand.write_reg64, setFlags]

theorem bsr_r64_r64_form {σ : Type} [PhysicalMemory σ]
    (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.BSR_GPRv_GPRv_0 ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (bsrSpec64 (dst.read s) (src.read s))
        (bsrOracleUsed (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := readGPR64_run s (gprNumber ctx.rex_b4 ctx.rex_b3 rm) hmode
  unfold X86.Instructions.BSR_GPRv_GPRv_0
  spec_run [Read_GPR => hread, X86.Instructions.Operations.BSR => bsr64_operation _ _]
  dsimp only []
  change (if !(s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)] == (0 : BitVec 64)) then
    Write_GPR (size := 64) (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (if s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)] = 0 then
        (s.oracle.take 64).1 else bsrValue64 s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)])
    else pure ()).run
      (setFlags {s with Next_IP := ip, oracle := (oracleSkip s.oracle
        (bsrOracleUsed s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)]))}
        (bsrFlags64 s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)])) = _
  by_cases hx : s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)] = (0 : BitVec 64)
  · have hb : (s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)] == (0 : BitVec 64)) = true :=
      by simpa using hx
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [hx, bsrOracleUsed, ↓reduceIte]
    change (Except.ok (), writeFlagsOutputs s (bsrFlags64 0) 64 ip) = _
    simp only [bsrSpec64, Operand.read_reg64, hx, ↓reduceIte]
    exact congrArg (fun t => (Except.ok (), t))
      (writeOutputs_read_self64 s (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (bsrFlags64 0) 64 ip).symm
  · have hb : (s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)] == (0 : BitVec 64)) = false :=
      by simpa using hx
    simp only [hb, Bool.not_false, ↓reduceIte, hx]
    have hm : In64BitMode (setFlags {s with Next_IP := ip, oracle := (oracleSkip s.oracle (bsrOracleUsed s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)]))}
        (bsrFlags64 s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)])) :=
      hmode.of_cs_lma_eq rfl rfl
    rw [writeGPR64_run _ _ _ hm]
    simp only [bsrSpec64, Operand.read_reg64, hx, ↓reduceIte]
    simp only [writeOutputs, Operand.write_reg64]

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
