import Sha3.Proofs.Scalar.Condition.Sete.LowByte

namespace X86Proofs

open X86 X86.Helpers

def orSpec {n : Nat} (af : Bool) (x y : BitVec n) : BitVec n × StatusFlags :=
  let r := x ||| y
  (r, { OF := false, CF := false, SF := r.msb, ZF := r == 0,
        PF := evenParity (r.extractLsb' 0 8), AF := af })

theorem or_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.OR n x y).run s =
      let (r, flags) := orSpec (oracleBit s.oracle) x y
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle 1 } flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.OR
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [-BitVec.msb_or, extractLsb'_msb, beq_zero_eq_decide, X86Proofs.oracleTake_match_eq_oracleTakeCount, oracleTakeGo_one,
      oracleSkip, orSpec, setFlags, StatusFlags.store]
    congr 2
    rw [ite_one_zero, ite_one_zero]
    simp

theorem or_low_form {σ : Type} [Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hlock : ctx.lock_prefix_present = false)
    (hdst : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hsrc : (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4) :
    (X86.Instructions.OR_GPR8_GPR8_08 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (orSpec (oracleBit s.oracle) (dst.read s) (src.read s))
        1 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.OR_GPR8_GPR8_08
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by assumption) _ hmode,
    X86.Instructions.Operations.OR => or_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ hdst _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
