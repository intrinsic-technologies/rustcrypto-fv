import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr
import X86Proofs.Program.Effect

namespace P256.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def shldOneFlags (x y : BitVec 64) : StatusFlagsOutcome :=
  let r := shldOneResult x y
  { CF := some x.msb, PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
    ZF := some (r == 0), SF := some r.msb, OF := some (x.msb != r.msb) }

theorem shldOneFlags_allows (af : Bool) (x y : BitVec 64) :
    (shldOneFlags x y).Allows (shldOneSpec af x y).2 := by
  simp [shldOneFlags, shldOneSpec, StatusFlagsOutcome.Allows, FlagAllows]

def shldR64R64OneEffect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let x := (Operand.reg dst : Operand 64).read s
  let y := (Operand.reg src : Operand 64).read s
  { rip := p + 5
    writes := [⟨(Operand.reg dst : Operand 64), shldOneResult x y⟩]
    flags := some (shldOneFlags x y) }

theorem shldR64R64OneEffect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (shldR64R64OneEffect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem shld_r64_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0xA4, modrm, 1])
      (shldR64R64OneEffect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shld_r64_r64_one_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 5 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shldOneSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shldOneFlags_allows

end P256.Proofs.Common.Instructions.ShiftLeft
