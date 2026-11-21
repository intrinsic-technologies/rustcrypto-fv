import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple


set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer.Machine

open X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Common.Instructions.CrossPageStore

theorem store_zero_index [Bindings] (p : BitVec 64) (reg : BitVec 3) (offset : BitVec 32) :
    StepEffect (fun s => Pre p 8 (fun t => rspOf t + offset.signExtend 64) 8 s ∧
        (Operand.reg 15#5 : Operand 64).read s = 0#64)
      (codeRange p (0x4a :: 0x89 :: (AddrMode.sib 4 (some 15) 0 (.d32 offset)).modrm reg ::
        (AddrMode.sib 4 (some 15) 0 (.d32 offset)).tail))
      (movM64R64Effect p (gprNumber 0 0 reg) (.sib 4 none 0 (.d32 offset))) := by
  intro s ready code hp
  obtain ⟨t, step, readyT, effect⟩ := mov_m64_r64_effect_step_any p 0x4a
    (by simp [RexWPrefix]) reg (.sib 4 (some 15) 0 (.d32 offset)) (by simp [AddrMode.Valid]) rfl rfl
    s ready code ⟨hp.1.rip, by
      x86_norm [hp.2, BitVec.shiftLeft_zero, BitVec.zero_add]
      exact hp.1.write, by
      x86_norm [hp.2, BitVec.shiftLeft_zero, BitVec.zero_add]
      exact hp.1.code⟩
  refine ⟨t, step, readyT, ?_⟩
  have eq : movM64R64Effect p (gprNumber 0 (rexR (0x4a : UInt8).toBitVec) reg)
      (.sib 4 (some 15) 0 (.d32 offset)) s =
      movM64R64Effect p (gprNumber 0 0 reg) (.sib 4 none 0 (.d32 offset)) s := by
    x86_norm [hp.2, BitVec.shiftLeft_zero, BitVec.zero_add]
    rfl
  exact eq ▸ effect

end P256.Proofs.HMAC.Finalize.OuterBuffer.Machine
