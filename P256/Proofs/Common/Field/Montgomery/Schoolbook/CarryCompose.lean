import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.Carry
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Carry
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Words
import P256.Proofs.Common.Instructions.Carry.Memory
import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Common.Instructions.AddByte
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64M64Effect adcR64R64Effect)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect)

namespace P256.Proofs.Common.Field.Montgomery.Schoolbook

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem addR8Imm8Effect_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (addR8Imm8Effect p dst imm) := by
  refine ⟨fun _ _ _ => rfl, ?_, fun _ _ _ => rfl, ?_, ?_⟩
  · intro s t h
    simp only [addR8Imm8Effect, h.read_reg]
  · intro s t h i hi
    simp only [addR8Imm8Effect, Effect.flag, h.read_reg]
  · intro s
    simp [addR8Imm8Effect, Write.Full, Operand.Full]

@[x86_compose] theorem setbR8Effect_eq (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) :
    setccR8Effect p len dst 2 s =
      { rip := p + BitVec.ofNat 64 len
        writes := [⟨(Operand.reg dst : Operand 64),
          mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then 1 else 0)
            ((Operand.reg dst : Operand 64).read s)⟩] } := rfl

attribute [x86_compose] adcR64R64Effect adcR64Imm8Effect adcR64M64Effect
  addR64M64Effect addR8Imm8Effect carryBit_eq_ofBool

end P256.Proofs.Common.Field.Montgomery.Schoolbook
