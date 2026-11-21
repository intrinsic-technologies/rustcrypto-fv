import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction
import Sha2.Proofs.Common.Instructions.CrossPageStore.Mov
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

theorem addImmediate_step [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeAddR64Imm8 dst imm))
      (addR64Imm8Effect p (dst.setWidth 5) imm) := by
  obtain ⟨rex, modrm, encoded, prefixValid, mode, register, destination⟩ :=
    encodeAddR64Imm8_spec dst imm
  rw [encoded, ← destination]
  exact add_r64_imm8_effect_step p rex modrm imm prefixValid mode register

theorem compareIndexStack_step [Bindings] (p : BitVec 64) (index : BitVec 4) (slot : Disp)
    (valid : (AddrMode.sib 4 none 0 slot).Valid) :
    StepEffect (LoadPre p (fun s => (AddrMode.sib 4 none 0 slot).addr s
      (p + BitVec.ofNat 64 (encodeCmpM64R64 index (.sib 4 none 0 slot)).length)) 8)
      (codeRange p (encodeCmpM64R64 index (.sib 4 none 0 slot)))
      (cmpMREffect p (encodeCmpM64R64 index (.sib 4 none 0 slot)).length 64
        (index.setWidth 5) (.sib 4 none 0 slot)) := by
  obtain ⟨prefixValid, register, indexBit, baseBit⟩ :=
    (AddrMode.sib 4 none 0 slot).rexByte_true_spec index
  have step := cmp_m64_r64_effect_step p _ prefixValid (regLow index)
    (.sib 4 none 0 slot) valid indexBit baseBit
  rw [register, gprNumber_reg] at step
  have length : (encodeCmpM64R64 index (.sib 4 none 0 slot)).length =
      3 + (AddrMode.sib 4 none 0 slot).tail.length := by
    simp only [encodeCmpM64R64, List.length_cons]
    omega
  rw [length]
  exact step

theorem zero_step [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeXorR32R32 dst dst))
      (xorR32R32Effect p (encodeXorR32R32 dst dst).length (dst.setWidth 5)
        (dst.setWidth 5)) := by
  rcases encodeXorR32R32_spec dst dst with ⟨modrm, encoded, mode, destination, source⟩ |
    ⟨rex, modrm, encoded, prefixValid, mode, destination, source⟩
  · have step := xor_r32_r32_effect_step p modrm mode
    rw [destination, source] at step
    simpa only [encoded, List.length_cons, List.length_nil] using step
  · have step := xor_r32_r32_rex_effect_step p rex modrm prefixValid mode
    rw [destination, source] at step
    simpa only [encoded, List.length_cons, List.length_nil] using step

theorem spill_step [Bindings] (p : BitVec 64) (src : BitVec 4) (slot : Disp)
    (valid : (AddrMode.sib 4 none 0 slot).Valid) :
    StepEffect (CrossPageStore.Pre p (encodeMovM64R64 src (.sib 4 none 0 slot)).length
      (storeAddrAt p (.sib 4 none 0 slot)
        (encodeMovM64R64 src (.sib 4 none 0 slot)).length) 8)
      (codeRange p (encodeMovM64R64 src (.sib 4 none 0 slot)))
      (movM64R64Effect p (src.setWidth 5) (.sib 4 none 0 slot)) := by
  obtain ⟨prefixValid, register, indexBit, baseBit⟩ :=
    (AddrMode.sib 4 none 0 slot).rexByte_true_spec src
  have step := CrossPageStore.mov_m64_r64_effect_step_any p _ prefixValid (regLow src)
    (.sib 4 none 0 slot) valid indexBit baseBit
  rw [register, gprNumber_reg] at step
  have length : (encodeMovM64R64 src (.sib 4 none 0 slot)).length =
      3 + (AddrMode.sib 4 none 0 slot).tail.length := by
    simp only [encodeMovM64R64, List.length_cons]
    omega
  rw [length]
  exact step

theorem compareZeroStack_step [Bindings] (p : BitVec 64) (slot : Disp) (imm : BitVec 8)
    (valid : (AddrMode.sib 4 none 0 slot).Valid) :
    StepEffect (LoadPre p (fun s => (AddrMode.sib 4 none 0 slot).addr s
      (p + BitVec.ofNat 64 (encodeCmpM64Imm8 (.sib 4 none 0 slot) imm).length)) 8)
      (codeRange p (encodeCmpM64Imm8 (.sib 4 none 0 slot) imm))
      (cmpMImm8Effect p (encodeCmpM64Imm8 (.sib 4 none 0 slot) imm).length 64
        (.sib 4 none 0 slot) imm) := by
  obtain ⟨prefixValid, _, indexBit, baseBit⟩ :=
    (AddrMode.sib 4 none 0 slot).rexByte_true_spec 0
  have step := cmp_m64_imm8_effect_step p _ prefixValid (.sib 4 none 0 slot)
    valid indexBit baseBit imm
  have length : (encodeCmpM64Imm8 (.sib 4 none 0 slot) imm).length =
      4 + (AddrMode.sib 4 none 0 slot).tail.length := by
    simp only [encodeCmpM64Imm8, List.length_cons, List.length_append, immBytes_length]
    omega
  rw [length]
  exact step

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
