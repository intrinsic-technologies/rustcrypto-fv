import P256.Proofs.Common.Der.Memory.Writable
import P256.Proofs.Common.Instructions.CrossPageStore.Legacy
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Der.Memory

open X86 X86.Machine X86.UserProcess X86Proofs

theorem mov_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s ready code pre
  exact (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any p rex hrex reg am hv hx hb) s ready code ⟨pre.rip, (pre.write.crossPage (by decide)), pre.code⟩

theorem mov_m32_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s ready code pre
  exact (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any p rex hrex reg am hv hx hb) s ready code ⟨pre.rip, (pre.write.crossPage (by decide)), pre.code⟩

theorem mov_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32Effect p am imm) := by
  intro s ready code pre
  exact (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any p rex hrex am hv hx hb imm) s ready code ⟨pre.rip, (pre.write.crossPage (by decide)), pre.code⟩

theorem mov_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8Effect p am imm) := by
  intro s ready code pre
  exact (X86Proofs.mov_m8_imm8_effect_step p am hv hx hb imm) s ready code ⟨pre.rip, pre.write.byte, pre.code⟩

theorem mov_m32_r32_low_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (movM32R32LowEffect p (gprNumber 0 0 reg)
        am) := by
  intro s ready code pre
  exact (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any p reg am hv hx hb) s ready code ⟨pre.rip, (pre.write.crossPage (by decide)), pre.code⟩

theorem mov_m32_imm32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (StorePre p (6 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32Effect p (6 + am.tail.length) am imm) := by
  intro s ready code pre
  exact (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_imm32_legacy_effect_step_any p am hv hx hb imm) s ready code ⟨pre.rip, (pre.write.crossPage (by decide)), pre.code⟩

theorem mov_m8_r8_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (2 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  intro s ready code pre
  exact (X86Proofs.mov_m8_r8_effect_step p reg hreg am hv hx hb) s ready code ⟨pre.rip, pre.write.byte, pre.code⟩

theorem mov_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  intro s ready code pre
  exact (X86Proofs.mov_m8_r8_rex_effect_step p rex hr reg am hv hx hb) s ready code ⟨pre.rip, pre.write.byte, pre.code⟩

theorem mov_m8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (StorePre p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)) 1)
      (codeRange p (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (storeEffect p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length))
        (fun _ => imm)) := by
  intro s ready code pre
  exact (X86Proofs.mov_m8_imm8_rex_effect_step p rex hr am hv hx hb imm) s ready code ⟨pre.rip, pre.write.byte, pre.code⟩

end P256.Proofs.Common.Der.Memory
