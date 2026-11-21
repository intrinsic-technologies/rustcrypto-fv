import Base16ct.Proofs.Base16ctUpperEncodeCorrect.LoopInstructions.Or
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Slices.Byte.Add
import Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.ByteLogic.And
import Base16ct.Proofs.Copied.P256.Proofs.Common.Encoding.Parser.ByteStore
namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_r8_imm8_effect_step)
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte (addR8R8Effect add_r8_r8_effect_step)

attribute [x86_compose] andR8Imm8Effect

@[x86_local] theorem andR8Imm8Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) : Effect.Local (andR8Imm8Effect p len dst imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [andR8Imm8Effect, h.read_reg]
  · cases i <;> simp_all [andR8Imm8Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, andFlags, h.read_reg]
  · simp [andR8Imm8Effect, Write.Full, Operand.Full]

theorem andR8Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (andR8Imm8Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem andR8Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 8) (s : RamState) (code : CodeMap) :
    (andR8Imm8Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [andR8Imm8Effect_components, Component.Covers]) code

theorem or_r10d_48_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x83, 0xca, 0x30])
      (orR32Imm8Effect p 10 48) :=
  or_r32_imm8_rex_effect_step p 0x41 0xca 48 (by unfold RexNoWPrefix; decide +kernel) rfl rfl

theorem or_r9d_48_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x83, 0xc9, 0x30])
      (orR32Imm8Effect p 9 48) :=
  or_r32_imm8_rex_effect_step p 0x41 0xc9 48 (by unfold RexNoWPrefix; decide +kernel) rfl rfl

theorem and_r11b_7_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x80, 0xe3, 0x07])
      (andR8Imm8Effect p 4 11 7) :=
  and_r8_imm8_effect_step p 0x41 0xe3 7 (by unfold RexPrefix; decide +kernel) rfl rfl

theorem and_r10b_7_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x80, 0xe2, 0x07])
      (andR8Imm8Effect p 4 10 7) :=
  and_r8_imm8_effect_step p 0x41 0xe2 7 (by unfold RexPrefix; decide +kernel) rfl rfl

theorem add_r11b_r10b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x45, 0x00, 0xd3])
      (addR8R8Effect p 11 10) :=
  add_r8_r8_effect_step p 0x45 0xd3 (by unfold RexPrefix; decide +kernel) rfl

theorem add_r10b_r9b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x45, 0x00, 0xca])
      (addR8R8Effect p 10 9) :=
  add_r8_r8_effect_step p 0x45 0xca (by unfold RexPrefix; decide +kernel) rfl

def movM8R8Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (storeAddrAt p am len) fun s ↦ (Operand.reg src : Operand 8).read s

attribute [x86_compose] movM8R8Effect

@[x86_local] theorem movM8R8Effect_local (p : BitVec 64) (len : Nat)
    (src : BitVec 5) (am : AddrMode) : Effect.Local (movM8R8Effect p len src am) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movM8R8Effect, storeEffect, AddrMode.addr_obs h]
  · simp [movM8R8Effect, storeEffect, h.read_reg, AddrMode.addr_obs h]
  · simpa only [movM8R8Effect, storeEffect, Effect.flag] using congrArg some hi
  · simp [movM8R8Effect, storeEffect, Write.Full, Operand.Full]

theorem mov_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.mov_m8_r8_effect_step p rex hrex reg am hv hx hb

theorem mov_m8_r11b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StorePre p 4 (storeAddrAt p (.sib 1 (some 8) 1 .none) 4) 1)
      (codeRange p [0x46, 0x88, 0x1c, 0x41])
      (movM8R8Effect p 4 11 (.sib 1 (some 8) 1 .none)) :=
  mov_m8_r8_rex_effect_step p 0x46 (by unfold RexPrefix; decide +kernel) 3
    (.sib 1 (some 8) 1 .none)
    (by decide +kernel) rfl rfl

theorem mov_m8_r10b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StorePre p 5 (storeAddrAt p (.sib 1 (some 8) 1 (.d8 1)) 5) 1)
      (codeRange p [0x46, 0x88, 0x54, 0x41, 0x01])
      (movM8R8Effect p 5 10 (.sib 1 (some 8) 1 (.d8 1))) :=
  mov_m8_r8_rex_effect_step p 0x46 (by unfold RexPrefix; decide +kernel) 2
    (.sib 1 (some 8) 1 (.d8 1))
    (by decide +kernel) rfl rfl

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
