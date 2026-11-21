import P256.Proofs.Verifying.Wrapper.KeyCopy.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Word

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure Pre (pc : BitVec 64) (off : BitVec 8) (s : RamState) : Prop where
  rip : s.RIP = pc
  readable : MemReadable s ((Operand.reg 2 : Operand 64).read s + off.signExtend 64) 8
  writable : CrossPageStore.Writable s ((Operand.reg 4 : Operand 64).read s + off.signExtend 64) 8
  apart : RangeApart ((Operand.reg 4 : Operand 64).read s + off.signExtend 64) 8 pc 9

def bytes (off : BitVec 8) : List UInt8 :=
  [0x48,0x8b,0x4a,UInt8.ofBitVec off,0x48,0x89,0x4c,0x24,UInt8.ofBitVec off]

def effect (pc : BitVec 64) (off : BitVec 8) (s : RamState) : Effect :=
  { rip := pc + 9
    writes := [⟨(.reg 1 : Operand 64),
      (.mem ((Operand.reg 2 : Operand 64).read s + off.signExtend 64) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + off.signExtend 64) : Operand 64),
      (.mem ((Operand.reg 2 : Operand 64).read s + off.signExtend 64) : Operand 64).read s⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (pc : BitVec 64) (off : BitVec 8)
    (nextLoad : pc + 4 ≠ boundary.rip) (nextStore : pc + 9 ≠ boundary.rip) :
    AdvanceTriple boundary (Pre pc off) (codeRange pc (bytes off)) (Effect.post (effect pc off)) := by
  advance_begin (mov_r64_m64_effect_step pc 0x48 (by simp [RexWPrefix]) 1
    (.base 2 (.d8 off)) (by simp [AddrMode.Valid, regLow]) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable⟩
  case sub =>
    simpa [bytes, AddrMode.tail, AddrMode.modrm, AddrMode.mod, AddrMode.rm,
      AddrMode.sibByte, idxLow, regLow, Disp.mod, Disp.bytes, immBytes, immByte] using
      (codeRange_slice_subset pc (bytes off) 0 4)
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any (pc + 4) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 off)) (by simp [AddrMode.Valid, regLow]) rfl rfl)
  case sub =>
    simpa [bytes, AddrMode.tail, AddrMode.modrm, AddrMode.mod, AddrMode.rm,
      AddrMode.sibByte, idxLow, regLow, Disp.mod, Disp.bytes, immBytes, immByte] using
      (codeRange_slice_subset pc (bytes off) 4 5)
  case mid =>
    intro s t hp hh ho
    refine ⟨CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable
    · x86_norm
      exact hp.apart.sub 4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart
    · x86_norm
      exact nextStore
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Wrapper.KeyCopy.Word
