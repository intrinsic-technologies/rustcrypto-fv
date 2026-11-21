import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Program.Entry
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Program.RipCopy

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

structure Pre (pc : BitVec 64) (displacement : BitVec 32) (offset : BitVec 8)
    (s : RamState) : Prop where
  rip : s.RIP = pc
  readable : MemReadable s (pc + 7 + displacement.signExtend 64) 8
  writable : MemWritable s ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 8
  apart : RangeApart ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 8 pc 12

def bytes (displacement : BitVec 32) (offset : BitVec 8) : List UInt8 :=
  [0x48, 0x8b, 0x05] ++ immBytes 32 displacement ++
    [0x48, 0x89, 0x44, 0x24, UInt8.ofBitVec offset]

def effect (pc : BitVec 64) (displacement : BitVec 32) (offset : BitVec 8)
    (s : RamState) : Effect :=
  { rip := pc + 12
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (pc + 7 + displacement.signExtend 64) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) : Operand 64),
        (.mem (pc + 7 + displacement.signExtend 64) : Operand 64).read s⟩] }

theorem copy_word [Bindings] (boundary : ReturnBoundary) (pc : BitVec 64)
    (displacement : BitVec 32) (offset : BitVec 8)
    (nextLoad : pc + 7 ≠ boundary.rip) (nextStore : pc + 12 ≠ boundary.rip) :
    AdvanceTriple boundary (Pre pc displacement offset) (codeRange pc (bytes displacement offset))
      (Effect.post (effect pc displacement offset)) := by
  advance_begin (mov_r64_m64_effect_step pc 0x48 (by simp [RexWPrefix]) 0
    (.rip displacement) (by trivial) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable⟩
  case sub =>
    simpa [bytes, immBytes, AddrMode.tail, AddrMode.modrm, AddrMode.mod, AddrMode.rm,
      AddrMode.sibByte, idxLow, regLow, Disp.mod, Disp.bytes, immByte] using
      (codeRange_slice_subset pc (bytes displacement offset) 0 7)
  advance_then (mov_m64_r64_effect_step (pc + 7) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 offset)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [bytes, immBytes, AddrMode.tail, AddrMode.modrm, AddrMode.mod, AddrMode.rm,
      AddrMode.sibByte, idxLow, regLow, Disp.mod, Disp.bytes, immByte] using
      (codeRange_slice_subset pc (bytes displacement offset) 7 5)
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable
    · x86_norm
      exact hp.apart.sub 7 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      x86_norm
      exact Effect.avoids_of_components_mem_rip (by x86_norm [Effect.components]) hp.apart
    · x86_norm
      exact nextStore
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Program.RipCopy
