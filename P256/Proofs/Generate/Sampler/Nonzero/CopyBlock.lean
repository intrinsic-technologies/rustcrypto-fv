import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero.CopyBlock

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x100c00
  readable : ∀ off ∈ ([80,88,96,104] : List (BitVec 64)), MemReadable s (stackPtr s+off) 8
  writable : ∀ off ∈ ([8,16,24,32,184,192,200,208] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s+off) 8
  codeApart : ∀ off ∈ ([8,16,24,32,184,192,200,208] : List (BitVec 64)), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart (stackPtr s+off) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x68,0x48,0x89,0x44,0x24,0x20,0x48,0x8b,0x4c,0x24,0x60,0x48,0x89,0x4c,0x24,0x18,0x48,0x8b,0x54,0x24,0x50,0x48,0x8b,0x74,0x24,0x58,0x48,0x89,0x74,0x24,0x10,0x48,0x89,0x54,0x24,0x8,0x48,0x89,0x94,0x24,0xb8,0x0,0x0,0x0,0x48,0x89,0xb4,0x24,0xc0,0x0,0x0,0x0,0x48,0x89,0x8c,0x24,0xc8,0x0,0x0,0x0,0x48,0x89,0x84,0x24,0xd0,0x0,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x100c48
    writes := [
      ⟨(.reg 0 : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+104) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+96) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+80) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+88) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+80) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+16) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+88) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+24) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+96) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+104) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+184) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+80) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+192) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+88) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+200) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+96) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+208) : Operand 64),(.mem ((Operand.reg 4 : Operand 64).read s+104) : Operand 64).read s⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x100c00 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x100c00 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,by x86_norm [stackPtr]; exact h.readable 104 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xc05 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c05 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 5 5
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 32 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 32 (by simp) 0xc05 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 32 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc0a (by decide))
  advance_then (mov_r64_m64_effect_step 0x100c0a 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 10 5
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.readable 96 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc0f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c0f 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 15 5
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 24 (by simp) 0xc0f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 24 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc14 (by decide))
  advance_then (mov_r64_m64_effect_step 0x100c14 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 20 5
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.readable 80 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc19 (by decide))
  advance_then (mov_r64_m64_effect_step 0x100c19 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 25 5
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.readable 88 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc1e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c1e 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 30 5
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 16 (by simp) 0xc1e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 16 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc23 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c23 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 35 5
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 8 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 8 (by simp) 0xc23 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 8 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc28 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c28 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 40 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 184 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 184 (by simp) 0xc28 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 184 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc30 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c30 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 48 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 192 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 192 (by simp) 0xc30 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 192 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc38 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c38 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 56 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 200 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 200 (by simp) 0xc38 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 200 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc40 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100c40 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 208)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c00 bytes 64 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 208 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 208 (by simp) 0xc40 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 208 (by simp) 0xc00 72 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc48 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Generate.Sampler.Nonzero.CopyBlock
