import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct.ClearCopy

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1026ac
  readable : ∀ off : Nat, off+8≤520 → MemReadable s (stackPtr s+BitVec.ofNat 64 off) 8
  writable : ∀ off : Nat, off+8≤472 → Common.Instructions.CrossPageStore.Writable s
    (stackPtr s+BitVec.ofNat 64 off) 8
  codeApart : ∀ off co cl : Nat, off+8≤472 → co+cl≤118431 →
    RangeApart (stackPtr s+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 co) cl

def bytes : List UInt8 :=
  [72, 139, 132, 36, 176, 0, 0, 0, 72, 137, 4, 36, 72, 139, 132, 36, 184, 0, 0, 0, 72, 137, 68, 36, 8, 72, 139, 132, 36, 192, 0, 0, 0, 72, 137, 68, 36, 16, 72, 139, 132, 36, 200, 0, 0, 0, 72, 137, 68, 36, 24]

def effect (s : RamState) : Effect :=
  { rip := 0x1026df
    writes := [⟨(.reg 0 : Operand 64),(Operand.mem ((Operand.reg 4 : Operand 64).read s+200) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+0) : Operand 64),(Operand.mem ((Operand.reg 4 : Operand 64).read s+176) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64),(Operand.mem ((Operand.reg 4 : Operand 64).read s+184) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+16) : Operand 64),(Operand.mem ((Operand.reg 4 : Operand 64).read s+192) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+24) : Operand 64),(Operand.mem ((Operand.reg 4 : Operand 64).read s+200) : Operand 64).read s⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1026ac bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x1026ac 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.readable 176 (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x26b4 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1026b4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 8 4
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 0 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 0 0x26b4 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 0 0x26ac 51 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26b8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1026b8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 12 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.readable 184 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26c0 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1026c0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 20 5
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 8 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 8 0x26c0 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 8 0x26ac 51 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26c5 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1026c5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 25 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.readable 192 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26cd (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1026cd 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 33 5
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 16 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 16 0x26cd 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 16 0x26ac 51 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26d2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1026d2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 38 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.readable 200 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26da (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1026da 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026ac bytes 46 5
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 24 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 24 0x26da 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 24 0x26ac 51 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26df (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  have h216_16 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 0 184 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h216_24 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 0 192 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h216_32 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 0 200 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h224_16 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 8 184 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h224_24 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 8 192 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h224_32 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 8 200 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h232_16 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 16 184 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h232_24 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 16 192 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  have h232_32 := fun m (v : BitVec 64) => memLoad_memStore_apart m (stackPtr s) 16 200 v 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect,BitVec.add_assoc,h216_16,h216_24,h216_32,h224_16,h224_24,h224_32,h232_16,h232_24,h232_32]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Wrapper.Entry.Construct.ClearCopy
