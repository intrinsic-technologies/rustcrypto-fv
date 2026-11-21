import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
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
import P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Store

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x101191
  index : (Operand.reg 15#5 : Operand 64).read s = 0#64
  readable : ∀ i ∈ ([8, 16, 24, 32] : List (BitVec 64)),
    MemReadable s (stackPtr s + i) 8
  writable : ∀ i ∈ ([176, 184, 192, 200] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + i) 8
  codeApart : ∀ i ∈ ([176, 184, 192, 200] : List (BitVec 64)),
    RangeApart (stackPtr s + i) 8 0x101182 208

theorem Pre.code_slice {s : RamState} (h : Pre s)
    (i : BitVec 64) (hi : i ∈ [176,184,192,200])
    (offset len : Nat) (bound : offset + len ≤ 208) :
    RangeApart (stackPtr s + i) 8 (0x101182 + BitVec.ofNat 64 offset) len := by
  intro j hj k hk
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    h.codeApart i hi j hj (offset + k) (by omega)

def bytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x20,0x4a,0x89,0x84,0x3c,0xc8,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x18,0x4a,0x89,0x84,0x3c,0xc0,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x8,0x48,0x8b,0x4c,0x24,0x10,0x4a,0x89,0x8c,0x3c,0xb8,0x0,0x0,0x0,0x4a,0x89,0x84,0x3c,0xb0,0x0,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x1011c5
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 8) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 16) 64⟩,
      ⟨(.mem (stackPtr s + 200) : Operand 64), memLoad s.external (stackPtr s + 32) 64⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), memLoad s.external (stackPtr s + 24) 64⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), memLoad s.external (stackPtr s + 16) 64⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), memLoad s.external (stackPtr s + 8) 64⟩] }

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x101191 bytes)
      (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (movR64M64Effect 0x101191 0 (.sib 4 none 0 (.d8 32))) from
    mov_r64_m64_effect_step 0x101191 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 32 (by simp)⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x1196 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x101196 0 (.sib 4 none 0 (.d32 200))) from
    store_zero_index 0x101196 0 200)
  case sub => exact codeRange_slice_subset 0x101191 bytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds (p := 0x101196) (am := .sib 4 none 0 (.d32 200)) (nxt := 0x101196 + 8) hH (hO true) (by x86_norm) ?_ ?_, ?_⟩, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 200 (by simp)
    · x86_norm [stackPtr]
      exact hP.code_slice 200 (by simp) 20 8 (by decide)
    · exact (hH.agrees.read (n := 64) (r := 15#5) (by x86_norm)).trans hP.index
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.code_slice 200 (by simp) 15 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x119e (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x10119e 0 (.sib 4 none 0 (.d8 24))) from
    mov_r64_m64_effect_step 0x10119e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101191 bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 24 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x11a3 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1011a3 0 (.sib 4 none 0 (.d32 192))) from
    store_zero_index 0x1011a3 0 192)
  case sub => exact codeRange_slice_subset 0x101191 bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds (p := 0x1011a3) (am := .sib 4 none 0 (.d32 192)) (nxt := 0x1011a3 + 8) hH (hO true) (by x86_norm) ?_ ?_, ?_⟩, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 192 (by simp)
    · x86_norm [stackPtr]
      exact hP.code_slice 192 (by simp) 33 8 (by decide)
    · exact (hH.agrees.read (n := 64) (r := 15#5) (by x86_norm)).trans hP.index
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.code_slice 192 (by simp) 15 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x11ab (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x1011ab 0 (.sib 4 none 0 (.d8 8))) from
    mov_r64_m64_effect_step 0x1011ab 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101191 bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 8 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x11b0 (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x1011b0 1 (.sib 4 none 0 (.d8 16))) from
    mov_r64_m64_effect_step 0x1011b0 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101191 bytes 31 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 16 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x11b5 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1011b5 1 (.sib 4 none 0 (.d32 184))) from
    store_zero_index 0x1011b5 1 184)
  case sub => exact codeRange_slice_subset 0x101191 bytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds (p := 0x1011b5) (am := .sib 4 none 0 (.d32 184)) (nxt := 0x1011b5 + 8) hH (hO true) (by x86_norm) ?_ ?_, ?_⟩, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 184 (by simp)
    · x86_norm [stackPtr]
      exact hP.code_slice 184 (by simp) 51 8 (by decide)
    · exact (hH.agrees.read (n := 64) (r := 15#5) (by x86_norm)).trans hP.index
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.code_slice 184 (by simp) 15 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x11bd (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1011bd 0 (.sib 4 none 0 (.d32 176))) from
    store_zero_index 0x1011bd 0 176)
  case sub => exact codeRange_slice_subset 0x101191 bytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds (p := 0x1011bd) (am := .sib 4 none 0 (.d32 176)) (nxt := 0x1011bd + 8) hH (hO true) (by x86_norm) ?_ ?_, ?_⟩, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 176 (by simp)
    · x86_norm [stackPtr]
      exact hP.code_slice 176 (by simp) 59 8 (by decide)
    · exact (hH.agrees.read (n := 64) (r := 15#5) (by x86_norm)).trans hP.index
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.code_slice 176 (by simp) 15 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x11c5 (by decide))
  advance_finish [effect, stackPtr, Operand.read_reg64, State.regValue, gprNumber]

end P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Copy
