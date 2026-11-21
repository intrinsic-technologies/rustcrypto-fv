import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.Bswap
import P256.Proofs.Program.Code
import P256.Proofs.ReadBe.Input
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

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (bswap64 bswapR64Effect bswap_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure InputLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fc15
  readable : ∀ i ∈ [0, 8, 16, 24],
    MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8

def inputLoadBytes : List UInt8 :=
  [0x48, 0x8b, 0x06, 0x48, 0x8b, 0x4e, 0x08,
    0x4c, 0x8b, 0x46, 0x10, 0x48, 0x8b, 0x56, 0x18,
    0x48, 0x0f, 0xc8, 0x48, 0x0f, 0xc9, 0x49, 0x0f, 0xc8, 0x48, 0x0f, 0xca]

def inputLoadEffect (s : RamState) : Effect :=
  { rip := 0x10fc30
    writes := [
      ⟨(Operand.reg 0 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s)⟩,
      ⟨(Operand.reg 1 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s)⟩,
      ⟨(Operand.reg 8 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 16) : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 24) : Operand 64).read s)⟩] }

def inputWordsEffect (s : RamState) : Effect :=
  { rip := 0x10fc24
    writes := [
      ⟨(Operand.reg 0 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.reg 8 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 24) : Operand 64).read s⟩] }

def inputSwapEffect (s : RamState) : Effect :=
  { rip := 0x10fc30
    writes := [
      ⟨(Operand.reg 0 : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.reg 1 : Operand 64), bswap64 ((Operand.reg 1 : Operand 64).read s)⟩,
      ⟨(Operand.reg 8 : Operand 64), bswap64 ((Operand.reg 8 : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩] }

theorem input_words_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InputLoadPre (codeRange 0x10fc15 inputLoadBytes)
      (Effect.post inputWordsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10fc15 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.base 6 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 0 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc18 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x10fc18 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc1c (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x10fc1c 0x4c
    (by unfold RexWPrefix; decide +kernel) 0 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc20 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x10fc20 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc24 (by decide +kernel))
  advance_finish [inputWordsEffect, BitVec.add_zero]

theorem input_swap_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fc24) (codeRange 0x10fc15 inputLoadBytes)
      (Effect.post inputSwapEffect) := by
  advance_begin (bswap_r64_effect_step 0x10fc24 0)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 15 3
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc27 (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x10fc27 1)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc2a (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x10fc2a 8)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc2d (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x10fc2d 2)
  case sub => exact codeRange_slice_subset 0x10fc15 inputLoadBytes 24 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc30 (by decide +kernel))
  advance_finish [inputSwapEffect]

theorem input_load_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InputLoadPre (codeRange 0x10fc15 inputLoadBytes)
      (Effect.post inputLoadEffect) := by
  intro s hr hc hp
  obtain ⟨n, u, hrun, hru, hcu, hu⟩ := input_words_correct boundary hout s hr hc hp
  obtain ⟨m, t, hrun', hrt, hct, ht⟩ := input_swap_correct boundary hout u hru hcu hu.rip
  refine ⟨n + m, t, hrun.trans hrun', hrt, hct, ?_⟩
  refine ⟨ht.rip, ?_, trivial, ?_⟩
  · change (Operand.reg 0 : Operand 64).read t = _ ∧
      (Operand.reg 1 : Operand 64).read t = _ ∧
      (Operand.reg 8 : Operand 64).read t = _ ∧
      (Operand.reg 2 : Operand 64).read t = _
    exact ⟨ht.writes.1.trans (congrArg bswap64 hu.writes.1),
      ht.writes.2.1.trans (congrArg bswap64 hu.writes.2.1),
      ht.writes.2.2.1.trans (congrArg bswap64 hu.writes.2.2.1),
      ht.writes.2.2.2.trans (congrArg bswap64 hu.writes.2.2.2)⟩
  · apply (hu.agrees.trans ht.agrees).mono
    simp [inputWordsEffect, inputSwapEffect, inputLoadEffect, Effect.components]

theorem input_load_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10fc15 inputLoadBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xfc15 inputLoadBytes
    (by decide +kernel) (by decide +kernel)

theorem input_load_nat [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (hout : ¬ InProgram boundary.rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : InputLoadPre s)
    (bytes : (registerRegion s .rsi 32).HasBytes s.external input) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10fc30 ∧
      t.regValue .rax = BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.octetsToNat input / 2^192) ∧
      t.regValue .rcx = BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.octetsToNat input / 2^128) ∧
      t.regValue .r8 = BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.octetsToNat input / 2^64) ∧
      t.regValue .rdx = BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.octetsToNat input) ∧
      AgreesExcept [.reg 0, .reg 1, .reg 8, .reg 2, .rip] s t := by
  obtain ⟨fuel, t, run, hr, _, he⟩ :=
    input_load_correct boundary hout s ready (input_load_code loaded) pre
  have hm : t.external = s.external := he.agrees.external
    (by simp [inputLoadEffect, Effect.components, Component.Covers])
  refine ⟨fuel, t, run, hr, ?_, he.rip, ?_, ?_, ?_, ?_, he.agrees⟩
  · intro a b hab
    rw [hm]
    exact loaded a b hab
  · have h := P256.Proofs.ReadBe.bswap_input_memLoad_limb bytes 0 (by decide +kernel)
    change bswap64 (memLoad s.external (s.regValue .rsi + (0 : BitVec 64)) 64) =
      BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.octetsToNat input / 2^192) at h
    have hz : s.regValue .rsi + (0 : BitVec 64) = s.regValue .rsi := BitVec.add_zero _
    rw [hz] at h
    exact he.writes.1.trans h
  · exact he.writes.2.1.trans (P256.Proofs.ReadBe.bswap_input_memLoad_limb bytes 1 (by decide +kernel))
  · exact he.writes.2.2.1.trans (P256.Proofs.ReadBe.bswap_input_memLoad_limb bytes 2 (by decide +kernel))
  · have h := P256.Proofs.ReadBe.bswap_input_memLoad_limb bytes 3 (by decide +kernel)
    change bswap64 (memLoad s.external (s.regValue .rsi + 24) 64) =
      BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.octetsToNat input / 1) at h
    rw [Nat.div_one] at h
    exact he.writes.2.2.2.trans h

end P256.Proofs.Sec1.Decompress.Input
