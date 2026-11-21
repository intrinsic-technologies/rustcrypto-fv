import P256.Proofs.Field.Schoolbook.Bytes
import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Field.Schoolbook.Frame
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Carry
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_avoids adcSpec adc_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable mov_m64_r64_effect_step_any)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Common.Field
open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StorePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cb43
  stack : ∀ c ∈ [24,80], MemReadable s (rspOf s+c) 8
  output : ∀ c ∈ [0,8,16,24,32,40,48,56], Writable s ((Operand.reg 7 : Operand 64).read s+c) 8
  apart : ∀ c ∈ [0,8,16,24,32,40,48,56],
    RangeApart ((Operand.reg 7 : Operand 64).read s+c) 8 0x11cb43 45
  stackOutput : RangeApart ((Operand.reg 7 : Operand 64).read s) 8 (rspOf s+24) 8

def storeBytes : List UInt8 :=
  [0x48,0x8b,0x4c,0x24,0x50,0x48,0x89,0x0f,0x48,0x8b,0x4c,0x24,0x18,
   0x48,0x89,0x4f,0x08,0x4c,0x89,0x57,0x10,0x48,0x89,0x77,0x18,
   0x4c,0x89,0x47,0x20,0x48,0x89,0x47,0x28,0x4c,0x89,0x6f,0x30,
   0x49,0x83,0xd7,0,0x4c,0x89,0x7f,0x38]

def storeEffect (s : RamState) : Effect :=
  let dst := (Operand.reg 7 : Operand 64).read s
  let q0 := (Operand.mem (rspOf s+80) : Operand 64).read s
  let q1 := (Operand.mem (rspOf s+24) : Operand 64).read s
  let high := adcSpec ((Operand.reg 15 : Operand 64).read s) 0 (s.RFLAGS.extractLsb' 0 1)
  { rip := 0x11cb70
    writes := [⟨(Operand.mem dst : Operand 64), q0⟩,
      ⟨(Operand.reg 1 : Operand 64), q1⟩,
      ⟨(Operand.mem (dst+8) : Operand 64), q1⟩,
      ⟨(Operand.mem (dst+16) : Operand 64), (Operand.reg 10 : Operand 64).read s⟩,
      ⟨(Operand.mem (dst+24) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.mem (dst+32) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.mem (dst+40) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(Operand.mem (dst+48) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 15 : Operand 64), high.1⟩,
      ⟨(Operand.mem (dst+56) : Operand 64), high.1⟩]
    flags := some (.ofStatusFlags high.2) }

theorem output_apart {s : RamState} (h : StorePre s) (c : BitVec 64)
    (hc : c ∈ [0,8,16,24,32,40,48,56]) (off len : Nat) (hbound : off+len ≤ 45) :
    RangeApart ((Operand.reg 7 : Operand 64).read s+c) 8
      (0x11cb43 + BitVec.ofNat 64 off) len := by
  intro i hi j hj
  have hap := h.apart c hc i hi (off+j) (by omega)
  simpa only [BitVec.add_assoc, BitVec.ofNat_add] using hap

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem store_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StorePre (codeRange 0x11cb43 storeBytes)
      (Effect.post storeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11cb43 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.stack 80 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb48 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb48 0x48
    (by simp [RexWPrefix]) 1 (.base 7 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 5 3
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 0) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 0 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 0) 8 0x11cb48 3
      rw [hd]
      exact output_apart hP 0 (by simp) 5 3 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 0) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 0 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb4b (by decide))
  advance_then (mov_r64_m64_effect_step 0x11cb4b 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.stack 24 (by simp)
    · exact Effect.avoids_of_components_reg_rip (movR64M64Effect_components _ _ _ _) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb50 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb50 0x48
    (by simp [RexWPrefix]) 1 (.base 7 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 13 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 8) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 8 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 8) 8 0x11cb50 4
      rw [hd]
      exact output_apart hP 8 (by simp) 13 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 8) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 8 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb54 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb54 0x4c
    (by simp [RexWPrefix]) 2 (.base 7 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 17 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 16) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 16 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 16) 8 0x11cb54 4
      rw [hd]
      exact output_apart hP 16 (by simp) 17 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 16) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 16 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb58 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb58 0x48
    (by simp [RexWPrefix]) 6 (.base 7 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 21 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 24) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 24 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 24) 8 0x11cb58 4
      rw [hd]
      exact output_apart hP 24 (by simp) 21 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 24) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 24 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb5c (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb5c 0x4c
    (by simp [RexWPrefix]) 0 (.base 7 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 25 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 32) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 32 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 32) 8 0x11cb5c 4
      rw [hd]
      exact output_apart hP 32 (by simp) 25 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 32) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 32 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb60 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb60 0x48
    (by simp [RexWPrefix]) 0 (.base 7 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 29 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 40) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 40 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 40) 8 0x11cb60 4
      rw [hd]
      exact output_apart hP 40 (by simp) 29 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 40) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 40 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb64 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb64 0x4c
    (by simp [RexWPrefix]) 5 (.base 7 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 33 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 48) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 48 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 48) 8 0x11cb64 4
      rw [hd]
      exact output_apart hP 48 (by simp) 33 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 48) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 48 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb68 (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11cb68 0x49 0xd7 0
    (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 37 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb6c (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cb6c 0x4c
    (by simp [RexWPrefix]) 7 (.base 7 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cb43 storeBytes 41 4
  case mid =>
    intro s t hP hH hO
    have hd : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
      hH.agrees.read (by x86_norm)
    refine ⟨⟨hH.rip_of (by x86_norm), ?_, ?_⟩, ?_, ?_⟩
    · change Writable t ((Operand.reg 7 : Operand 64).read t + 56) 8
      rw [hd]
      exact Writable.of_holds hH (hP.output 56 (by simp))
    · change RangeApart ((Operand.reg 7 : Operand 64).read t + 56) 8 0x11cb6c 4
      rw [hd]
      exact output_apart hP 56 (by simp) 41 4 (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart ((Operand.reg 7 : Operand 64).read t + 56) 8 0x11cb43 45
      rw [hd]
      exact hP.apart 56 (by simp)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb70 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread : memLoad (memStore s.external ((Operand.reg 7 : Operand 64).read s)
      ((Operand.mem (rspOf s+80) : Operand 64).read s)) (rspOf s+24) 64 =
      (Operand.mem (rspOf s+24) : Operand 64).read s := by
    apply memLoad_memStore_rangeApart
    exact hP.stackOutput
  simp only [rspOf] at hread
  apply hH.weaken
  · x86_norm [storeEffect, BitVec.add_zero]
  · x86_norm [storeEffect, Operand.write_reg64, hread, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inr rfl | exact Or.inr hread.symm | rfl | exact hread.symm)
  · intro i; cases i <;> x86_norm [storeEffect] <;> rfl
  · x86_norm [storeEffect, BitVec.add_zero]
    all_goals (try (repeat constructor <;> first | rfl | assumption))

def outputLimbs (s : RamState) : Vector (BitVec 64) 8 :=
  #v[(Operand.mem (rspOf s+80) : Operand 64).read s,
    (Operand.mem (rspOf s+24) : Operand 64).read s,
    (Operand.reg 10 : Operand 64).read s,
    (Operand.reg 6 : Operand 64).read s,
    (Operand.reg 8 : Operand 64).read s,
    (Operand.reg 0 : Operand 64).read s,
    (Operand.reg 13 : Operand 64).read s,
    (adcSpec ((Operand.reg 15 : Operand 64).read s) 0 (s.RFLAGS.extractLsb' 0 1)).1]

theorem storeEffect_memLoad {s t : RamState} (h : (storeEffect s).Holds s t)
    (j : Nat) (hj : j < 8) :
    memLoad t.external ((Operand.reg 7 : Operand 64).read s+BitVec.ofNat 64 (8*j)) 64 =
      (outputLimbs s)[j] := by
  have hw := h.writes
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change memLoad t.external ((Operand.reg 7 : Operand 64).read s + 0#64) 64 = _
    rw [BitVec.add_zero]
    exact hw.1
  · exact hw.2.2.1
  · exact hw.2.2.2.1
  · exact hw.2.2.2.2.1
  · exact hw.2.2.2.2.2.1
  · exact hw.2.2.2.2.2.2.1
  · exact hw.2.2.2.2.2.2.2.1
  · exact hw.2.2.2.2.2.2.2.2.2

theorem storeEffect_bytes {s t : RamState} (h : (storeEffect s).Holds s t)
    (v : Vector Nat 8) (hv : ∀ i : Fin 8, v[i] < wordBase)
    (ha : ∀ i < 64, (s.external[(Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 i]?).isSome)
    (hl : ∀ j (hj : j < 8), (outputLimbs s)[j] = BitVec.ofNat 64 (v[j]'hj)) :
    Bytes t.external ((Operand.reg 7 : Operand 64).read s) 64
      (fun i => UInt8.ofNat (packEight v / 256^i % 256)) := by
  apply bytes_of_memLoad_packEight v hv
  · intro i hi
    exact h.agrees.grow _ (ha i hi)
  · intro j hj
    exact (storeEffect_memLoad h j hj).trans (hl j hj)

end P256.Proofs.Field.Schoolbook
