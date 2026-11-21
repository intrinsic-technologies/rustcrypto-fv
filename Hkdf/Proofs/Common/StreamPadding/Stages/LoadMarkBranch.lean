import Hkdf.Proofs.Common.StreamPadding.Layout
import Hkdf.Proofs.Common.Instructions.XorImmediate
import Hkdf.Proofs.Common.Instructions.ForgetFlags
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Stages

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field
open Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Instructions.XorImmediate

attribute [local x86_compose] Variant.hashIndex Variant.lengthIndex Variant.blocksIndex
  Variant.remainingIndex Variant.hashReg Variant.lengthReg Variant.blocksReg Variant.remainingReg
  regIndex X86.Syntax.Reg.fin BitVec.reduceSetWidth

private theorem pc_add_ne (v : Variant) (point : Point) (offset : Nat)
    (bound : offset ≤ 128) {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip) :
    v.pc point + BitVec.ofNat 64 offset ≠ boundary.rip := by
  apply boundary_ne_program outside
  have lower : 0x100000 ≤ (v.pc point).toNat := by cases v <;> cases point <;> decide
  have upper : (v.pc point).toNat ≤ 0x11768f := by cases v <;> cases point <;> decide
  have eqpc : v.pc point = Extracted.textAddress +
      BitVec.ofNat 64 ((v.pc point).toNat - 0x100000) := by
    cases v <;> cases point <;> rfl
  rw [eqpc]
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    inProgram_of_textOffset ((v.pc point).toNat - 0x100000 + offset) (by omega)


def tailLengthAM : Variant → AddrMode
  | .key => .sib 4 none 0 (.d8 127)
  | .hmac | .simpleInner | .simpleOuter => .sib 4 none 0 (.d32 135)

def loadByteLen (v : Variant) : Nat :=
  (encodeMovzxR32M8 (v.lengthIndex.setWidth 4) (tailLengthAM v)).length

def loadBytes (v : Variant) : List UInt8 :=
  encodeLeaR64M (v.hashIndex.setWidth 4) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.hash))) ++
  encodeMovzxR32M8 (v.lengthIndex.setWidth 4) (tailLengthAM v) ++
  encodeMovR64M64 (v.blocksIndex.setWidth 4) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.counter))) ++
  encodeMovR64R64 (v.remainingIndex.setWidth 4) (v.lengthIndex.setWidth 4) ++
  [0x49,0x83,(if v = .simpleInner then 0xf4 else 0xf7),0x3f]

structure LoadPre (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = v.pc .entry
  tailLength : MemReadable s (rspOf s + BitVec.ofNat 64 (v.tail + 63)) 1
  blocks : MemReadable s (rspOf s + BitVec.ofNat 64 v.counter) 8

def loadEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc .mark
    writes := [
      ⟨(.reg v.hashIndex : Operand 64), rspOf s + BitVec.ofNat 64 v.hash⟩,
      ⟨(.reg v.lengthIndex : Operand 64), (memLoad s.external
        (rspOf s + BitVec.ofNat 64 (v.tail + 63)) 8).setWidth 64⟩,
      ⟨(.reg v.blocksIndex : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 v.counter) 64⟩,
      ⟨(.reg v.remainingIndex : Operand 64), (memLoad s.external
        (rspOf s + BitVec.ofNat 64 (v.tail + 63)) 8).setWidth 64 ^^^ 63⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem load_code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc .entry) (loadBytes v)) s := by
  cases v
  · exact programText_slice (programLoaded_codeIn loaded) 0x16442 (loadBytes .key)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xddb3 (loadBytes .hmac)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x17297 (loadBytes .simpleInner)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x17535 (loadBytes .simpleOuter)
      (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1200000 in
theorem load_run [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (LoadPre v) (codeRange (v.pc .entry) (loadBytes v))
      (Effect.post (loadEffect v)) := by
  advance_begin (show StepEffect (fun s : RamState => s.RIP = v.pc .entry)
    (codeRange (v.pc .entry) (encodeLeaR64M (v.hashIndex.setWidth 4)
      (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.hash)))))
    (leaR64Effect (v.pc .entry) v.hashIndex (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.hash)))) from
    (by
      cases v
      · exact lea_r64_effect_step _ 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl
      · exact lea_r64_effect_step _ 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl
      · exact lea_r64_effect_step _ 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl
      · exact lea_r64_effect_step _ 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .entry) (loadBytes .key) 0 8
    · exact codeRange_slice_subset (Variant.hmac.pc .entry) (loadBytes .hmac) 0 8
    · exact codeRange_slice_subset (Variant.simpleInner.pc .entry) (loadBytes .simpleInner) 0 8
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .entry) (loadBytes .simpleOuter) 0 8
  case next => exact fun _ _ ↦ pc_add_ne v .entry 8 (by decide) outside
  advance_then (show StepEffect
      (X86Proofs.LoadPre (v.pc .entry + 8)
        (fun s => (tailLengthAM v).addr s (v.pc .entry + 8 + BitVec.ofNat 64 (loadByteLen v))) 1)
      (codeRange (v.pc .entry + 8) (encodeMovzxR32M8 (v.lengthIndex.setWidth 4) (tailLengthAM v)))
      (movzxR32M8Effect (v.pc .entry + 8) (loadByteLen v) v.lengthIndex (tailLengthAM v)) from
    (by
      cases v
      · exact movzx_r_m8_rex_effect_step _ 0x44 (by simp [RexPrefix]) 32
          (.inr rfl) (fun _ => rfl) 4 (.sib 4 none 0 (.d8 127)) (by decide) rfl rfl
      · exact movzx_r_m8_rex_effect_step _ 0x44 (by simp [RexPrefix]) 32
          (.inr rfl) (fun _ => rfl) 4 (.sib 4 none 0 (.d32 135)) (by decide) rfl rfl
      · exact movzx_r_m8_rex_effect_step _ 0x44 (by simp [RexPrefix]) 32
          (.inr rfl) (fun _ => rfl) 5 (.sib 4 none 0 (.d32 135)) (by decide) rfl rfl
      · exact movzx_r_m8_rex_effect_step _ 0x44 (by simp [RexPrefix]) 32
          (.inr rfl) (fun _ => rfl) 4 (.sib 4 none 0 (.d32 135)) (by decide) rfl rfl))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .entry) (loadBytes .key) 8 6
    · exact codeRange_slice_subset (Variant.hmac.pc .entry) (loadBytes .hmac) 8 9
    · exact codeRange_slice_subset (Variant.simpleInner.pc .entry) (loadBytes .simpleInner) 8 9
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .entry) (loadBytes .simpleOuter) 8 9
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm; all_goals cases v <;> rfl) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · cases v <;> x86_norm <;> exact hp.tailLength
    · x86_norm
      have hn := pc_add_ne v .entry (8 + loadByteLen v) (by cases v <;> decide) outside
      cases v <;> exact hn
  advance_then (show StepEffect
      (X86Proofs.LoadPre (v.pc .entry + BitVec.ofNat 64 (8 + loadByteLen v))
        (fun s => (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.counter)) : AddrMode).addr s
          (v.pc .entry + BitVec.ofNat 64 (16 + loadByteLen v))) 8)
      (codeRange (v.pc .entry + BitVec.ofNat 64 (8 + loadByteLen v))
        (encodeMovR64M64 (v.blocksIndex.setWidth 4)
          (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.counter)))))
      (movR64M64Effect (v.pc .entry + BitVec.ofNat 64 (8 + loadByteLen v)) v.blocksIndex
        (.sib 4 none 0 (.d32 (BitVec.ofNat 32 v.counter)))) from
    (by
      cases v
      · exact mov_r64_m64_effect_step _ 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl
      · exact mov_r64_m64_effect_step _ 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl
      · exact mov_r64_m64_effect_step _ 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl
      · exact mov_r64_m64_effect_step _ 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .entry) (loadBytes .key) 14 8
    · exact codeRange_slice_subset (Variant.hmac.pc .entry) (loadBytes .hmac) 17 8
    · exact codeRange_slice_subset (Variant.simpleInner.pc .entry) (loadBytes .simpleInner) 17 8
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .entry) (loadBytes .simpleOuter) 17 8
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm; all_goals cases v <;> rfl) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · cases v <;> x86_norm <;> exact hp.blocks
    · x86_norm
      have hn := pc_add_ne v .entry (8 + loadByteLen v + 8) (by cases v <;> decide) outside
      cases v <;> exact hn
  advance_then (show StepEffect
      (fun s : RamState => s.RIP = v.pc .entry + BitVec.ofNat 64 (16 + loadByteLen v))
      (codeRange (v.pc .entry + BitVec.ofNat 64 (16 + loadByteLen v))
        (encodeMovR64R64 (v.remainingIndex.setWidth 4) (v.lengthIndex.setWidth 4)))
      (movR64R64Effect (v.pc .entry + BitVec.ofNat 64 (16 + loadByteLen v)) v.remainingIndex v.lengthIndex) from
    (by
      cases v
      · exact mov_r64_r64_effect_step _ 0x4d 0xe7 (by simp [RexWPrefix]) rfl
      · exact mov_r64_r64_effect_step _ 0x4d 0xe7 (by simp [RexWPrefix]) rfl
      · exact mov_r64_r64_effect_step _ 0x4d 0xec (by simp [RexWPrefix]) rfl
      · exact mov_r64_r64_effect_step _ 0x4d 0xe7 (by simp [RexWPrefix]) rfl))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .entry) (loadBytes .key) 22 3
    · exact codeRange_slice_subset (Variant.hmac.pc .entry) (loadBytes .hmac) 25 3
    · exact codeRange_slice_subset (Variant.simpleInner.pc .entry) (loadBytes .simpleInner) 25 3
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .entry) (loadBytes .simpleOuter) 25 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm
      cases v <;> rfl
    · x86_norm
      have hn := pc_add_ne v .entry (19 + loadByteLen v) (by cases v <;> decide) outside
      cases v <;> exact hn
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect
      (fun s : RamState => s.RIP = v.pc .entry + BitVec.ofNat 64 (19 + loadByteLen v))
      (codeRange (v.pc .entry + BitVec.ofNat 64 (19 + loadByteLen v))
        [0x49,0x83,(if v = .simpleInner then 0xf4 else 0xf7),63])
      (xorR64Imm8Effect
      (v.pc .entry + BitVec.ofNat 64 (19 + loadByteLen v)) v.remainingIndex 63) from
      (by
      cases v
      · exact xor_r64_imm8_effect_step _ 0x49 0xf7 63 (by simp [RexWPrefix]) rfl rfl
      · exact xor_r64_imm8_effect_step _ 0x49 0xf7 63 (by simp [RexWPrefix]) rfl rfl
      · exact xor_r64_imm8_effect_step _ 0x49 0xf4 63 (by simp [RexWPrefix]) rfl rfl
      · exact xor_r64_imm8_effect_step _ 0x49 0xf7 63 (by simp [RexWPrefix]) rfl rfl))))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .entry) (loadBytes .key) 25 4
    · exact codeRange_slice_subset (Variant.hmac.pc .entry) (loadBytes .hmac) 28 4
    · exact codeRange_slice_subset (Variant.simpleInner.pc .entry) (loadBytes .simpleInner) 28 4
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .entry) (loadBytes .simpleOuter) 28 4
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm; all_goals cases v <;> rfl), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect,
        Effect.components, Component.Covers]
    · x86_norm
      have hn := pc_add_ne v .entry (23 + loadByteLen v) (by cases v <;> decide) outside
      cases v <;> exact hn
  cases v <;> advance_finish [loadEffect, Variant.pc, Variant.hash, Variant.counter,
    Variant.tail, tailLengthAM, loadByteLen, Variant.hashIndex, Variant.lengthIndex,
    Variant.blocksIndex, Variant.remainingIndex, Variant.hashReg, Variant.lengthReg,
    Variant.blocksReg, Variant.remainingReg, regIndex, X86.Syntax.Reg.fin, (show (12 : Fin 16).val = 12 from rfl),
          (show (13 : Fin 16).val = 13 from rfl), BitVec.reduceSetWidth]
  all_goals cases v <;> x86_full


attribute [local x86_compose] movM8Imm8RexEffect addR64Imm8Effect
  BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero

structure MarkPre (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = v.pc .mark
  writable : MemWritable s (rspOf s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 v.tail) 1
  codeApart : RangeApart (rspOf s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 v.tail) 1
    (v.pc .mark) 19

def markBytes (v : Variant) : List UInt8 :=
  [0x42,0xc6,0x44,(if v = .simpleInner then 0x2c else 0x24),UInt8.ofNat v.tail,0x80,0x4a,0x8d,0x3c,(if v = .simpleInner then 0x2c else 0x24),
    0x48,0x83,0xc7,UInt8.ofNat (v.tail+1),0x31,0xf6,0x4c,0x89,(if v = .simpleInner then 0xe2 else 0xfa)]

def markEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc .fillCall
    writes := [
      ⟨(.mem (rspOf s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 v.tail) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 (v.tail+1)⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (.reg v.remainingIndex : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem mark_code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc .mark) (markBytes v)) s := by
  cases v
  · exact programText_slice (programLoaded_codeIn loaded) 0x1645f (markBytes .key)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xddd3 (markBytes .hmac)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x172b7 (markBytes .simpleInner)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x17555 (markBytes .simpleOuter)
      (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1200000 in
theorem mark_run [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (MarkPre v) (codeRange (v.pc .mark) (markBytes v))
      (Effect.post (markEffect v)) := by
  advance_begin (mov_m8_imm8_rex_effect_step (v.pc .mark) 0x42 (by simp [RexPrefix])
    (.sib 4 (some (v.lengthIndex.setWidth 4)) 0 (.d8 (BitVec.ofNat 8 v.tail))) (by cases v <;> decide) (by cases v <;> rfl) rfl 128)
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .mark) (markBytes .key) 0 6
    · exact codeRange_slice_subset (Variant.hmac.pc .mark) (markBytes .hmac) 0 6
    · exact codeRange_slice_subset (Variant.simpleInner.pc .mark) (markBytes .simpleInner) 0 6
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .mark) (markBytes .simpleOuter) 0 6
  case pre =>
    intro s hp
    refine ⟨hp.rip, ?_, ?_⟩
    · cases v <;> x86_norm <;>
        simpa only [rspOf, Operand.read, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, Variant.tail,
          Nat.reduceAdd, BitVec.reduceSignExtend, Variant.lengthIndex, Variant.lengthReg,
          regIndex, X86.Syntax.Reg.fin, (show (12 : Fin 16).val = 12 from rfl),
          (show (13 : Fin 16).val = 13 from rfl), BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat] using hp.writable
    · cases v <;> x86_norm
      all_goals intro i hi j hj
      all_goals simpa only [rspOf, Operand.read, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, Variant.tail,
          Nat.reduceAdd, BitVec.reduceSignExtend, Variant.lengthIndex, Variant.lengthReg,
          regIndex, X86.Syntax.Reg.fin, (show (12 : Fin 16).val = 12 from rfl),
          (show (13 : Fin 16).val = 13 from rfl), BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat] using
        hp.codeApart i hi j (by omega)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    cases v <;> x86_norm <;>
      simpa only [rspOf, Operand.read, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, Variant.tail,
          Nat.reduceAdd, BitVec.reduceSignExtend, Variant.lengthIndex, Variant.lengthReg,
          regIndex, X86.Syntax.Reg.fin, (show (12 : Fin 16).val = 12 from rfl),
          (show (13 : Fin 16).val = 13 from rfl), BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat] using hp.codeApart
  case next => exact fun _ _ ↦ pc_add_ne v .mark 6 (by decide) outside
  advance_then (show StepEffect _ _ (leaR64Effect (v.pc .mark+6) 7
      (.sib 4 (some (v.lengthIndex.setWidth 4)) 0 .none)) from
    lea_r64_effect_step _ 0x4a (by simp [RexWPrefix]) 7
      (.sib 4 (some (v.lengthIndex.setWidth 4)) 0 .none) (by cases v <;> decide) (by cases v <;> rfl) rfl)
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .mark) (markBytes .key) 6 4
    · exact codeRange_slice_subset (Variant.hmac.pc .mark) (markBytes .hmac) 6 4
    · exact codeRange_slice_subset (Variant.simpleInner.pc .mark) (markBytes .simpleInner) 6 4
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .mark) (markBytes .simpleOuter) 6 4
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm; all_goals cases v <;> rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      (by x86_norm; exact pc_add_ne v .mark 10 (by decide) outside)⟩
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (addR64Imm8Effect (v.pc .mark+10) 7 (BitVec.ofNat 8 (v.tail+1))) from
      add_r64_imm8_effect_step _ 0x48 0xc7 (BitVec.ofNat 8 (v.tail+1))
        (by simp [RexWPrefix]) rfl rfl)))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .mark) (markBytes .key) 10 4
    · exact codeRange_slice_subset (Variant.hmac.pc .mark) (markBytes .hmac) 10 4
    · exact codeRange_slice_subset (Variant.simpleInner.pc .mark) (markBytes .simpleInner) 10 4
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .mark) (markBytes .simpleOuter) 10 4
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm; all_goals cases v <;> rfl), Effect.Avoids.of_noMem ?_ _,
      (by x86_norm; exact pc_add_ne v .mark 14 (by decide) outside)⟩
    simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, addR64Imm8Effect,
      Effect.components, Component.Covers]
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR32R32Effect (v.pc .mark+14) 2 6 6) from
      xor_r32_r32_effect_step _ 0xf6 rfl)))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .mark) (markBytes .key) 14 2
    · exact codeRange_slice_subset (Variant.hmac.pc .mark) (markBytes .hmac) 14 2
    · exact codeRange_slice_subset (Variant.simpleInner.pc .mark) (markBytes .simpleInner) 14 2
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .mark) (markBytes .simpleOuter) 14 2
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm; all_goals cases v <;> rfl), Effect.Avoids.of_noMem ?_ _,
      (by x86_norm; exact pc_add_ne v .mark 16 (by decide) outside)⟩
    simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, xorR32R32Effect,
      Effect.components, Component.Covers]
  advance_then (show StepEffect (fun s : RamState => s.RIP = v.pc .mark + (16 : BitVec 64))
      (codeRange (v.pc .mark+16)
        (encodeMovR64R64 2 (v.remainingIndex.setWidth 4)))
      (movR64R64Effect (v.pc .mark+16) 2 v.remainingIndex) from
    (by
      cases v
      · exact mov_r64_r64_effect_step _ 0x4c 0xfa (by simp [RexWPrefix]) rfl
      · exact mov_r64_r64_effect_step _ 0x4c 0xfa (by simp [RexWPrefix]) rfl
      · exact mov_r64_r64_effect_step _ 0x4c 0xe2 (by simp [RexWPrefix]) rfl
      · exact mov_r64_r64_effect_step _ 0x4c 0xfa (by simp [RexWPrefix]) rfl))
  case sub =>
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .mark) (markBytes .key) 16 3
    · exact codeRange_slice_subset (Variant.hmac.pc .mark) (markBytes .hmac) 16 3
    · exact codeRange_slice_subset (Variant.simpleInner.pc .mark) (markBytes .simpleInner) 16 3
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .mark) (markBytes .simpleOuter) 16 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm; all_goals cases v <;> rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      (by x86_norm; exact pc_add_ne v .mark 19 (by decide) outside)⟩
  cases v <;> advance_finish [markEffect, Variant.pc, Variant.tail, Variant.lengthIndex, Variant.lengthReg,
    Variant.remainingIndex, Variant.remainingReg, regIndex, X86.Syntax.Reg.fin, (show (12 : Fin 16).val = 12 from rfl),
          (show (13 : Fin 16).val = 13 from rfl), BitVec.reduceSetWidth]


def branchDisp : Variant → BitVec 32
  | .key => 0xbc
  | .hmac | .simpleInner | .simpleOuter => 0xa4

def branchBytes (v : Variant) : List UInt8 :=
  [0x49,0x83,(if v = .simpleInner then 0xfc else 0xff),7,0x0f,0x87] ++ immBytes 32 (branchDisp v)

theorem branch_code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc .branch) (branchBytes v)) s := by
  cases v
  · exact programText_slice (programLoaded_codeIn loaded) 0x16478 (branchBytes .key)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xddec (branchBytes .hmac)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x172d0 (branchBytes .simpleInner)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x1756e (branchBytes .simpleOuter)
      (by decide +kernel) (by decide +kernel)

theorem branch_run [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) {s : RamState}
    (ready : ReadyToStep s) (loaded : CodeIn (codeRange (v.pc .branch) (branchBytes v)) s)
    (rip : s.RIP = v.pc .branch) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue v.remainingReg).toNat < 8 then v.pc .firstHead else v.pc .length) ∧
      AgreesExcept [.flags, .rip] s t := by
  have firstCode : CodeIn (codeRange (v.pc .branch) [0x49,0x83,(if v = .simpleInner then 0xfc else 0xff),7]) s := by
    apply loaded.mono
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .branch) (branchBytes .key) 0 4
    · exact codeRange_slice_subset (Variant.hmac.pc .branch) (branchBytes .hmac) 0 4
    · exact codeRange_slice_subset (Variant.simpleInner.pc .branch) (branchBytes .simpleInner) 0 4
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .branch) (branchBytes .simpleOuter) 0 4
  obtain ⟨u, run, readyU, compared⟩ :=
    (show StepEffect (fun s : RamState => s.RIP = v.pc .branch)
      (codeRange (v.pc .branch) [0x49,0x83,(if v = .simpleInner then 0xfc else 0xff),7])
      (cmpR64Imm8Effect (v.pc .branch) v.remainingIndex 7) from
      (by
      cases v
      · exact cmp_r64_imm8_effect_step _ 0x49 0xff 7 (by simp [RexWPrefix]) rfl rfl
      · exact cmp_r64_imm8_effect_step _ 0x49 0xff 7 (by simp [RexWPrefix]) rfl rfl
      · exact cmp_r64_imm8_effect_step _ 0x49 0xfc 7 (by simp [RexWPrefix]) rfl rfl
      · exact cmp_r64_imm8_effect_step _ 0x49 0xff 7 (by simp [RexWPrefix]) rfl rfl)).advances ready firstCode rip
      (pc_add_ne v .branch 4 (by decide) outside)
  have frame : AgreesExcept [.flags, .rip] s u := compared.agrees
  have nextCode : CodeIn (codeRange (v.pc .branch+4)
      ([0x0f,0x87] ++ immBytes 32 (branchDisp v))) u := by
    apply (frame.codeIn (by simp [Component.Covers]) loaded).mono
    cases v
    · exact codeRange_slice_subset (Variant.key.pc .branch) (branchBytes .key) 4 6
    · exact codeRange_slice_subset (Variant.hmac.pc .branch) (branchBytes .hmac) 4 6
    · exact codeRange_slice_subset (Variant.simpleInner.pc .branch) (branchBytes .simpleInner) 4 6
    · exact codeRange_slice_subset (Variant.simpleOuter.pc .branch) (branchBytes .simpleOuter) 4 6
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step
    (v.pc .branch+4) 7 (branchDisp v) u readyU nextCode
    ⟨compared.rip, by cases v <;> intro _ <;> decide +kernel⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = (s.regValue v.remainingReg).ult 7 := by
    cases v <;> exact compared.flags.1
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue v.remainingReg - 7 == 0) := by
    cases v <;> exact compared.flags.2.2.2.1
  have jumpTarget : branchTarget (v.pc .branch+4) 6 ((branchDisp v).signExtend 64) =
      v.pc .length := by cases v <;> rfl
  have fallTarget : v.pc .branch+4+6 = v.pc .firstHead := by cases v <;> rfl
  have target : t.RIP =
      (if (s.regValue v.remainingReg).toNat < 8 then v.pc .firstHead else v.pc .length) := by
    rw [jumped.rip]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
      then branchTarget (v.pc .branch+4) 6 ((branchDisp v).signExtend 64)
      else v.pc .branch+4+6) = _
    rw [jumpTarget, fallTarget, carry, zero]
    have zeroEq : (s.regValue v.remainingReg - 7 == 0) = decide ((s.regValue v.remainingReg).toNat = 7) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · exact congrArg BitVec.toNat
      · intro h
        apply BitVec.eq_of_toNat_eq
        exact h
    rw [zeroEq]
    have cond : (!((s.regValue v.remainingReg).ult 7 || decide ((s.regValue v.remainingReg).toNat = 7))) =
        decide (8 ≤ (s.regValue v.remainingReg).toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
        decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
      omega
    rw [cond]
    by_cases small : (s.regValue v.remainingReg).toNat < 8
    · simp only [small, show ¬8 ≤ (s.regValue v.remainingReg).toNat by omega,
        decide_false, Bool.false_eq_true, ↓reduceIte]
    · simp only [small, show 8 ≤ (s.regValue v.remainingReg).toNat by omega,
        decide_true, ↓reduceIte]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · simpa only [BitVec.add_zero] using pc_add_ne v .firstHead 0 (by decide) outside
    · simpa only [BitVec.add_zero] using pc_add_ne v .length 0 (by decide) outside
  exact ⟨t, run.trans advance, readyT, target,
    (frame.trans jumped.agrees).mono (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])⟩

end Hkdf.Proofs.Common.StreamPadding.Stages
