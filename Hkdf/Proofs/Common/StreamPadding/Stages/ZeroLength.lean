import Hkdf.Proofs.Common.StreamPadding.Layout
import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Instructions.ShiftLeft.Word32Rex
import Hkdf.Proofs.Common.Instructions.Bswap
import Hkdf.Proofs.Common.Instructions.ForgetFlags
import Hkdf.Proofs.Common.Instructions.Or
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Stages

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Instructions.Or (orR64R64Effect or_r64_r64_effect_step)
open Hkdf.Proofs.Common.Instructions.ShiftLeft

private def zeroOffsets : List Nat := [0,8,16,24,32,40,48]

structure ZeroPre (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = v.pc .zero
  writable : ∀ i ∈ zeroOffsets, MemWritable s (rspOf s + BitVec.ofNat 64 (v.tail+i)) 8
  codeApart : ∀ i ∈ zeroOffsets, RangeApart (rspOf s + BitVec.ofNat 64 (v.tail+i)) 8 (v.pc .zero) 63

private def zeroStoreBytes (v : Variant) (i : Nat) : List UInt8 :=
  [0x48,0xc7,0x44,0x24,UInt8.ofNat (v.tail+i),0,0,0,0]

private def zeroBytes (v : Variant) : List UInt8 :=
  zeroStoreBytes v 0 ++ zeroStoreBytes v 8 ++ zeroStoreBytes v 16 ++
  zeroStoreBytes v 24 ++ zeroStoreBytes v 32 ++ zeroStoreBytes v 40 ++ zeroStoreBytes v 48

def zeroEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc .length
    writes := [⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+0)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+8)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+16)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+24)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+32)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+40)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+48)) : Operand 64), 0⟩] }

@[local x86_compose] private theorem tail_offsets_sub (v : Variant) (i j : Nat) :
    BitVec.ofNat 64 (v.tail+i) - BitVec.ofNat 64 (v.tail+j) =
      BitVec.ofNat 64 i - BitVec.ofNat 64 j := by
  simp only [BitVec.ofNat_add]
  bv_omega

@[local x86_local] private theorem stack_zero_local (p a : BitVec 64) :
    Effect.Local (storeEffect p 9 (fun s => rspOf s+a) (fun _ => (0 : BitVec 64))) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, rspOf, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

private theorem zero_store_step [Bindings] (v : Variant) (i : Nat) (hi : i ∈ zeroOffsets)
    (p : BitVec 64) :
    StepEffect (StorePre p 9 (fun s => rspOf s + BitVec.ofNat 64 (v.tail+i)) 8)
      (codeRange p (zeroStoreBytes v i))
      (storeEffect p 9 (fun s => rspOf s + BitVec.ofNat 64 (v.tail+i)) (fun _ => (0 : BitVec 64))) := by
  have h := mov_m64_imm32_effect_step p 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (v.tail+i)))) (by simp [AddrMode.Valid, regLow]) rfl rfl 0
  simp only [zeroOffsets, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases v <;>
    exact h


private theorem zero_internal (v : Variant) (i : Nat) (hi : i ≤ 63) :
    InProgram (v.pc .zero + BitVec.ofNat 64 i) := by
  cases v with
  | key =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0x164ff+i) (by omega)
  | hmac =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0xde5b+i) (by omega)
  | simpleInner =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0x1733f+i) (by omega)
  | simpleOuter =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0x175dd+i) (by omega)

theorem zero_code {s : RamState} (v : Variant) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc .zero) (zeroBytes v)) s := by
  cases v with
  | key =>
    exact programText_slice (programLoaded_codeIn loaded) 0x164ff _
      (by decide +kernel) (by decide +kernel)
  | hmac =>
    exact programText_slice (programLoaded_codeIn loaded) 0xde5b _
      (by decide +kernel) (by decide +kernel)
  | simpleInner =>
    exact programText_slice (programLoaded_codeIn loaded) 0x1733f _
      (by decide +kernel) (by decide +kernel)
  | simpleOuter =>
    exact programText_slice (programLoaded_codeIn loaded) 0x175dd _
      (by decide +kernel) (by decide +kernel)

theorem zero_run [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ZeroPre v) (codeRange (v.pc .zero) (zeroBytes v))
      (Effect.post (zeroEffect v)) := by
  advance_begin (zero_store_step v 0 (by decide) (v.pc .zero))
  case sub => simpa only [zeroBytes, zeroStoreBytes, List.drop, List.take, List.cons_append, BitVec.add_zero] using codeRange_slice_subset (v.pc .zero) (zeroBytes v) 0 9
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 0 (by decide), fun a ha b hb => h.codeApart 0 (by decide) a ha b (by omega)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [zeroBytes, zeroStoreBytes]
    exact h.codeApart 0 (by decide)
  case next =>
    exact fun _ _ => boundary_ne_program outside (zero_internal v 9 (by decide))
  advance_then (zero_store_step v 8 (by decide) (v.pc .zero + 9))
  case sub => exact codeRange_slice_subset (v.pc .zero) (zeroBytes v) 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      intro a ha b hb
      simpa only [rspOf, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        hP.codeApart 8 (by decide) a ha (9+b) (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [zeroBytes, zeroStoreBytes]
      exact hP.codeApart 8 (by decide)
    · apply boundary_ne_program outside
      simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using zero_internal v 18 (by decide)
  advance_then (zero_store_step v 16 (by decide) (v.pc .zero + 18))
  case sub => exact codeRange_slice_subset (v.pc .zero) (zeroBytes v) 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      intro a ha b hb
      simpa only [rspOf, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        hP.codeApart 16 (by decide) a ha (18+b) (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [zeroBytes, zeroStoreBytes]
      exact hP.codeApart 16 (by decide)
    · apply boundary_ne_program outside
      simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using zero_internal v 27 (by decide)
  advance_then (zero_store_step v 24 (by decide) (v.pc .zero + 27))
  case sub => exact codeRange_slice_subset (v.pc .zero) (zeroBytes v) 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      intro a ha b hb
      simpa only [rspOf, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        hP.codeApart 24 (by decide) a ha (27+b) (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [zeroBytes, zeroStoreBytes]
      exact hP.codeApart 24 (by decide)
    · apply boundary_ne_program outside
      simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using zero_internal v 36 (by decide)
  advance_then (zero_store_step v 32 (by decide) (v.pc .zero + 36))
  case sub => exact codeRange_slice_subset (v.pc .zero) (zeroBytes v) 36 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      intro a ha b hb
      simpa only [rspOf, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        hP.codeApart 32 (by decide) a ha (36+b) (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [zeroBytes, zeroStoreBytes]
      exact hP.codeApart 32 (by decide)
    · apply boundary_ne_program outside
      simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using zero_internal v 45 (by decide)
  advance_then (zero_store_step v 40 (by decide) (v.pc .zero + 45))
  case sub => exact codeRange_slice_subset (v.pc .zero) (zeroBytes v) 45 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by decide)
    · x86_norm
      intro a ha b hb
      simpa only [rspOf, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        hP.codeApart 40 (by decide) a ha (45+b) (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [zeroBytes, zeroStoreBytes]
      exact hP.codeApart 40 (by decide)
    · apply boundary_ne_program outside
      simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using zero_internal v 54 (by decide)
  advance_then (zero_store_step v 48 (by decide) (v.pc .zero + 54))
  case sub => exact codeRange_slice_subset (v.pc .zero) (zeroBytes v) 54 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by decide)
    · x86_norm
      intro a ha b hb
      simpa only [rspOf, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        hP.codeApart 48 (by decide) a ha (54+b) (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [zeroBytes, zeroStoreBytes]
      exact hP.codeApart 48 (by decide)
    · apply boundary_ne_program outside
      simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using zero_internal v 63 (by decide)
  have hpc : v.pc .zero + 63#64 = v.pc .length := by cases v <;> rfl
  advance_finish [zeroEffect, hpc]

attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64

@[local x86_local] theorem shift64_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Hkdf.Proofs.Common.Instructions.Effect.forgetFlags (shlR64Effect p n r c s)) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, shlR64Effect, h.read_reg]
  · intro s
    simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, shlR64Effect, Write.Full, Operand.Full]

@[local x86_local] theorem shift32_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Hkdf.Proofs.Common.Instructions.Effect.forgetFlags (shlR32Effect p n r c s)) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, shlR32Effect, h.read_reg]
  · intro s
    simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, shlR32Effect, Write.Full, Operand.Full]

def lengthByteCount : Variant → Nat
  | .key => 19
  | .hmac | .simpleInner | .simpleOuter => 22

structure LengthPre (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = v.pc .length
  writable : MemWritable s (rspOf s + BitVec.ofNat 64 (v.tail+56)) 8
  codeApart : RangeApart (rspOf s + BitVec.ofNat 64 (v.tail+56)) 8
    (v.pc .length) (lengthByteCount v)

private def lengthStoreBytes : Variant → List UInt8
  | .key => [0x4c,0x89,0x64,0x24,0x78]
  | .hmac | .simpleOuter => [0x4c,0x89,0xa4,0x24,0x80,0,0,0]
  | .simpleInner => [0x4c,0x89,0xac,0x24,0x80,0,0,0]

private def lengthBytes (v : Variant) : List UInt8 :=
  (match v with
  | .simpleInner => [0x48,0xc1,0xe5,9,0x41,0xc1,0xe5,3,0x49,9,0xed,0x49,0x0f,0xcd]
  | _ => [0x49,0xc1,0xe5,9,0x41,0xc1,0xe4,3,0x4d,9,0xec,0x49,0x0f,0xcc]) ++ lengthStoreBytes v

def lengthEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc .lastHead
    writes := [⟨(.reg v.blocksIndex : Operand 64), (.reg v.blocksIndex : Operand 64).read s <<< 9⟩,
      ⟨(.reg v.lengthIndex : Operand 64), bswap64
        (((.reg v.lengthIndex : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg v.blocksIndex : Operand 64).read s <<< 9))⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.tail+56)) : Operand 64), bswap64
        (((.reg v.lengthIndex : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg v.blocksIndex : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

private theorem length_store_step [Bindings] (v : Variant) (p : BitVec 64) :
    StepEffect (StorePre p (lengthByteCount v-14)
      (fun s => rspOf s + BitVec.ofNat 64 (v.tail+56)) 8)
      (codeRange p (lengthStoreBytes v))
      (storeEffect p (lengthByteCount v-14)
        (fun s => rspOf s + BitVec.ofNat 64 (v.tail+56))
        (fun s => (.reg v.lengthIndex : Operand 64).read s)) := by
  cases v with
  | key =>
    exact mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 4
      (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl
  | hmac | simpleOuter =>
    exact mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 4
      (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl
  | simpleInner =>
    exact mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl

@[local x86_local] private theorem stack_length_local (p a : BitVec 64) (n : Nat) (r : BitVec 5) :
    Effect.Local (storeEffect p n (fun s => rspOf s+a)
      (fun s => (.reg r : Operand 64).read s)) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, rspOf, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

private theorem length_internal (v : Variant) (i : Nat) (hi : i ≤ lengthByteCount v) :
    InProgram (v.pc .length + BitVec.ofNat 64 i) := by
  cases v with
  | key =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0x1653e+i) (by simp only [lengthByteCount] at hi; omega)
  | hmac =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0xde9a+i) (by simp only [lengthByteCount] at hi; omega)
  | simpleInner =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0x1737e+i) (by simp only [lengthByteCount] at hi; omega)
  | simpleOuter =>
    simpa only [Variant.pc, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using
      inProgram_of_textOffset (0x1761c+i) (by simp only [lengthByteCount] at hi; omega)

theorem length_code {s : RamState} (v : Variant) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc .length) (lengthBytes v)) s := by
  cases v with
  | key =>
    exact programText_slice (programLoaded_codeIn loaded) 0x1653e _
      (by decide +kernel) (by decide +kernel)
  | hmac =>
    exact programText_slice (programLoaded_codeIn loaded) 0xde9a _
      (by decide +kernel) (by decide +kernel)
  | simpleInner =>
    exact programText_slice (programLoaded_codeIn loaded) 0x1737e _
      (by decide +kernel) (by decide +kernel)
  | simpleOuter =>
    exact programText_slice (programLoaded_codeIn loaded) 0x1761c _
      (by decide +kernel) (by decide +kernel)

private theorem length_bytes_size (v : Variant) : (lengthBytes v).length = lengthByteCount v := by
  cases v <;> rfl

attribute [local x86_compose] Variant.blocksIndex Variant.blocksReg
  Variant.lengthIndex Variant.lengthReg regIndex X86.Syntax.Reg.fin

set_option maxHeartbeats 400000 in
theorem length_run [Bindings] (v : Variant) (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (LengthPre v)
      (codeRange (v.pc .length) (lengthBytes v)) (Effect.post (lengthEffect v)) := by
  have hpc : v.pc .length + (14#64 + BitVec.ofNat 64 (lengthByteCount v-14)) = v.pc .lastHead := by cases v <;> rfl
  have hend : InProgram (v.pc .lastHead) := by
    cases v with
    | key => exact inProgram_of_textOffset 0x16551 (by decide)
    | hmac => exact inProgram_of_textOffset 0xdeb0 (by decide)
    | simpleInner => exact inProgram_of_textOffset 0x17394 (by decide)
    | simpleOuter => exact inProgram_of_textOffset 0x17632 (by decide)
  cases v
  case' key =>
    let v := Variant.key
    change AdvanceTriple boundary (LengthPre v)
      (codeRange (v.pc .length) (lengthBytes v)) (Effect.post (lengthEffect v))
  case' hmac =>
    let v := Variant.hmac
    change AdvanceTriple boundary (LengthPre v)
      (codeRange (v.pc .length) (lengthBytes v)) (Effect.post (lengthEffect v))
  case' simpleInner =>
    let v := Variant.simpleInner
    change AdvanceTriple boundary (LengthPre v)
      (codeRange (v.pc .length) (lengthBytes v)) (Effect.post (lengthEffect v))
  case' simpleOuter =>
    let v := Variant.simpleOuter
    change AdvanceTriple boundary (LengthPre v)
      (codeRange (v.pc .length) (lengthBytes v)) (Effect.post (lengthEffect v))
  all_goals
    advance_begin (StepEffect.forgetFlags (h :=
      (show StepEffect (fun s => s.RIP = v.pc .length)
        (codeRange (v.pc .length) ((lengthBytes v).take 4))
        (shlR64Effect (v.pc .length) 4 v.blocksIndex 9) from
        by
          first
          | exact shl_r64_imm8_effect_step _ 0x49 0xe5 9 (by simp [RexWPrefix]) rfl rfl
          | exact shl_r64_imm8_effect_step _ 0x48 0xe5 9 (by simp [RexWPrefix]) rfl rfl)))
    x86_norm [v]
    case next => exact fun _ _ => boundary_ne_program outside (length_internal v 4 (by decide))
    advance_then (StepEffect.forgetFlags (h :=
      (show StepEffect (fun s => s.RIP = v.pc .length + 4#64)
        (codeRange (v.pc .length + 4) (((lengthBytes v).drop 4).take 4))
        (shlR32Effect (v.pc .length + 4) 4 v.lengthIndex 3) from
        by
          first
          | exact shl_r32_imm8_rex_effect_step _ 0x41 0xe4 3 (by simp [RexNoWPrefix]) rfl rfl
          | exact shl_r32_imm8_rex_effect_step _ 0x41 0xe5 3 (by simp [RexNoWPrefix]) rfl rfl)))
    x86_norm [v]
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [v]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, shlR32Effect, Effect.components,
          Write.component, Operand.component, Component.Covers]
      · apply boundary_ne_program outside
        simpa only [v, Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, shlR32Effect, BitVec.add_assoc, BitVec.reduceAdd] using
          length_internal v 8 (by decide)
    advance_then (StepEffect.forgetFlags (h :=
      (show StepEffect (fun s => s.RIP = v.pc .length + 8#64)
        (codeRange (v.pc .length + 8) (((lengthBytes v).drop 8).take 3))
        (orR64R64Effect (v.pc .length + 8) v.lengthIndex v.blocksIndex) from
        by
          first
          | exact or_r64_r64_effect_step _ 0x4d 0xec (by simp [RexWPrefix]) rfl
          | exact or_r64_r64_effect_step _ 0x49 0xed (by simp [RexWPrefix]) rfl)))
    x86_norm [v]
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [v]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, orR64R64Effect, Effect.components,
          Write.component, Operand.component, Component.Covers]
      · apply boundary_ne_program outside
        simpa only [v, Hkdf.Proofs.Common.Instructions.Effect.forgetFlags, orR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using
          length_internal v 11 (by decide)
    advance_then (bswap_r64_effect_step (v.pc .length + 11) (v.lengthIndex.setWidth 4))
    x86_norm [v]
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [v]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · apply boundary_ne_program outside
        simpa only [v, bswapR64Effect, BitVec.add_assoc, BitVec.reduceAdd] using
          length_internal v 14 (by decide)
    advance_then (length_store_step v (v.pc .length + 14))
    x86_norm [v]
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [v]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [v]
        exact hP.writable
      · x86_norm [v]
        intro a ha b hb
        simpa only [v, rspOf, Operand.read, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart a ha (14+b) (by
            simp only [lengthByteCount] at hb ⊢
            omega)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [v]
        simpa only [v, length_bytes_size, lengthByteCount, rspOf, BitVec.ofNat_eq_ofNat] using hP.codeApart
      · apply boundary_ne_program outside
        simpa only [storeEffect, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, v, Variant.pc,
          lengthByteCount, Nat.reduceSub, BitVec.reduceAdd] using hend
    advance_finish [lengthEffect, hpc, v, Variant.blocksIndex, Variant.blocksReg,
      Variant.lengthIndex, Variant.lengthReg, regIndex]


end Hkdf.Proofs.Common.StreamPadding.Stages
