import Hkdf.Proofs.Common.StreamPadding.Stages.ZeroLength
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Payload
import X86Proofs.Instructions.Or.Generated.AccImm32.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.OuterPad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad
open Hkdf.Proofs.Common.Instructions.ShiftLeft
open Hkdf.Proofs.Common.Instructions.CrossPageStore (Writable)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10f42e
  r15 : s.regValue .r15 = rspOf s + 144
  readable : MemReadable s (rspOf s + 216) 8
  writable : ∀ i ∈ ([72,113,121,128,136] : List Nat),
    Writable s (rspOf s + BitVec.ofNat 64 i) 8
  marker : Writable s (rspOf s + 112) 1
  codeApart : ∀ i ∈ ([72,113,121,128,136] : List Nat),
    ∀ offset len : Nat, offset + len ≤ 63 →
      RangeApart (rspOf s + BitVec.ofNat 64 i) 8
        (0x10f42e + BitVec.ofNat 64 offset) len
  markerApart : ∀ offset len : Nat, offset + len ≤ 63 →
    RangeApart (rspOf s + 112) 1 (0x10f42e + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xd8, 0x00, 0x00, 0x00,
   0xc6, 0x44, 0x24, 0x70, 0x80,
   0x49, 0xc7, 0x47, 0xf0, 0x00, 0x00, 0x00, 0x00,
   0x49, 0xc7, 0x47, 0xe9, 0x00, 0x00, 0x00, 0x00,
   0x49, 0xc7, 0x47, 0xe1, 0x00, 0x00, 0x00, 0x00,
   0x48, 0xc1, 0xe0, 0x09,
   0x48, 0x0d, 0x00, 0x01, 0x00, 0x00,
   0x48, 0x0f, 0xc8,
   0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
   0x48, 0x89, 0x44, 0x24, 0x48]

private theorem bytes_length : bytes.length = 63 := by decide

def lengthWord (s : RamState) : BitVec 64 :=
  bswap64 ((memLoad s.external (rspOf s + 216) 64 <<< 9) ||| 256)

def effect (s : RamState) : Effect :=
  { rip := 0x10f46d
    writes := [⟨(.reg 0 : Operand 64), lengthWord s⟩,
      ⟨(.mem (rspOf s + 112) : Operand 8), 128⟩,
      ⟨(.mem (rspOf s + 128) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 121) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 113) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 136) : Operand 64), lengthWord s⟩,
      ⟨(.mem (rspOf s + 72) : Operand 64), lengthWord s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10f42e bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xf42e bytes
    (by decide +kernel) (by decide +kernel)

attribute [local x86_local] Hkdf.Proofs.Common.StreamPadding.Stages.shift64_local
attribute [local x86_compose] shlR64Effect
  external_write_mem external_write_reg external_after

private def zeroMode (d : BitVec 8) : AddrMode := .base 15 (.d8 d)

private theorem zeroMode_length (d : BitVec 8) : (zeroMode d).tail.length = 1 := rfl

private def zeroEffect (pc : BitVec 64) (offset : Nat) : RamState → Effect :=
  storeEffect pc 8 (fun s => rspOf s + BitVec.ofNat 64 offset) (fun _ => 0#64)

@[local x86_local] private theorem zeroEffect_local (pc : BitVec 64) (offset : Nat) :
    Effect.Local (zeroEffect pc offset) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    have rsp : rspOf s = rspOf t := h.read_reg (n := 64) 4
    simp only [zeroEffect, storeEffect, rsp]
  · intro s
    simp [zeroEffect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_compose] zeroEffect

private def ZeroPre (pc : BitVec 64) (offset : Nat) (s : RamState) : Prop :=
  Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre pc 8
    (fun t => rspOf t + BitVec.ofNat 64 offset) 8 s ∧
    s.regValue .r15 = rspOf s + 144

private theorem zeroStep [Bindings] (pc : BitVec 64) (d : BitVec 8) (offset : Nat)
    (hd : 144#64 + d.signExtend 64 = BitVec.ofNat 64 offset) :
    StepEffect (ZeroPre pc offset)
      (codeRange pc (0x49 :: 0xc7 :: (zeroMode d).modrm 0 :: ((zeroMode d).tail ++ immBytes 32 0)))
      (zeroEffect pc offset) := by
  intro s ready code pre
  have addr : ∀ next, (zeroMode d).addr s next = rspOf s + BitVec.ofNat 64 offset := by
    intro next
    change s.regValue .r15 + d.signExtend 64 = _
    rw [pre.2, BitVec.add_assoc]
    exact congrArg (rspOf s + ·) hd
  obtain ⟨t, step, ready', h⟩ :=
    Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
      pc 0x49 (by simp [RexWPrefix]) (zeroMode d) ⟨by decide, fun h => by cases h⟩ rfl rfl 0 s ready code
      ⟨pre.1.rip, by simpa only [storeAddrAt, addr] using pre.1.write,
        by simpa only [storeAddrAt, addr, zeroMode_length, Nat.reduceAdd] using pre.1.code⟩
  refine ⟨t,step,ready',?_⟩
  have signZero : BitVec.signExtend 64 (0 : BitVec 32) = 0#64 := rfl
  simpa only [zeroEffect, movM64Imm32Effect, storeEffect, storeAddrAt, addr,
    zeroMode_length, Nat.reduceAdd, signZero] using h

local macro "outer_zero " out:ident "," pc:term "," d:term "," slot:term "," start:term "," next:term : tactic =>
  `(tactic| (
    advance_then (zeroStep $pc $d $slot (by decide))
    try (case sub => exact codeRange_slice_subset 0x10f42e bytes $start 8)
    case mid =>
      intro s t pre holds obs
      have rsp : rspOf t = rspOf s := by
        have h := (obs true).read_reg (n := 64) 4
        x86_norm at h
        exact h.symm
      have r15 : t.regValue .r15 = s.regValue .r15 := by
        have h := (obs true).read_reg (n := 64) 15
        x86_norm at h
        exact h.symm
      refine ⟨⟨⟨holds.rip_of (by x86_norm), ?_, ?_⟩, by rw [r15, rsp, pre.r15]⟩, ?_, ?_⟩
      · change Writable t (rspOf t + BitVec.ofNat 64 $slot) 8
        rw [rsp]
        exact (pre.writable $slot (by decide)).of_holds holds
      · change RangeApart (rspOf t + BitVec.ofNat 64 $slot) 8 _ 8
        rw [rsp]
        exact pre.codeApart $slot (by decide) $start 8 (by decide)
      · refine Effect.avoids_of_components_mem_rip (a := rspOf t + BitVec.ofNat 64 $slot) (len := 8) ?_ ?_
        · simp only [zeroEffect, storeEffect_components, Nat.reduceDiv]
        · rw [rsp, bytes_length]
          exact pre.codeApart $slot (by decide) 0 63 (by decide)
      · exact boundary_ne_program $out (inProgram_of_textOffset $next (by decide))))

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10f42e bytes) (Effect.post effect) := by
  have shift_nine : shiftCount 64 (UInt8.toBitVec 9) = 9 := rfl
  have zero_stores (m : Ram) (a b : BitVec 64) :
      memLoad (memStore (memStore m a 0#64) b 0#64) a 64 = 0#64 :=
    memLoad_zero_store _ a b (memLoad_memStore m a (by decide) (by decide) 0)
  advance_begin (mov_r64_m64_effect_step 0x10f42e 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
  case pre => exact fun s h => ⟨h.rip,h.readable⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf436 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10f436 (.sib 4 none 0 (.d8 112))
    (by decide) rfl rfl 128)
  case sub => exact codeRange_slice_subset 0x10f42e bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact ⟨hP.marker.low, hP.marker.mem, hP.marker.tables⟩
    · x86_norm
      exact hP.markerApart 8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.markerApart 0 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf43b (by decide))
  outer_zero outside, 0x10f43b, 0xf0, 128, 13, 0xf443
  outer_zero outside, 0x10f443, 0xe9, 121, 21, 0xf44b
  outer_zero outside, 0x10f44b, 0xe1, 113, 29, 0xf453
  advance_then (StepEffect.forgetFlags (h := shl_r64_imm8_effect_step 0x10f453
    0x48 0xe0 9 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10f42e bytes 37 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Effect.forgetFlags, shlR64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf457 (by decide))
  advance_then (StepEffect.forgetFlags (h := or_rax_imm32_effect_step 0x10f457
    0x48 256 (by simp [RexWPrefix])))
  case sub => exact codeRange_slice_subset 0x10f42e bytes 41 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Effect.forgetFlags, orRaxImm32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf45d (by decide))
  advance_then (bswap_r64_effect_step 0x10f45d 0)
  case sub => exact codeRange_slice_subset 0x10f42e bytes 47 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf460 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10f460 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f42e bytes 50 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by decide)
    · x86_norm
      exact hP.codeApart 136 (by decide) 50 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by decide) 0 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf468 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10f468 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f42e bytes 58 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by decide)
    · x86_norm
      exact hP.codeApart 72 (by decide) 58 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by decide) 0 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf46d (by decide))
  advance_finish [effect, lengthWord, shift_nine, zero_stores]

theorem rsp_unchanged {s t : RamState} (h : (effect s).Holds s t) :
    rspOf t = rspOf s :=
  h.agrees.read (r := 4) (n := 64) (by simp [effect, Effect.components, Write.component, Operand.component])

theorem memory_footprint {s : RamState} {c : Component} {address : BitVec 64}
    (member : c ∈ (effect s).components) (covers : c.Covers address) :
    (Component.mem (rspOf s + 72) 8).Covers address ∨
      (Component.mem (rspOf s + 112) 32).Covers address := by
  have within (offset len : Nat) (low : 112 ≤ offset) (high : offset + len ≤ 144)
      (hc : (Component.mem (rspOf s + BitVec.ofNat 64 offset) len).Covers address) :
      (Component.mem (rspOf s + 112) 32).Covers address := by
    obtain ⟨j,hj,eq⟩ := hc
    refine ⟨offset - 112 + j, by omega, ?_⟩
    rw [eq]
    change rspOf s + BitVec.ofNat 64 offset + BitVec.ofNat 64 j =
      rspOf s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (offset - 112 + j)
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 112 + (offset - 112 + j) = offset + j by omega]
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component,
    Nat.reduceDiv] at member
  rcases member with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl
  all_goals first
  | exact covers.elim
  | exact Or.inl covers
  | exact Or.inr (within _ _ (by decide) (by decide) covers)

private def suffix : ByteArray :=
  ⟨#[128]⟩ ++ ⟨Array.replicate 23 0⟩ ++ Hkdf.Proofs.NIST.Encoding.natToOctets 8 768

private theorem suffix_size : suffix.size = 32 := by decide +kernel

private theorem suffix_byte (j : Fin 32) :
    suffix[j.val]'(by simpa only [suffix_size] using j.isLt) =
      if j.val = 0 then 128 else if j.val = 30 then 3 else 0 := by
  revert j
  decide +kernel

private theorem suffix_bytes {s t : RamState}
    (h : (effect s).Holds s t) (count : memLoad s.external (rspOf s + 216) 64 = 1)
    (readable : MemReadable t (rspOf s + 80) 64) :
    ∀ j : Fin 32, t.external[rspOf s + BitVec.ofNat 64 (112+j.val)]? =
      some (suffix[j.val]'(by simpa only [suffix_size] using j.isLt)) := by
  have word {n offset : Nat} {value : BitVec n} (low : 80 ≤ offset)
      (high : offset + n / 8 ≤ 144)
      (eq : memLoad t.external (rspOf s + BitVec.ofNat 64 offset) n = value)
      (i : Nat) (hi : i < n / 8) :
      t.external[rspOf s + BitVec.ofNat 64 (offset + i)]? = some (storedByte value i) := by
    have hbytes := Bytes.of_memLoad (n := n) (a := rspOf s + BitVec.ofNat 64 offset)
      (m := t.external) (fun k hk => by
        have addr : rspOf s + BitVec.ofNat 64 80 + BitVec.ofNat 64 (offset - 80 + k) =
            rspOf s + BitVec.ofNat 64 offset + BitVec.ofNat 64 k := by
          simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
          rw [show 80 + (offset - 80 + k) = offset + k by omega]
        rw [← addr]
        exact readable.mem _ (by omega))
    rw [eq] at hbytes
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hbytes i hi
  have lengthValue : lengthWord s = bswap64 (768 : BitVec 64) := by
    unfold lengthWord
    rw [count]
    rfl
  intro j
  have bound := j.isLt
  have words := h.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  rw [suffix_byte]
  by_cases marker : j.val = 0
  · simp only [marker, ite_true]
    exact word (n := 8) (offset := 112) (by decide) (by decide) words.2.1 0 (by decide)
  by_cases tail : 24 ≤ j.val
  · have length := word (n := 64) (offset := 136) (by decide) (by decide)
      (words.2.2.2.2.2.1.trans lengthValue) (j.val - 24) (by omega)
    have addr : 136 + (j.val - 24) = 112 + j.val := by omega
    rw [addr] at length
    have value (k : Fin 8) : storedByte (bswap64 (768 : BitVec 64)) k.val =
        if k.val = 6 then 3 else 0 := by
      revert k
      decide +kernel
    have hv := value ⟨j.val - 24, by omega⟩
    change storedByte (bswap64 (768 : BitVec 64)) (j.val - 24) =
      (if j.val - 24 = 6 then 3 else 0) at hv
    have same : (j.val - 24 = 6) ↔ (j.val = 30) := ⟨by omega, by omega⟩
    simpa only [hv, same, marker, ite_false] using length
  have zero (offset : Nat) (low : 80 ≤ offset) (high : offset + 8 ≤ 144)
      (left : offset ≤ 112 + j.val) (right : 112 + j.val < offset + 8)
      (written : memLoad t.external (rspOf s + BitVec.ofNat 64 offset) 64 = 0) :
      t.external[rspOf s + BitVec.ofNat 64 (112 + j.val)]? = some 0 := by
    have byte := word low high written (112 + j.val - offset) (by omega)
    rw [Nat.add_sub_of_le left] at byte
    have value : storedByte (0 : BitVec 64) (112 + j.val - offset) = 0 := by
      simp [storedByte]
    rwa [value] at byte
  simp only [marker, ite_false, show j.val ≠ 30 by omega]
  by_cases first : j.val < 9
  · exact zero 113 (by decide) (by decide) (by omega) (by omega) words.2.2.2.2.1
  by_cases second : j.val < 17
  · exact zero 121 (by decide) (by decide) (by omega) (by omega) words.2.2.2.1
  · exact zero 128 (by decide) (by decide) (by omega) (by omega) words.2.2.1

theorem payload {s t : RamState} {digest : ByteArray}
    (h : (effect s).Holds s t) (count : memLoad s.external (rspOf s + 216) 64 = 1)
    (source : (⟨(rspOf s + 80).toNat,32⟩ : MemoryRegion).HasBytes s.external digest)
    (readable : MemReadable t (rspOf s + 80) 64) :
    (⟨(rspOf s + 80).toNat,64⟩ : MemoryRegion).HasBytes t.external (padded digest) := by
  have size : digest.size = 32 := source.1
  have appended : padded digest = digest ++ suffix := by
    simp only [padded, suffix, ByteArray.append_assoc]
  rw [appended]
  refine ⟨by simp only [MemoryRegion.HasLength, ByteArray.size_append, size, suffix_size], ?_⟩
  intro i
  have bound : i.val < 64 := by
    simpa only [ByteArray.size_append, size, suffix_size, Nat.reduceAdd] using i.isLt
  change t.external[BitVec.ofNat 64 ((rspOf s + 80).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases front : i.val < 32
  · have saved := source.2 ⟨i.val, by omega⟩
    rw [ByteArray.getElem_append_left (by omega)]
    rw [h.agrees.byte (x := rspOf s + 80 + BitVec.ofNat 64 i.val)]
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using saved
    · intro c member covered
      rcases memory_footprint member covered with ⟨j,hj,eq⟩ | ⟨j,hj,eq⟩
      · exact RangeApart.offsets (rspOf s) (a := 80) (len := 32) (b := 72) (count := 8)
          (by decide) (by decide) (.inr (by decide)) i.val front j hj eq
      · exact RangeApart.offsets (rspOf s) (a := 80) (len := 32) (b := 112) (count := 32)
          (by decide) (by decide) (.inl (by decide)) i.val front j hj eq
  · rw [ByteArray.getElem_append_right (by omega)]
    have tail := suffix_bytes h count readable ⟨i.val - 32, by omega⟩
    change t.external[rspOf s + BitVec.ofNat 64 (112 + (i.val - 32))]? = _ at tail
    have address : 112 + (i.val - 32) = 80 + i.val := by omega
    rw [address, BitVec.ofNat_add, ← BitVec.add_assoc] at tail
    change t.external[rspOf s + 80#64 + BitVec.ofNat 64 i.val]? = _
    refine tail.trans (congrArg some ?_)
    simp only [size]

theorem execute [Bindings] {s : RamState} {boundary : ReturnBoundary} {digest : ByteArray}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : Pre s) (count : memLoad s.external (rspOf s + 216) 64 = 1)
    (source : (⟨(rspOf s + 80).toNat,32⟩ : MemoryRegion).HasBytes s.external digest)
    (readable : MemReadable s (rspOf s + 80) 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (effect s).Holds s t ∧
      (⟨(rspOf s + 80).toNat,64⟩ : MemoryRegion).HasBytes t.external (padded digest) ∧
      memLoad t.external (rspOf s + 72) 64 = memLoad t.external (rspOf s + 136) 64 := by
  obtain ⟨fuel,t,advance,ready',_,h⟩ := run boundary outside s ready (code loaded) pre
  have words := h.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  exact ⟨fuel,t,advance,ready',h,payload h count source (readable.of_holds h),
    words.2.2.2.2.2.2.trans words.2.2.2.2.2.1.symm⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.OuterPad
