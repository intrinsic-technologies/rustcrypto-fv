import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Extra

open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def copyLengthBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x88, 0, 0, 0, 0x48, 0x89, 0x44, 0x24, 0x48]

structure CopyLengthPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f995
  readable : MemReadable s (rspOf s + 136) 8
  writable : MemWritable s (rspOf s + 72) 8
  codeApart : RangeApart (rspOf s + 72) 8 0x10f995 13

def copyLengthEffect (s : RamState) : Effect :=
  let value := memLoad s.external (rspOf s + 136) 64
  { rip := 0x10f9a2
    writes := [⟨(.reg 0 : Operand 64), value⟩, ⟨(.mem (rspOf s + 72) : Operand 64), value⟩] }

theorem copyLength [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : CopyLengthPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (copyLengthEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf995 copyLengthBytes
    (by decide) (by decide +kernel)
  suffices block : AdvanceTriple boundary CopyLengthPre (codeRange 0x10f995 copyLengthBytes)
      (Effect.post copyLengthEffect) by
    obtain ⟨fuel, t, run, ready', _, effect⟩ := block s ready code pre
    exact ⟨fuel, t, run, ready', effect⟩
  advance_begin (mov_r64_m64_effect_step 0x10f995 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case pre => exact fun _ h => ⟨h.rip, h.readable⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf99d (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f99d 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f995 copyLengthBytes 8 5
  case mid =>
    intro s t h holds obs
    refine ⟨StorePre.of_holds holds (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact h.writable
    · x86_norm
      exact h.codeApart.sub 8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact h.codeApart
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf9a2 (by decide))
  advance_finish [copyLengthEffect]

private def zeroMode (i : Nat) : AddrMode :=
  .sib 4 none 0 (if i = 6 then .d32 128 else .d8 (BitVec.ofNat 8 (80 + 8*i)))

private def zeroBytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x50, 0, 0, 0, 0, 0x48, 0xc7, 0x44, 0x24, 0x58, 0, 0, 0, 0,
   0x48, 0xc7, 0x44, 0x24, 0x60, 0, 0, 0, 0, 0x48, 0xc7, 0x44, 0x24, 0x68, 0, 0, 0, 0,
   0x48, 0xc7, 0x44, 0x24, 0x70, 0, 0, 0, 0, 0x48, 0xc7, 0x44, 0x24, 0x78, 0, 0, 0, 0,
   0x48, 0xc7, 0x84, 0x24, 0x80, 0, 0, 0, 0, 0, 0, 0, 0xe9, 0xd7, 0xf8, 0xff, 0xff]

structure ZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fa02
  writable : ∀ i : Nat, i < 7 → MemWritable s (rspOf s + BitVec.ofNat 64 (80 + 8*i)) 8
  codeApart : ∀ i : Nat, i < 7 → RangeApart (rspOf s + BitVec.ofNat 64 (80 + 8*i)) 8 0x10fa02 71

def zeroEffect (s : RamState) : Effect :=
  { rip := 0x10f320
    writes := ([0,1,2,3,4,5,6] : List Nat).map fun i =>
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (80+8*i)) : Operand 64), 0⟩ }

attribute [local x86_compose] zeroMode

local macro "extra_zero_store " outside:ident ", " pc:term ", " offset:term ", " size:term ", "
    word:term ", " next:term : tactic =>
  `(tactic| (
    advance_then (mov_m64_imm32_effect_step $pc 0x48 (by simp [RexWPrefix])
      (zeroMode $word) (by decide) rfl rfl 0)
    case sub => exact codeRange_slice_subset 0x10fa02 zeroBytes $offset $size
    case mid =>
      intro s t pre holds obs
      refine ⟨StorePre.of_holds holds (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact pre.writable $word (by decide)
      · x86_norm
        exact (pre.codeApart $word (by decide)).sub $offset $size (by decide)
      · apply Effect.Local.avoids (by x86_local) (obs true)
        apply Effect.avoids_codeRange
        x86_norm
        exact pre.codeApart $word (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset $next (by decide))))

private theorem zero_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPre (codeRange 0x10fa02 zeroBytes) (Effect.post zeroEffect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10fa02 0x48 (by simp [RexWPrefix])
    (zeroMode 0) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 0 (by decide), (h.codeApart 0 (by decide)).sub0 9 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 0 (by decide)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xfa0b (by decide))
  extra_zero_store outside, 0x10fa0b, 9, 9, 1, 0xfa14
  extra_zero_store outside, 0x10fa14, 18, 9, 2, 0xfa1d
  extra_zero_store outside, 0x10fa1d, 27, 9, 3, 0xfa26
  extra_zero_store outside, 0x10fa26, 36, 9, 4, 0xfa2f
  extra_zero_store outside, 0x10fa2f, 45, 9, 5, 0xfa38
  extra_zero_store outside, 0x10fa38, 54, 12, 6, 0xfa44
  advance_then (jmp_rel32_effect_step 0x10fa44 0xfffff8d7 (by decide))
  case sub => exact codeRange_slice_subset 0x10fa02 zeroBytes 66 5
  case mid =>
    intro s t pre holds obs
    exact ⟨holds.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf320 (by decide))⟩
  advance_finish [zeroEffect, List.map_cons, List.map_nil]

private theorem zero_word {s t : RamState} (h : (zeroEffect s).Holds s t) {i : Nat} (hi : i < 7) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 (80+8*i)) 64 = 0 := by
  have member : i ∈ ([0,1,2,3,4,5,6] : List Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact Write.allHold_iff.mp h.writes
    ⟨(.mem (rspOf s + BitVec.ofNat 64 (80+8*i)) : Operand 64), 0⟩
    (List.mem_map_of_mem member)

theorem zero_bytes {s t : RamState} (pre : ZeroPre s) (h : (zeroEffect s).Holds s t) :
    (⟨(rspOf s + 80).toNat, 56⟩ : MemoryRegion).HasBytes t.external ⟨Array.replicate 56 0⟩ := by
  refine ⟨rfl, fun i => ?_⟩
  have hi : i.val < 56 := i.isLt
  have wordBound : i.val / 8 < 7 := by omega
  have readable := (pre.writable _ wordBound).readable.of_holds h
  have bytes := Bytes.of_memLoad (n := 64) readable.mem
  rw [zero_word h wordBound] at bytes
  have byte := bytes (i.val % 8) (by omega)
  have offset : 8 * (i.val / 8) + i.val % 8 = i.val := by omega
  have address : rspOf s + BitVec.ofNat 64 (80+8*(i.val/8)) + BitVec.ofNat 64 (i.val%8) =
      rspOf s + 80 + BitVec.ofNat 64 i.val := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc, offset, BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  have zero : storedByte (0 : BitVec 64) (i.val % 8) = 0 := by simp [storedByte]
  change t.external[BitVec.ofNat 64 ((rspOf s + 80).toNat + i.val)]? =
    some ((⟨Array.replicate 56 0⟩ : ByteArray)[i.val]'i.isLt)
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ByteArray.getElem_eq_getElem_data, Array.getElem_replicate, ← address]
  simpa only [zero] using byte

theorem zero_memory_footprint {a : BitVec 64} {s : RamState} {c : Component}
    (member : c ∈ (zeroEffect s).components) (covered : c.Covers a) :
    (Component.mem (rspOf s + 80) 56).Covers a := by
  simp only [Effect.components, zeroEffect, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
    at member
  rcases member with member | rfl
  · obtain ⟨w, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have bound : i < 7 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    rw [Write.component_mem] at covered
    obtain ⟨j, hj, rfl⟩ := covered
    refine ⟨8*i + j, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · exact covered.elim

theorem zeroPrefix [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : ZeroPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (zeroEffect s).Holds s t ∧
      (⟨(rspOf s + 80).toNat, 56⟩ : MemoryRegion).HasBytes t.external ⟨Array.replicate 56 0⟩ := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xfa02 zeroBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, t, run, ready', _, effect⟩ := zero_run boundary outside s ready code pre
  exact ⟨fuel, t, run, ready', effect, zero_bytes pre effect⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.Extra
