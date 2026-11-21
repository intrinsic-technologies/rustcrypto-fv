import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Copy

open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x80, 0, 0, 0, 0x48, 0x89, 0x44, 0x24, 0x40,
   0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38,
   0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x30,
   0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28,
   0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20,
   0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x8b, 0x4c, 0x24, 0x58,
   0x48, 0x89, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10]

def IsStart (pc : BitVec 64) : Prop :=
  pc = 0x10f357 ∨ pc = 0x10f46d ∨ pc = 0x10f9a2

structure Pre (pc : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = pc
  readable : ∀ i : Nat, i < 7 → MemReadable s (rspOf s + BitVec.ofNat 64 (80 + 8*i)) 8
  writable : ∀ i : Nat, i < 7 → MemWritable s (rspOf s + BitVec.ofNat 64 (16 + 8*i)) 8
  codeApart : ∀ i : Nat, i < 7 →
    RangeApart (rspOf s + BitVec.ofNat 64 (16 + 8*i)) 8 pc bytes.length

def effect (pc : BitVec 64) (s : RamState) : Effect :=
  { rip := pc + 73
    writes :=
      [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 80) 64⟩,
       ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 88) 64⟩] ++
      ([6,5,4,3,2,1,0] : List Nat).map fun i =>
        ⟨(.mem (rspOf s + BitVec.ofNat 64 (16 + 8*i)) : Operand 64),
          memLoad s.external (rspOf s + BitVec.ofNat 64 (80 + 8*i)) 64⟩ }

theorem code {s : RamState} {pc : BitVec 64} (loaded : ProgramLoaded s) (site : IsStart pc) :
    CodeIn (codeRange pc bytes) s := by
  rcases site with rfl | rfl | rfl
  · exact programText_slice (programLoaded_codeIn loaded) 0xf357 bytes (by decide) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xf46d bytes (by decide) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xf9a2 bytes (by decide) (by decide +kernel)

private theorem continues_at {pc : BitVec 64} {boundary : ReturnBoundary}
    (site : IsStart pc) (outside : ¬ InProgram boundary.rip) (off : Nat) (bound : off ≤ 73) :
    pc + BitVec.ofNat 64 off ≠ boundary.rip := by
  apply boundary_ne_program outside
  rcases site with rfl | rfl | rfl
  · have h := inProgram_of_textOffset (0xf357 + off) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  · have h := inProgram_of_textOffset (0xf46d + off) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  · have h := inProgram_of_textOffset (0xf9a2 + off) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h

private def loadMode (i : Nat) : AddrMode :=
  .sib 4 none 0 (if i = 6 then .d32 128 else .d8 (BitVec.ofNat 8 (80 + 8*i)))

private def storeMode (i : Nat) : AddrMode :=
  .sib 4 none 0 (.d8 (BitVec.ofNat 8 (16 + 8*i)))

attribute [local x86_compose] loadMode storeMode

local macro "copy_load " pc:ident "," next:ident "," offset:term "," word:term "," dst:term : tactic =>
  `(tactic| (
    advance_then (mov_r64_m64_effect_step ($pc + BitVec.ofNat 64 $offset) 0x48
      (by simp [RexWPrefix]) $dst (loadMode $word) (by decide +kernel) rfl rfl)
    try (case sub => exact codeRange_slice_subset $pc bytes $offset 5)
    case mid =>
      intro s t pre holds obs
      refine ⟨LoadPre.of_holds holds (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm
        exact pre.readable $word (by decide)
      · apply Effect.Avoids.of_noMem
        x86_norm
        simp [Component.Covers]
      · x86_norm
        exact $next ($offset + 5) (by decide)))

local macro "copy_store " pc:ident "," next:ident "," offset:term "," word:term "," src:term : tactic =>
  `(tactic| (
    advance_then (mov_m64_r64_effect_step ($pc + BitVec.ofNat 64 $offset) 0x48
      (by simp [RexWPrefix]) $src (storeMode $word) (by decide +kernel) rfl rfl)
    try (case sub => exact codeRange_slice_subset $pc bytes $offset 5)
    case mid =>
      intro s t pre holds obs
      refine ⟨StorePre.of_holds holds (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact pre.writable $word (by decide)
      · x86_norm
        exact (pre.codeApart $word (by decide)).sub $offset 5 (by decide)
      · apply Effect.Local.avoids (by x86_local) (obs true)
        apply Effect.avoids_codeRange
        x86_norm
        exact pre.codeApart $word (by decide)
      · x86_norm
        exact $next ($offset + 5) (by decide)))

set_option maxHeartbeats 3200000 in
theorem run [Bindings] {pc : BitVec 64} (boundary : ReturnBoundary)
    (site : IsStart pc) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre pc) (codeRange pc bytes) (Effect.post (effect pc)) := by
  have next := continues_at site outside
  advance_begin (mov_r64_m64_effect_step pc 0x48
    (by simp [RexWPrefix]) 0 (loadMode 6) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 6 (by decide)⟩
  case next => exact fun _ _ ↦ next 8 (by decide)
  copy_store pc, next, 8, 6, 0
  copy_load pc, next, 13, 5, 0
  copy_store pc, next, 18, 5, 0
  copy_load pc, next, 23, 4, 0
  copy_store pc, next, 28, 4, 0
  copy_load pc, next, 33, 3, 0
  copy_store pc, next, 38, 3, 0
  copy_load pc, next, 43, 2, 0
  copy_store pc, next, 48, 2, 0
  copy_load pc, next, 53, 0, 0
  copy_load pc, next, 58, 1, 1
  copy_store pc, next, 63, 1, 1
  copy_store pc, next, 68, 0, 0
  advance_finish [effect, List.map_cons, List.map_nil]

theorem word {pc : BitVec 64} {s t : RamState} (h : (effect pc s).Holds s t)
    {i : Nat} (hi : i < 7) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 (16 + 8*i)) 64 =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (80 + 8*i)) 64 := by
  have member : i ∈ ([6,5,4,3,2,1,0] : List Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact Write.allHold_iff.mp h.writes
    ⟨(.mem (rspOf s + BitVec.ofNat 64 (16 + 8*i)) : Operand 64),
      memLoad s.external (rspOf s + BitVec.ofNat 64 (80 + 8*i)) 64⟩
    (List.mem_append_right _ (List.mem_map_of_mem member))

theorem memory_footprint {pc a : BitVec 64} {s : RamState} {c : Component}
    (member : c ∈ (effect pc s).components) (covered : c.Covers a) :
    (Component.mem (rspOf s + 16) 56).Covers a := by
  simp only [Effect.components, effect, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with member | rfl
  · obtain ⟨w, hm, rfl⟩ := List.mem_map.mp member
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> exact covered.elim
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

end Hkdf.Proofs.NewExpand.Expand.Finalize.Copy
