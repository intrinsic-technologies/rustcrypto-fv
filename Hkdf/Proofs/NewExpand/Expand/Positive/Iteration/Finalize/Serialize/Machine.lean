import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Compose
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Legacy

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open Hkdf.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

def start (outer : Bool) : BitVec 64 := if outer then 0x10f4cb else 0x10f3bd

def finish (outer : Bool) : BitVec 64 := start outer + 113

def source (outer : Bool) : Nat := if outer then 184 else 144

def destination (outer : Bool) : Nat := if outer then 16 else 80

structure Pre (outer : Bool) (s : RamState) : Prop where
  rip : s.RIP = start outer
  readable : ∀ i < 8, MemReadable s (rspOf s + BitVec.ofNat 64 (source outer + 4 * i)) 4
  writable : ∀ i < 8,
    CrossPageStore.Writable s (rspOf s + BitVec.ofNat 64 (destination outer + 4 * i)) 4
  codeApart : ∀ i < 8,
    RangeApart (rspOf s + BitVec.ofNat 64 (destination outer + 4 * i)) 4 (start outer) 113

def bytes (outer : Bool) : List UInt8 :=
  [0x8b, 0x84, 0x24, (UInt8.ofNat (source outer + 0)), 0x0, 0x0, 0x0,
   0x8b, 0x8c, 0x24, (UInt8.ofNat (source outer + 4)), 0x0, 0x0, 0x0,
   0xf, 0xc8,
   0xf, 0xc9,
   0x8b, 0x94, 0x24, (UInt8.ofNat (source outer + 8)), 0x0, 0x0, 0x0,
   0xf, 0xca,
   0x8b, 0xb4, 0x24, (UInt8.ofNat (source outer + 12)), 0x0, 0x0, 0x0,
   0xf, 0xce,
   0x8b, 0xbc, 0x24, (UInt8.ofNat (source outer + 16)), 0x0, 0x0, 0x0,
   0xf, 0xcf,
   0x44, 0x8b, 0x84, 0x24, (UInt8.ofNat (source outer + 20)), 0x0, 0x0, 0x0,
   0x41, 0xf, 0xc8,
   0x44, 0x8b, 0x8c, 0x24, (UInt8.ofNat (source outer + 24)), 0x0, 0x0, 0x0,
   0x41, 0xf, 0xc9,
   0x44, 0x8b, 0x94, 0x24, (UInt8.ofNat (source outer + 28)), 0x0, 0x0, 0x0,
   0x41, 0xf, 0xca,
   0x89, 0x44, 0x24, (UInt8.ofNat (destination outer + 0)),
   0x89, 0x4c, 0x24, (UInt8.ofNat (destination outer + 4)),
   0x89, 0x54, 0x24, (UInt8.ofNat (destination outer + 8)),
   0x89, 0x74, 0x24, (UInt8.ofNat (destination outer + 12)),
   0x89, 0x7c, 0x24, (UInt8.ofNat (destination outer + 16)),
   0x44, 0x89, 0x44, 0x24, (UInt8.ofNat (destination outer + 20)),
   0x44, 0x89, 0x4c, 0x24, (UInt8.ofNat (destination outer + 24)),
   0x44, 0x89, 0x54, 0x24, (UInt8.ofNat (destination outer + 28))]

theorem code {s : RamState} (loaded : ProgramLoaded s) (outer : Bool) :
    CodeIn (codeRange (start outer) (bytes outer)) s := by
  cases outer
  · exact Hkdf.Proofs.Common.Machine.programText_slice
      (Hkdf.Proofs.Common.Machine.programLoaded_codeIn loaded) 0xf3bd (bytes false)
      (by decide +kernel) (by decide +kernel)
  · exact Hkdf.Proofs.Common.Machine.programText_slice
      (Hkdf.Proofs.Common.Machine.programLoaded_codeIn loaded) 0xf4cb (bytes true)
      (by decide +kernel) (by decide +kernel)

private abbrev sourceMode (outer : Bool) (i : Nat) : AddrMode :=
  .sib 4 none 0 (.d32 (BitVec.ofNat 32 (source outer + 4 * i)))

private abbrev destinationMode (outer : Bool) (i : Nat) : AddrMode :=
  .sib 4 none 0 (.d8 (BitVec.ofNat 8 (destination outer + 4 * i)))

private theorem source_disp (outer : Bool) (i : Nat) (hi : i < 8) :
    (BitVec.ofNat 32 (source outer + 4 * i)).signExtend 64 =
      BitVec.ofNat 64 (source outer + 4 * i) := by
  have eq : ∀ (phase : Bool) (word : Fin 8),
      (BitVec.ofNat 32 (source phase + 4 * word.val)).signExtend 64 =
        BitVec.ofNat 64 (source phase + 4 * word.val) := by decide +kernel
  exact eq outer ⟨i, hi⟩

private theorem destination_disp (outer : Bool) (i : Nat) (hi : i < 8) :
    (BitVec.ofNat 8 (destination outer + 4 * i)).signExtend 64 =
      BitVec.ofNat 64 (destination outer + 4 * i) := by
  have eq : ∀ (phase : Bool) (word : Fin 8),
      (BitVec.ofNat 8 (destination phase + 4 * word.val)).signExtend 64 =
        BitVec.ofNat 64 (destination phase + 4 * word.val) := by decide +kernel
  exact eq outer ⟨i, hi⟩

private def swapped (outer : Bool) (s : RamState) (i : Nat) : BitVec 32 :=
  bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (source outer + 4 * i)) : Operand 32).read s)

private def registerWrite (outer : Bool) (s : RamState) (i : Nat) (reg : BitVec 5) : Write :=
  ⟨(.reg reg : Operand 64), (swapped outer s i).setWidth 64⟩

private def stackWrite (outer : Bool) (s : RamState) (i : Nat) : Write :=
  ⟨(.mem (rspOf s + BitVec.ofNat 64 (destination outer + 4 * i)) : Operand 32), swapped outer s i⟩

def effect (outer : Bool) (s : RamState) : Effect :=
  { rip := finish outer
    writes := [
      registerWrite outer s 0 0,
      registerWrite outer s 1 1,
      registerWrite outer s 2 2,
      registerWrite outer s 3 6,
      registerWrite outer s 4 7,
      registerWrite outer s 5 8,
      registerWrite outer s 6 9,
      registerWrite outer s 7 10,
      stackWrite outer s 0,
      stackWrite outer s 1,
      stackWrite outer s 2,
      stackWrite outer s 3,
      stackWrite outer s 4,
      stackWrite outer s 5,
      stackWrite outer s 6,
      stackWrite outer s 7] }

private theorem dest_sub (outer : Bool) (i j : Nat) :
    BitVec.ofNat 64 (destination outer + i) - BitVec.ofNat 64 (destination outer + j) =
      BitVec.ofNat 64 i - BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add]
  bv_omega

private theorem dest_eq (outer : Bool) (i j : Nat) :
    BitVec.ofNat 64 (destination outer + i) = BitVec.ofNat 64 (destination outer + j) ↔
      BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_right_inj]

private theorem bytes_length (outer : Bool) : (bytes outer).length = 113 := by
  cases outer <;> rfl

attribute [local x86_compose] Hkdf.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber BitVec.add_assoc dest_sub dest_eq bytes_length sourceMode destinationMode

private theorem code_subset (outer : Bool) (offset len : Nat) (insn : List UInt8)
    (eq : (List.drop offset (bytes outer)).take len = insn) :
    ∀ entry ∈ codeRange (start outer + BitVec.ofNat 64 offset) insn,
      entry ∈ codeRange (start outer) (bytes outer) := by
  rw [← eq]
  exact codeRange_slice_subset (start outer) (bytes outer) offset len

local macro "serialize_code " phase:ident "," off:term "," len:term : tactic =>
  `(tactic| exact code_subset $phase $off $len _ (by cases ($phase : Bool) <;> decide +kernel))

local macro "serialize_load " phase:ident "," i:term "," off:term "," len:term
    "," next:term "," outside:ident "," step:term : tactic =>
  `(tactic| (
    advance_then $step
    case sub => serialize_code $phase, $off, $len
    case mid =>
      intro s t pre holds obs
      refine ⟨LoadPre.of_holds holds (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [(source_disp $phase $i (by decide))]
        exact pre.readable $i (by decide)
      · apply Effect.Avoids.of_noMem
        simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
      · x86_norm
        exact $outside $next (by decide)))

local macro "serialize_swap " phase:ident "," off:term "," len:term
    "," next:term "," outside:ident "," step:term : tactic =>
  `(tactic| (
    advance_then $step
    case sub => serialize_code $phase, $off, $len
    case mid =>
      intro s t pre holds obs
      refine ⟨holds.rip_of (by x86_norm), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
      · x86_norm
        exact $outside $next (by decide)))

local macro "serialize_store " phase:ident "," i:term "," off:term "," len:term
    "," next:term "," outside:ident "," step:term : tactic =>
  `(tactic| (
    advance_then $step
    case sub => serialize_code $phase, $off, $len
    case mid =>
      intro s t pre holds obs
      have apart := pre.codeApart $i (by decide)
      refine ⟨CrossPageStore.storePre_of_holds holds (obs true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm [(destination_disp $phase $i (by decide))]
        exact pre.writable $i (by decide)
      · x86_norm [(destination_disp $phase $i (by decide))]
        exact apart.sub $off $len (by decide)
      · apply Effect.Local.avoids (by x86_local) (obs true)
        apply Effect.avoids_codeRange
        x86_norm [(destination_disp $phase $i (by decide))]
        exact apart
      · x86_norm
        exact $outside $next (by decide)))

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (outer : Bool) (boundary : ReturnBoundary)
    (outside : ∀ offset ≤ 113, start outer + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (Pre outer) (codeRange (start outer) (bytes outer))
      (Effect.post (effect outer)) := by
  advance_begin (mov_r32_m32_legacy_effect_step (start outer) 0 (sourceMode outer 0) (by simp [AddrMode.Valid]) rfl rfl)
  case sub => simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    code_subset outer 0 7 _ (by cases outer <;> decide +kernel)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm [(source_disp outer 0 (by decide))]
    exact h.readable 0 (by decide)
  case next =>
    intro s h
    exact outside 7 (by decide)
  serialize_load outer, 1, 7, 7, 14, outside,
    (mov_r32_m32_legacy_effect_step (start outer + 7) 1 (sourceMode outer 1) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 14, 2, 16, outside,
    (bswap_r32_effect_step (start outer + 14) 0)
  serialize_swap outer, 16, 2, 18, outside,
    (bswap_r32_effect_step (start outer + 16) 1)
  serialize_load outer, 2, 18, 7, 25, outside,
    (mov_r32_m32_legacy_effect_step (start outer + 18) 2 (sourceMode outer 2) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 25, 2, 27, outside,
    (bswap_r32_effect_step (start outer + 25) 2)
  serialize_load outer, 3, 27, 7, 34, outside,
    (mov_r32_m32_legacy_effect_step (start outer + 27) 6 (sourceMode outer 3) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 34, 2, 36, outside,
    (bswap_r32_effect_step (start outer + 34) 6)
  serialize_load outer, 4, 36, 7, 43, outside,
    (mov_r32_m32_legacy_effect_step (start outer + 36) 7 (sourceMode outer 4) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 43, 2, 45, outside,
    (bswap_r32_effect_step (start outer + 43) 7)
  serialize_load outer, 5, 45, 8, 53, outside,
    (mov_r32_m32_effect_step (start outer + 45) 0x44 (by simp [RexNoWPrefix]) 0 (sourceMode outer 5) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 53, 3, 56, outside,
    (bswap_r32_effect_step (start outer + 53) 8)
  serialize_load outer, 6, 56, 8, 64, outside,
    (mov_r32_m32_effect_step (start outer + 56) 0x44 (by simp [RexNoWPrefix]) 1 (sourceMode outer 6) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 64, 3, 67, outside,
    (bswap_r32_effect_step (start outer + 64) 9)
  serialize_load outer, 7, 67, 8, 75, outside,
    (mov_r32_m32_effect_step (start outer + 67) 0x44 (by simp [RexNoWPrefix]) 2 (sourceMode outer 7) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_swap outer, 75, 3, 78, outside,
    (bswap_r32_effect_step (start outer + 75) 10)
  serialize_store outer, 0, 78, 4, 82, outside,
    (CrossPageStore.mov_m32_r32_legacy_effect_step_any (start outer + 78) 0 (destinationMode outer 0) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 1, 82, 4, 86, outside,
    (CrossPageStore.mov_m32_r32_legacy_effect_step_any (start outer + 82) 1 (destinationMode outer 1) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 2, 86, 4, 90, outside,
    (CrossPageStore.mov_m32_r32_legacy_effect_step_any (start outer + 86) 2 (destinationMode outer 2) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 3, 90, 4, 94, outside,
    (CrossPageStore.mov_m32_r32_legacy_effect_step_any (start outer + 90) 6 (destinationMode outer 3) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 4, 94, 4, 98, outside,
    (CrossPageStore.mov_m32_r32_legacy_effect_step_any (start outer + 94) 7 (destinationMode outer 4) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 5, 98, 5, 103, outside,
    (CrossPageStore.mov_m32_r32_effect_step_any (start outer + 98) 0x44 (by simp [RexNoWPrefix]) 0 (destinationMode outer 5) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 6, 103, 5, 108, outside,
    (CrossPageStore.mov_m32_r32_effect_step_any (start outer + 103) 0x44 (by simp [RexNoWPrefix]) 1 (destinationMode outer 6) (by simp [AddrMode.Valid]) rfl rfl)
  serialize_store outer, 7, 108, 5, 113, outside,
    (CrossPageStore.mov_m32_r32_effect_step_any (start outer + 108) 0x44 (by simp [RexNoWPrefix]) 2 (destinationMode outer 7) (by simp [AddrMode.Valid]) rfl rfl)
  advance_finish [effect, finish, registerWrite, stackWrite, swapped,
    (source_disp outer 0 (by decide)), (source_disp outer 1 (by decide)),
    (source_disp outer 2 (by decide)), (source_disp outer 3 (by decide)),
    (source_disp outer 4 (by decide)), (source_disp outer 5 (by decide)),
    (source_disp outer 6 (by decide)), (source_disp outer 7 (by decide)),
    (destination_disp outer 0 (by decide)), (destination_disp outer 1 (by decide)),
    (destination_disp outer 2 (by decide)), (destination_disp outer 3 (by decide)),
    (destination_disp outer 4 (by decide)), (destination_disp outer 5 (by decide)),
    (destination_disp outer 6 (by decide)), (destination_disp outer 7 (by decide))]

theorem word {outer : Bool} {s t : RamState} (h : (effect outer s).Holds s t)
    (i : Nat) (hi : i < 8) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 (destination outer + 4 * i)) 32 =
      bswap32 (memLoad s.external (rspOf s + BitVec.ofNat 64 (source outer + 4 * i)) 32) := by
  apply Write.allHold_iff.mp h.writes (stackWrite outer s i)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [effect, List.mem_cons, true_or, or_true]

theorem rsp_unchanged {outer : Bool} {s t : RamState} (h : (effect outer s).Holds s t) :
    rspOf t = rspOf s := by
  exact h.agrees.read (by simp [effect, registerWrite, stackWrite, Effect.components])

theorem footprint (outer : Bool) (s : RamState) :
    ∀ c ∈ (effect outer s).components, ∀ a, c.Covers a →
      (Component.mem (rspOf s + BitVec.ofNat 64 (destination outer)) 32).Covers a := by
  have cover (i : Nat) (hi : i < 8) {a : BitVec 64}
      (h : (Component.mem (rspOf s + BitVec.ofNat 64 (destination outer + 4 * i)) 4).Covers a) :
      (Component.mem (rspOf s + BitVec.ofNat 64 (destination outer)) 32).Covers a := by
    obtain ⟨j, hj, rfl⟩ := h
    refine ⟨4 * i + j, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  intro c member a covered
  simp only [effect, registerWrite, stackWrite, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact covered.elim | exact cover _ (by decide) covered

theorem agreement {outer : Bool} {s t : RamState} (h : (effect outer s).Holds s t) :
    AgreesExcept
      [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .rip,
        .mem (rspOf s + BitVec.ofNat 64 (destination outer)) 32] s t := by
  apply h.agrees.widen
  · intro c member reg
    simp only [effect, registerWrite, stackWrite, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact Bool.noConfusion (show true = false from reg) | simp
  · intro a c member covered
    exact ⟨_, by simp, footprint outer s c member a covered⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.Serialize
