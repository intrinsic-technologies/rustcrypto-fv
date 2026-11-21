import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.Instructions.RepMovsq.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Return

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

def copySetupBytes : List UInt8 :=
  [0x48,0x89,0xdf,0x48,0x83,0xc7,0x60,0x48,0x8d,0xb4,0x24,0x20,1,0,0,
    0xb9,0x0a,0,0,0]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x10e287
    writes := [⟨(.reg 7 : Operand 64), s.regValue .rbx + 96⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 288⟩,
      ⟨(.reg 1 : Operand 64), 10⟩]
    flags := some (.ofStatusFlags (addSpec (s.regValue .rbx) 96).2) }

theorem copySetup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10e273 copySetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xe273 copySetupBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem copySetup_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10e273)
      (codeRange 0x10e273 copySetupBytes) (Effect.post copySetupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10e273 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xe276 (by decide))
  advance_then (show StepEffect _ _ (addR64Imm8Effect 0x10e276 7 96) from
    add_r64_imm8_effect_step 0x10e276 0x48 0xc7 96 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e273 copySetupBytes 3 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xe27a (by decide))⟩
  advance_then (lea_r64_effect_step 0x10e27a 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e273 copySetupBytes 7 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xe282 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10e282 0xb9 (by decide) 10)
  case sub => exact codeRange_slice_subset 0x10e273 copySetupBytes 15 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xe287 (by decide))⟩
  advance_finish [copySetupEffect]

set_option maxHeartbeats 1200000 in
theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e273) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e28a ∧
      (∀ i < 96, t.external[initial.regValue .rdi + BitVec.ofNat 64 i]? =
        s.external[initial.regValue .rdi + BitVec.ofNat 64 i]?) ∧
      (∀ i < 80, t.external[initial.regValue .rdi + BitVec.ofNat 64 (96 + i)]? =
        s.external[stackPtr initial - 120 + BitVec.ofNat 64 i]?) := by
  have outLow : (initial.regValue .rdi).toNat + 176 < 2^32 := pre.outputBounded
  have stackBounds := Hkdf.Proofs.Common.Encoding.Serialize.stack_bounds pre
  have outStack : (registerRegion initial .rdi 176).Disjoint (Stack.region initial 1264) :=
    pre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  have outContains (i : Nat) (hi : i < 176) :
      (registerRegion initial .rdi 176).Contains
        (initial.regValue .rdi + BitVec.ofNat 64 i).toNat :=
    memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  obtain ⟨fuel, u, runU, readyU, _, effectU⟩ :=
    copySetup_run boundary pre.outerBoundary s
      (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.running.machine)
      (copySetup_code state.running.loaded) rip
  have componentsU : (copySetupEffect s).components =
      [.reg 7, .reg 6, .reg 1, .flags, .rip] := rfl
  have externalU : u.external = s.external := by
    apply effectU.agrees.external
    rw [componentsU]
    simp [Component.Covers]
  have stateU : Suffix.State initial boundary u := by
    apply state.of_agrees pre runU readyU effectU.agrees
    · intro c hc a cover
      rw [componentsU] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact cover.elim
    · intro c hc
      rw [componentsU]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro i hi
      rw [externalU]
  have stores := effectU.writes
  change rdi.read u = s.regValue .rbx + 96 ∧
    rsi.read u = rspOf s + 288 ∧ rcx.read u = 10 at stores
  have outputU : rdi.read u = initial.regValue .rdi + 96 := by
    rw [stores.1, state.rbx]
  have inputU : rsi.read u = stackPtr initial - 120 := by
    rw [stores.2.1]
    change stackPtr s + 288 = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have countU : (rcx.read u).toNat = 10 := by rw [stores.2.2]; rfl
  have outputNat : (initial.regValue .rdi + 96).toNat =
      (initial.regValue .rdi).toNat + 96 := toNat_add_ofNat (initial.regValue .rdi) 96 (by omega)
  have inputNat : (stackPtr initial - 120).toNat = (stackPtr initial).toNat - 120 :=
    Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_toNat pre (by decide)
  have outputRead : MemReadable u (initial.regValue .rdi) 176 := by
    apply Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
      (Hkdf.Proofs.Common.Machine.memoryRegion_memReadable pre.outputBounded
        pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)) stateU.running.allocated
  have writable : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable u
      (initial.regValue .rdi) 176 := by
    refine ⟨outputRead, tables_of_not_reserved (by decide) outputRead.low ?_⟩
    intro i hi reserved
    exact pre.avoids _ (by simp) _ (outContains i hi) (.inr reserved)
  have src : MemReadable u (rsi.read u) 80 := by
    rw [inputU]
    exact Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
      (Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre (by decide) (by decide))
      stateU.running.allocated
  have dst : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable u (rdi.read u) 80 := by
    rw [outputU]
    exact writable.add 96 (by decide)
  have disjoint : (rsi.read u).toNat + 80 ≤ (rdi.read u).toNat ∨
      (rdi.read u).toNat + 80 ≤ (rsi.read u).toNat := by
    rw [inputU, outputU, inputNat, outputNat]
    by_cases before : (stackPtr initial).toNat - 120 + 80 ≤
        (initial.regValue .rdi).toNat + 96
    · exact .inl before
    right
    apply Nat.le_of_not_lt
    intro after
    apply outStack (max ((initial.regValue .rdi).toNat + 96)
      ((stackPtr initial).toNat - 120))
    · change (initial.regValue .rdi).toNat ≤ _ ∧
        _ < (initial.regValue .rdi).toNat + 176
      constructor <;> omega
    · change (stackPtr initial).toNat - 1264 ≤ _ ∧
        _ < (Stack.region initial 1264).start + (Stack.region initial 1264).size
      rw [Hkdf.Proofs.Common.Machine.stack_region_end]
      constructor <;> omega
  have codeApart : RangeApart (rdi.read u) 80 0x10e287 3 := by
    intro i hi j hj eq
    apply pre.avoids (registerRegion initial .rdi 176) (by simp)
      (rdi.read u + BitVec.ofNat 64 i) ?_ (.inl ?_)
    · rw [outputU]
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        outContains (96 + i) (by omega)
    · rw [eq]
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
        inProgram_of_textOffset (0xe287 + j) (by omega)
  have repPre := Hkdf.Proofs.Common.Instructions.RepMovsq.pre_of_memory
    effectU.rip stateU.running.directionFlag.df countU src dst disjoint codeApart
  have rep := Hkdf.Proofs.Common.Instructions.RepMovsq.rep_movsq_execution pre.stride readyU
    (programText_slice (programLoaded_codeIn stateU.running.loaded) 0xe287
      [0xf3,0x48,0xa5] (by decide) (by decide +kernel)) repPre countU
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe287 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe28a (by decide)))
  let t := nextStates 10 u
  change Advances boundary 10 u t ∧ ReadyToStep t ∧
    (repMovsqEffect 0x10e287 u).Holds u t ∧
    (∀ i < 80, t.external[rdi.read u + BitVec.ofNat 64 i]? =
      u.external[rsi.read u + BitVec.ofNat 64 i]?) at rep
  obtain ⟨runT, readyT, effectT, copyBytes⟩ := rep
  have footprint : WritesWithin (repMovsqEffect 0x10e287 u).components
      #v[registerRegion initial .rdi 176] := by
    intro c hc a cover
    rw [repMovsqEffect_components, countU] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i, hi, rfl⟩ := cover
    refine ⟨registerRegion initial .rdi 176, by simp, ?_⟩
    rw [outputU]
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        outContains (96 + i) (by omega)
  have savedT : (Component.mem (stackPtr initial - 40) 48).Agrees u t := by
    apply frame_agrees_of_disjoint (effectT.agrees.memoryWriteFrame footprint)
    · rw [show (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 from
        Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_toNat pre (by decide)]
      omega
    · intro region member a saved output
      have eq : region = registerRegion initial .rdi 176 := by simpa using member
      subst region
      apply outStack a output
      change (Stack.region initial 1264).start ≤ a ∧
        a < (Stack.region initial 1264).start + (Stack.region initial 1264).size
      rw [Hkdf.Proofs.Common.Machine.stack_region_end]
      change (stackPtr initial).toNat - 1264 ≤ a ∧ a < (stackPtr initial).toNat + 8
      change (stackPtr initial - 40).toNat ≤ a ∧
        a < (stackPtr initial - 40).toNat + 48 at saved
      rw [show (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 from
        Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_toNat pre (by decide)] at saved
      constructor <;> omega
  refine ⟨t, stateU.of_agrees pre runT readyT effectT.agrees ?_ ?_ savedT,
    effectT.rip, ?_⟩
  · intro c hc a cover
    obtain ⟨region, member, contained⟩ := footprint c hc a cover
    have eq : region = registerRegion initial .rdi 176 := by simpa using member
    subst region
    exact ⟨registerRegion initial .rdi 176, by simp, contained⟩
  · intro c hc
    rw [repMovsqEffect_components]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · constructor
    · intro i hi
      rw [← externalU]
      apply effectT.agrees.byte
      intro c hc cover
      rw [repMovsqEffect_components, countU] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover
      obtain ⟨j, hj, eq⟩ := cover
      rw [outputU] at eq
      exact (RangeApart.offsets (initial.regValue .rdi) (a := 0) (len := 96)
        (b := 96) (count := 80) (by decide) (by decide) (.inl (by decide)))
        i hi j hj (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using eq)
    · intro i hi
      have h := copyBytes i hi
      rw [outputU, inputU, externalU] at h
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h

end Hkdf.Proofs.Standard.Finalize.Suffix.Return
