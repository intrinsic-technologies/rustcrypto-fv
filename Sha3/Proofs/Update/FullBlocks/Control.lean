import Sha3.Proofs.Update.FullBlocks.Basic
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Add.Imm32.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Call.Triple

namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

def adjustLength : Variant → Nat
  | .sha224 | .sha256 => 7
  | .sha384 | .sha512 => 4

def counterPC (v : Variant) : BitVec 64 := loadPC v v.lanes

def pointerPC (v : Variant) : BitVec 64 := counterPC v + .ofNat 64 (adjustLength v)

def argumentPC (v : Variant) : BitVec 64 := pointerPC v + .ofNat 64 (adjustLength v)

def callPC (v : Variant) : BitVec 64 := argumentPC v + 3

def counterBytes : Variant → List UInt8
  | .sha224 => [0x48, 0x81, 0xc5, 0x70, 0xff, 0xff, 0xff]
  | .sha256 => [0x48, 0x81, 0xc5, 0x78, 0xff, 0xff, 0xff]
  | .sha384 => [0x48, 0x83, 0xc5, 0x98]
  | .sha512 => [0x48, 0x83, 0xc5, 0xb8]

def pointerBytes : Variant → List UInt8
  | .sha224 => [0x49, 0x81, 0xc6, 0x90, 0, 0, 0]
  | .sha256 => [0x49, 0x81, 0xc6, 0x88, 0, 0, 0]
  | .sha384 => [0x49, 0x83, 0xc6, 0x68]
  | .sha512 => [0x49, 0x83, 0xc6, 0x48]

def counterEffect (v : Variant) (s : RamState) : Effect :=
  { rip := pointerPC v
    writes := [⟨(Operand.reg 5 : Operand 64),
      (Operand.reg 5 : Operand 64).read s - .ofNat 64 (8 * v.lanes)⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 5 : Operand 64).read s)
      (-.ofNat 64 (8 * v.lanes))).2) }

def pointerEffect (v : Variant) (s : RamState) : Effect :=
  { rip := argumentPC v
    writes := [⟨(Operand.reg 14 : Operand 64),
      (Operand.reg 14 : Operand 64).read s + .ofNat 64 (8 * v.lanes)⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 14 : Operand 64).read s)
      (.ofNat 64 (8 * v.lanes))).2) }

theorem counter_effect [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = counterPC v) (codeRange (counterPC v) (counterBytes v))
      (counterEffect v) := by
  cases v
  case sha224 =>
    have h := add_r64_imm32_effect_step (counterPC .sha224) 0x48 0xc5 0xffffff70
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm32Effect (counterPC .sha224) 5 0xffffff70 = counterEffect .sha224 := by
      funext s
      simp only [addR64Imm32Effect, counterEffect, pointerPC, adjustLength,
        Variant.lanes, BitVec.sub_eq_add_neg]
      rfl
    change StepEffect _ _ (addR64Imm32Effect (counterPC .sha224) 5 0xffffff70) at h
    rw [he] at h
    exact h
  case sha256 =>
    have h := add_r64_imm32_effect_step (counterPC .sha256) 0x48 0xc5 0xffffff78
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm32Effect (counterPC .sha256) 5 0xffffff78 = counterEffect .sha256 := by
      funext s
      simp only [addR64Imm32Effect, counterEffect, pointerPC, adjustLength,
        Variant.lanes, BitVec.sub_eq_add_neg]
      rfl
    change StepEffect _ _ (addR64Imm32Effect (counterPC .sha256) 5 0xffffff78) at h
    rw [he] at h
    exact h
  case sha384 =>
    have h := add_r64_imm8_effect_step (counterPC .sha384) 0x48 0xc5 0x98
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm8Effect (counterPC .sha384) 5 0x98 = counterEffect .sha384 := by
      funext s
      simp only [addR64Imm8Effect, counterEffect, pointerPC, adjustLength,
        Variant.lanes, BitVec.sub_eq_add_neg]
      rfl
    change StepEffect _ _ (addR64Imm8Effect (counterPC .sha384) 5 0x98) at h
    rw [he] at h
    exact h
  case sha512 =>
    have h := add_r64_imm8_effect_step (counterPC .sha512) 0x48 0xc5 0xb8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm8Effect (counterPC .sha512) 5 0xb8 = counterEffect .sha512 := by
      funext s
      simp only [addR64Imm8Effect, counterEffect, pointerPC, adjustLength,
        Variant.lanes, BitVec.sub_eq_add_neg]
      rfl
    change StepEffect _ _ (addR64Imm8Effect (counterPC .sha512) 5 0xb8) at h
    rw [he] at h
    exact h

theorem pointer_effect [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = pointerPC v) (codeRange (pointerPC v) (pointerBytes v))
      (pointerEffect v) := by
  cases v
  case sha224 =>
    have h := add_r64_imm32_effect_step (pointerPC .sha224) 0x49 0xc6 0x90
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm32Effect (pointerPC .sha224) 14 0x90 = pointerEffect .sha224 := by
      funext s
      simp only [addR64Imm32Effect, pointerEffect, argumentPC, adjustLength,
        Variant.lanes]
      rfl
    change StepEffect _ _ (addR64Imm32Effect (pointerPC .sha224) 14 0x90) at h
    rw [he] at h
    exact h
  case sha256 =>
    have h := add_r64_imm32_effect_step (pointerPC .sha256) 0x49 0xc6 0x88
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm32Effect (pointerPC .sha256) 14 0x88 = pointerEffect .sha256 := by
      funext s
      simp only [addR64Imm32Effect, pointerEffect, argumentPC, adjustLength,
        Variant.lanes]
      rfl
    change StepEffect _ _ (addR64Imm32Effect (pointerPC .sha256) 14 0x88) at h
    rw [he] at h
    exact h
  case sha384 =>
    have h := add_r64_imm8_effect_step (pointerPC .sha384) 0x49 0xc6 0x68
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm8Effect (pointerPC .sha384) 14 0x68 = pointerEffect .sha384 := by
      funext s
      simp only [addR64Imm8Effect, pointerEffect, argumentPC, adjustLength,
        Variant.lanes]
      rfl
    change StepEffect _ _ (addR64Imm8Effect (pointerPC .sha384) 14 0x68) at h
    rw [he] at h
    exact h
  case sha512 =>
    have h := add_r64_imm8_effect_step (pointerPC .sha512) 0x49 0xc6 0x48
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : addR64Imm8Effect (pointerPC .sha512) 14 0x48 = pointerEffect .sha512 := by
      funext s
      simp only [addR64Imm8Effect, pointerEffect, argumentPC, adjustLength,
        Variant.lanes]
      rfl
    change StepEffect _ _ (addR64Imm8Effect (pointerPC .sha512) 14 0x48) at h
    rw [he] at h
    exact h


theorem argument_effect [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = argumentPC v) (codeRange (argumentPC v) [0x4c, 0x89, 0xff])
      (movR64R64Effect (argumentPC v) 7 15) := by
  exact mov_r64_r64_effect_step (argumentPC v) 0x4c 0xff
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem setup_image (v : Variant) :
    (∀ byte ∈ codeRange (counterPC v) (counterBytes v), byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (pointerPC v) (pointerBytes v), byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (argumentPC v) [0x4c, 0x89, 0xff], byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2) := by
  cases v <;> decide +kernel

theorem scalar_advance [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect} {cs : List Component}
    (step : StepEffect (fun s ↦ s.RIP = p) (codeRange p bytes) effect)
    (image : ∀ byte ∈ codeRange p bytes, byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2)
    (frame : ∀ s, ∀ c ∈ (effect s).components, c ∈ cs)
    (nomem : ∀ c ∈ cs, ∀ x, ¬c.Covers x)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (boundaryOutside : ¬ InProgram boundary.rip)
    (nextInProgram : ∀ s, InProgram (effect s).rip) (ip : s.RIP = p) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (effect s).Holds s t ∧ AgreesExcept cs s t := by
  have code : CodeIn (codeRange p bytes) s := by
    intro byte hb
    exact ⟨(image byte hb).1, programLoaded_fetchByte loaded (image byte hb).2⟩
  obtain ⟨t, ht, hr, he⟩ := step s ready code ip
  have ha := he.agrees.mono (frame s)
  have away : t.RIP ≠ boundary.rip := by
    intro h
    have hp : InProgram t.RIP := by
      rw [he.rip]
      exact nextInProgram s
    exact boundaryOutside (h ▸ hp)
  refine ⟨t, Advances.of_step ht (.inl away), hr, ?_, he, ha⟩
  unfold ProgramLoaded
  rw [ha.external nomem]
  exact loaded

def setupClobbers : List Component := [.reg 5, .reg 14, .reg 7, .flags, .rip]

theorem setup_nomem : ∀ c ∈ setupClobbers, ∀ x, ¬c.Covers x := by
  simp [setupClobbers, Component.Covers]

theorem setup_nosp : Component.reg 4 ∉ setupClobbers := by decide +kernel

theorem setup_inProgram (v : Variant) :
    InProgram (pointerPC v) ∧ InProgram (argumentPC v) ∧ InProgram (callPC v) := by
  constructor
  · refine ⟨0x49, ?_⟩
    apply imageSections_mem_toCodeMap_of_fetchByte
    cases v <;> decide +kernel
  · constructor
    · refine ⟨0x4c, ?_⟩
      apply imageSections_mem_toCodeMap_of_fetchByte
      cases v <;> decide +kernel
    · refine ⟨0xe8, ?_⟩
      apply imageSections_mem_toCodeMap_of_fetchByte
      cases v <;> decide +kernel

theorem setup_advance [Bindings] {boundary : ReturnBoundary} {v : Variant} {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (boundaryOutside : ¬ InProgram boundary.rip) (ip : s.RIP = counterPC v) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = callPC v ∧
      (Operand.reg 5 : Operand 64).read t =
        (Operand.reg 5 : Operand 64).read s - .ofNat 64 (8 * v.lanes) ∧
      (Operand.reg 14 : Operand 64).read t =
        (Operand.reg 14 : Operand 64).read s + .ofNat 64 (8 * v.lanes) ∧
      (Operand.reg 7 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s ∧
      AgreesExcept setupClobbers s t := by
  obtain ⟨u, hu, ru, lu, eu, fu⟩ := scalar_advance (cs := setupClobbers)
    (counter_effect v) (setup_image v).1
    (by intro s; simp [counterEffect, Effect.components, setupClobbers])
    setup_nomem ready loaded boundaryOutside (fun _ ↦ (setup_inProgram v).1) ip
  obtain ⟨w, hw, rw', lw, ew, fw⟩ := scalar_advance (cs := setupClobbers)
    (pointer_effect v) (setup_image v).2.1
    (by intro s; simp [pointerEffect, Effect.components, setupClobbers])
    setup_nomem ru lu boundaryOutside (fun _ ↦ (setup_inProgram v).2.1) eu.rip
  obtain ⟨t, ht, rt, lt, et, ft⟩ := scalar_advance (cs := setupClobbers)
    (argument_effect v) (setup_image v).2.2
    (by intro s; simp [movR64R64Effect_components, setupClobbers])
    setup_nomem rw' lw boundaryOutside (fun _ ↦ (setup_inProgram v).2.2) ew.rip
  refine ⟨t, hu.trans (hw.trans ht), rt, lt, et.rip, ?_, ?_, ?_, ?_⟩
  · rw [et.agrees.read (by simp [movR64R64Effect_components]),
      ew.agrees.read (by simp [pointerEffect, Effect.components])]
    exact eu.writes
  · rw [et.agrees.read (by simp [movR64R64Effect_components])]
    have hv : (Operand.reg 14 : Operand 64).read w =
        (Operand.reg 14 : Operand 64).read u + .ofNat 64 (8 * v.lanes) := ew.writes
    rw [hv, eu.agrees.read (by simp [counterEffect, Effect.components])]
  · change (Operand.reg 7 : Operand 64).read t = _
    rw [show (Operand.reg 7 : Operand 64).read t =
      (Operand.reg 15 : Operand 64).read w from et.writes,
      fw.read (by simp [setupClobbers]), fu.read (by simp [setupClobbers])]
  · apply (fu.trans (fw.trans ft)).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

def comparePC (v : Variant) : BitVec 64 := callPC v + 5

def backedgePC (v : Variant) : BitVec 64 := comparePC v + .ofNat 64 (adjustLength v)

def exitAddress : Variant → BitVec 64
  | .sha224 => 0x100a7d | .sha256 => 0x10075f
  | .sha384 => 0x10044c | .sha512 => 0x10017c

def compareBytes : Variant → List UInt8
  | .sha224 => [0x48, 0x81, 0xfd, 0x90, 0, 0, 0]
  | .sha256 => [0x48, 0x81, 0xfd, 0x88, 0, 0, 0]
  | .sha384 => [0x48, 0x83, 0xfd, 0x68]
  | .sha512 => [0x48, 0x83, 0xfd, 0x48]

def backedgeBytes : Variant → List UInt8
  | .sha224 => [0x0f, 0x83, 0x43, 0xff, 0xff, 0xff]
  | .sha256 => [0x0f, 0x83, 0x51, 0xff, 0xff, 0xff]
  | .sha384 => [0x73, 0x84]
  | .sha512 => [0x73, 0xa4]

def compareEffect (v : Variant) (s : RamState) : Effect :=
  { rip := backedgePC v
    flags := some (.ofStatusFlags
      (cmpSpec ((Operand.reg 5 : Operand 64).read s) (.ofNat 64 (8 * v.lanes)))) }

def backedgeEffect (v : Variant) (s : RamState) : Effect :=
  branchEffect (condHolds 3 (StatusFlags.ofRFLAGS s.RFLAGS)) (exitAddress v) (start v)

theorem compare_effect [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = comparePC v) (codeRange (comparePC v) (compareBytes v))
      (compareEffect v) := by
  cases v
  case sha224 =>
    have h := cmp_r64_imm32_effect_step (comparePC .sha224) 0x48 0xfd 0x90
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : cmpR64Imm32Effect (comparePC .sha224) 5 0x90 = compareEffect .sha224 := by
      funext s
      rfl
    change StepEffect _ _ (cmpR64Imm32Effect (comparePC .sha224) 5 0x90) at h
    rw [he] at h
    exact h
  case sha256 =>
    have h := cmp_r64_imm32_effect_step (comparePC .sha256) 0x48 0xfd 0x88
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : cmpR64Imm32Effect (comparePC .sha256) 5 0x88 = compareEffect .sha256 := by
      funext s
      rfl
    change StepEffect _ _ (cmpR64Imm32Effect (comparePC .sha256) 5 0x88) at h
    rw [he] at h
    exact h
  case sha384 =>
    have h := cmp_r64_imm8_effect_step (comparePC .sha384) 0x48 0xfd 0x68
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : cmpR64Imm8Effect (comparePC .sha384) 5 0x68 = compareEffect .sha384 := by
      funext s
      rfl
    change StepEffect _ _ (cmpR64Imm8Effect (comparePC .sha384) 5 0x68) at h
    rw [he] at h
    exact h
  case sha512 =>
    have h := cmp_r64_imm8_effect_step (comparePC .sha512) 0x48 0xfd 0x48
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
    have he : cmpR64Imm8Effect (comparePC .sha512) 5 0x48 = compareEffect .sha512 := by
      funext s
      rfl
    change StepEffect _ _ (cmpR64Imm8Effect (comparePC .sha512) 5 0x48) at h
    rw [he] at h
    exact h

theorem backedge_effect [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = backedgePC v)
      (codeRange (backedgePC v) (backedgeBytes v)) (backedgeEffect v) := by
  cases v
  case sha224 =>
    have h := jcc_rel32_effect_step (backedgePC .sha224) 3 0xffffff43
    have h' := h.mono_pre (pre' := fun s ↦ s.RIP = backedgePC .sha224)
      (fun s hip ↦ ⟨hip, fun _ ↦ by decide +kernel⟩)
    exact h'
  case sha256 =>
    have h := jcc_rel32_effect_step (backedgePC .sha256) 3 0xffffff51
    have h' := h.mono_pre (pre' := fun s ↦ s.RIP = backedgePC .sha256)
      (fun s hip ↦ ⟨hip, fun _ ↦ by decide +kernel⟩)
    exact h'
  case sha384 =>
    have h := jcc_rel8_effect_step (backedgePC .sha384) 3 0x84
    have h' := h.mono_pre (pre' := fun s ↦ s.RIP = backedgePC .sha384)
      (fun s hip ↦ ⟨hip, fun _ ↦ by decide +kernel⟩)
    exact h'
  case sha512 =>
    have h := jcc_rel8_effect_step (backedgePC .sha512) 3 0xa4
    have h' := h.mono_pre (pre' := fun s ↦ s.RIP = backedgePC .sha512)
      (fun s hip ↦ ⟨hip, fun _ ↦ by decide +kernel⟩)
    exact h'

theorem backedge_image (v : Variant) :
    (∀ byte ∈ codeRange (comparePC v) (compareBytes v), byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (backedgePC v) (backedgeBytes v), byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2) := by
  cases v <;> decide +kernel

theorem backedge_inProgram (v : Variant) :
    InProgram (backedgePC v) ∧ InProgram (exitAddress v) ∧ InProgram (start v) := by
  constructor
  · refine ⟨if v = .sha224 ∨ v = .sha256 then 0x0f else 0x73, ?_⟩
    apply imageSections_mem_toCodeMap_of_fetchByte
    cases v <;> decide +kernel
  · constructor
    · refine ⟨0x4d, ?_⟩
      apply imageSections_mem_toCodeMap_of_fetchByte
      cases v <;> decide +kernel
    · refine ⟨0x49, ?_⟩
      apply imageSections_mem_toCodeMap_of_fetchByte
      cases v <;> decide +kernel

theorem backedge_advance [Bindings] {boundary : ReturnBoundary} {v : Variant} {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (boundaryOutside : ¬ InProgram boundary.rip) (ip : s.RIP = comparePC v) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if ((Operand.reg 5 : Operand 64).read s).toNat < 8 * v.lanes
        then (exitAddress v) else start v) ∧ AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, lu, eu, fu⟩ := scalar_advance (cs := [.flags, .rip])
    (compare_effect v) (backedge_image v).1
    (by intro s; simp [compareEffect, Effect.components])
    (by simp [Component.Covers]) ready loaded boundaryOutside
    (fun _ ↦ (backedge_inProgram v).1) ip
  obtain ⟨t, ht, rt, lt, et, ft⟩ := scalar_advance (cs := [.flags, .rip])
    (backedge_effect v) (backedge_image v).2
    (by intro s; simp [backedgeEffect, branchEffect_components])
    (by simp [Component.Covers]) ru lu boundaryOutside
    (fun u ↦ by
      change InProgram (if condHolds 3 (StatusFlags.ofRFLAGS u.RFLAGS) then start v else (exitAddress v))
      split
      · exact (backedge_inProgram v).2.2
      · exact (backedge_inProgram v).2.1) eu.rip
  refine ⟨t, hu.trans ht, rt, lt, ?_, ?_⟩
  · have hcf : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
        (cmpSpec ((Operand.reg 5 : Operand 64).read s) (.ofNat 64 (8 * v.lanes))).CF :=
      eu.flags.1
    have he := et.rip
    change t.RIP = (if !(StatusFlags.ofRFLAGS u.RFLAGS).CF then start v else (exitAddress v)) at he
    rw [hcf] at he
    have hn : (BitVec.ofNat 64 (8 * v.lanes)).toNat = 8 * v.lanes := by
      have := laneBound v
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simpa only [cmpSpec, subSpec, hn, Bool.not_eq_true',
      decide_eq_false_iff_not, ite_not] using he
  · apply (fu.trans ft).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

theorem callPC_values :
    callPC .sha224 = 0x100a6b ∧ callPC .sha256 = 0x10074d ∧
    callPC .sha384 = 0x100441 ∧ callPC .sha512 = 0x100171 := by decide +kernel

theorem callReturn_inProgram (v : Variant) : InProgram (comparePC v) := by
  refine ⟨0x48, ?_⟩
  apply imageSections_mem_toCodeMap_of_fetchByte
  cases v <;> decide +kernel

theorem comparePC_values :
    comparePC .sha224 = 0x100a70 ∧ comparePC .sha256 = 0x100752 ∧
    comparePC .sha384 = 0x100446 ∧ comparePC .sha512 = 0x100176 := by decide +kernel

def callBytes : Variant → List UInt8
  | .sha224 => [0xe8, 0x50, 0x01, 0, 0]
  | .sha256 => [0xe8, 0x6e, 0x04, 0, 0]
  | .sha384 => [0xe8, 0x7a, 0x07, 0, 0]
  | .sha512 => [0xe8, 0x4a, 0x0a, 0, 0]

def callDisplacement : Variant → BitVec 32
  | .sha224 => 0x150 | .sha256 => 0x46e | .sha384 => 0x77a | .sha512 => 0xa4a

theorem call_encoding (v : Variant) :
    callBytes v = encodeCallRel32 (callDisplacement v) ∧
    branchTarget (callPC v) 5 ((callDisplacement v).signExtend 64) = entryAddress .absorb := by
  cases v <;> decide +kernel

theorem call_image (v : Variant) :
    ∀ byte ∈ codeRange (callPC v) (callBytes v), byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2 := by
  cases v <;> decide +kernel

end Sha3.Proofs.Update.FullBlocks
