import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Frame
import Hkdf.Proofs.Common.Pad.Loop
import Hkdf.Proofs.Common.ExtractCaller.PadEntry

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.StreamPadding (base regions)
open Hkdf.Proofs.Common.StreamPadding.Execution

private def padVariant (outer : Bool) : Common.Pad.Variant :=
  if outer then .v10e160 else .v10e0d0

private theorem pad_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outer : Bool) (ready : ReadyToStep s) (machine : SupportedMachine inferInstance s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = if outer then 0x10e159 else 0x10e0c0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (padVariant outer).entry ∧ t.regValue .rax = 3 ∧
      AgreesExcept [.reg 0, .rip] s t := by
  cases outer
  · have padding : StepEffect (fun s ↦ s.RIP = 0x10e0c5)
        (codeRange 0x10e0c5 [0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0])
        (fun _ ↦ nopEffect 0x10e0c5 11) :=
      nop_m_effect_step _ [0x66,0x66,0x2e] (by decide) (by decide)
        (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl
    obtain ⟨t, run, readyT, _, _, ripT, index, frame, _⟩ :=
      ExtractCaller.PadEntry.mov_eax_three_nop (offset := 0xe0c0) padding ready
        machine loaded outside rip (by decide) (by decide +kernel) (by decide +kernel)
    exact ⟨t, run, readyT, ripT, index, frame⟩
  · obtain ⟨t, run, readyT, _, _, ripT, index, frame, _⟩ :=
      ExtractCaller.PadEntry.mov_eax_three_nop (offset := 0xe159) (nop_66_effect_step _)
        ready machine loaded outside rip (by decide) (by decide +kernel) (by decide +kernel)
    exact ⟨t, run, readyT, ripT, index, frame⟩

theorem pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (outer : Bool) (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s)
    (rip : s.RIP = if outer then 0x10e159 else 0x10e0c0)
    {bytes : ByteArray}
    (stored : (MemoryRegion.mk (base .hmac initial + 72).toNat 64).HasBytes s.external bytes) :
    ∃ t, Suffix.State initial boundary t ∧
      t.RIP = (if outer then 0x10e17e else 0x10e0ee) ∧
      MemoryWriteFrame s t (writes initial) ∧
      AgreesExcept (Common.Pad.components (base .hmac initial + 72)) s t ∧
      (MemoryRegion.mk (base .hmac initial + 72).toNat 64).HasBytes t.external
        (HMAC.xorPad bytes (if outer then 0x6a else 0x36)) := by
  obtain ⟨u, runU, readyU, ripU, index, move⟩ := pad_entry outer
    (supportedMachine_readyToStep state.running.machine) state.running.machine
    state.running.loaded pre.outerBoundary rip
  have runningU := state.running.of_agrees runU readyU move
    (by simp [WritesWithin, Component.Covers]) (regions_avoids .hmac pre) (by simp)
  have rspU : stackPtr u = base .hmac initial :=
    (move.read (n := 64) (r := 4) (by simp)).trans state.rsp
  let pointer := base .hmac initial + BitVec.ofNat 64 72
  have raw : (MemoryRegion.mk pointer.toNat 64).HasBytes u.external bytes := by
    rw [move.external (by simp [Component.Covers])]
    exact stored
  have readable : MemReadable u pointer 64 := by
    simpa only [rspU] using local_readable .hmac pre runningU rspU 72 64 (by decide)
  have contained (i : Nat) (hi : i < 64) :
      (Stack.region initial 1264).Contains (pointer + BitVec.ofNat 64 i).toNat := by
    dsimp only [pointer]
    rw [local_address .hmac pre 72 (by decide)]
    exact stackRegion_contains_sub pre.stack.2.2.1 (offset := 336) (len := 64)
      (by decide) (by decide) ⟨i, hi, rfl⟩
  have writable : Hkdf.Proofs.Refine.Writable Extracted.programImage u.external pointer 64 := by
    refine ⟨⟨readable.low, readable.mem⟩, tables_of_not_reserved (by decide) readable.low ?_, ?_⟩
    · intro i hi reserved
      exact pre.avoids _ (by simp) _ (contained i hi) (.inr reserved)
    · intro x code i hi eq
      exact pre.avoids _ (by simp) _ (contained i hi) (.inl ⟨x.2, eq ▸ code⟩)
  have conditions : Common.Pad.Pre (padVariant outer) boundary u pointer bytes := {
    machine := runningU.machine
    loaded := runningU.loaded
    directionFlag := runningU.directionFlag
    outside := pre.outerBoundary
    rip := ripU
    index := by cases outer <;> exact index
    base := by
      cases outer <;> change pointer = stackPtr u + BitVec.ofNat 64 72 <;> rw [rspU]
    bytes := raw
    writable := writable }
  obtain ⟨fuel, t, runT, readyT, ripT, _, loopFrame, padded⟩ := Common.Pad.contract_of_loop
    (by cases outer <;> rfl) conditions readyU pre.outerBoundary
  have agrees := Common.Pad.agrees_trans
    (move.mono (by simp [Common.Pad.components])) loopFrame
  have footprint : WritesWithin (Common.Pad.components pointer) (writes initial) := by
    intro c member a covered
    simp only [Common.Pad.components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact covered.elim
    · exact covered.elim
    · have address : pointer = stackPtr s + BitVec.ofNat 64 72 := by
        dsimp only [pointer]
        rw [state.rsp]
        rfl
      rw [address] at covered
      exact local_within pre state.rsp 72 64 (by left; constructor <;> decide) a covered
    · exact covered.elim
  have frame := agrees.memoryWriteFrame footprint
  have final := state.of_agrees pre (runU.trans runT) readyT agrees
    (by
      intro c hc a ha
      obtain ⟨region, member, contains⟩ := footprint c hc a ha
      exact writes_within pre region member a.toNat contains)
    (by simp [Common.Pad.components]) (saved_after pre frame)
  refine ⟨t, final, ?_, frame, agrees, ?_⟩
  · cases outer <;> exact ripT
  · cases outer <;> exact padded

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey
