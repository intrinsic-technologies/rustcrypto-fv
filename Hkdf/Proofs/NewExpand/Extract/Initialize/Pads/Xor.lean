import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Frame
import Hkdf.Proofs.Common.Pad.Loop
import Hkdf.Proofs.Common.ExtractCaller.PadEntry

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Pads

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def variant (outer : Bool) : Pad.Variant :=
  if outer then .v10fb70 else .v10faf0

theorem xorPad_inner_to_outer (block : ByteArray) :
    HMAC.xorPad (HMAC.xorPad block 0x36) 0x6a = HMAC.xorPad block 0x5c := by
  apply ByteArray.ext
  simp only [HMAC.xorPad, Array.map_map]
  congr 1
  funext byte
  exact UInt8.xor_assoc byte 0x36 0x6a

private theorem entry [Bindings] (outer : Bool) {s : RamState} {boundary : ReturnBoundary}
    (machine : Hkdf.Proofs.Program.SupportedMachine inferInstance s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = if outer then 0x10fb64 else 0x10fadf) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (variant outer).entry ∧ t.regValue .rax = 3 ∧
      AgreesExcept [.reg 0, .rip] s t ∧ t.external = s.external := by
  have ready := supportedMachine_readyToStep machine
  cases outer
  · have nop : StepEffect (fun s ↦ s.RIP = 0x10fae4)
        (codeRange 0x10fae4 [0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0])
        (fun _ ↦ nopEffect 0x10fae4 12) :=
      nop_m_effect_step _ [0x66,0x66,0x66,0x2e] (by decide) (by decide)
        (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl
    obtain ⟨t, run, readyT, _, _, ripT, index, frame, memory⟩ :=
      ExtractCaller.PadEntry.mov_eax_three_nop (offset := 0xfadf) nop ready machine loaded
        outside rip (by decide) (by decide +kernel) (by decide +kernel)
    exact ⟨t, run, readyT, ripT, index, frame, memory⟩
  · have nop : StepEffect (fun s ↦ s.RIP = 0x10fb69)
        (codeRange 0x10fb69 [0x0f,0x1f,0x80,0,0,0,0])
        (fun _ ↦ nopEffect 0x10fb69 7) :=
      nop_m_effect_step _ [] (by decide) (by decide) (.base 0 (.d32 0))
        (by decide) rfl rfl
    obtain ⟨t, run, readyT, _, _, ripT, index, frame, memory⟩ :=
      ExtractCaller.PadEntry.mov_eax_three_nop (offset := 0xfb64) nop ready machine loaded
        outside rip (by decide) (by decide +kernel) (by decide +kernel)
    exact ⟨t, run, readyT, ripT, index, frame, memory⟩

abbrev padRegion (initial : RamState) : MemoryRegion := slotRegion initial 336 64

theorem padding [Bindings] (outer : Bool) {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm raw : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (state : Frame initial s boundary)
    (rip : s.RIP = if outer then 0x10fb64 else 0x10fadf)
    (stored : (padRegion initial).HasBytes s.external raw) :
    ∃ t, Frame initial t boundary ∧ t.RIP = (if outer then 0x10fb8e else 0x10fb0e) ∧
      (padRegion initial).HasBytes t.external (HMAC.xorPad raw (if outer then 0x6a else 0x36)) ∧
      AgreesExcept (Pad.components (slot initial 336)) s t ∧
      MemoryWriteFrame s t #v[padRegion initial] := by
  have outside := pre.call.outerBoundary
  have stack := pre.call.stack
  let pointer := slot initial 336
  obtain ⟨u, enter, readyU, ripU, index, entered, memory⟩ :=
    entry outer state.machine state.loaded outside rip
  have readable : MemReadable u pointer 64 :=
    stack_readable stack (fun a ha ↦ entered.grow a (state.allocated a ha)) (by decide) (by decide)
  have writable : MemWritable u pointer 64 :=
    MemWritable.of_not_reserved (by decide) readable.low readable.mem (by
      intro i hi h
      exact pre.call.stackAvoid _ (stackRegion_contains_sub stack.2.2.1
        (offset := 336) (len := 64) (by decide) (by decide) ⟨i, hi, rfl⟩) (.inr h))
  have conditions : Pad.Pre (variant outer) boundary u pointer raw := {
    machine := supportedMachine_of_ready_agrees state.machine readyU entered
    loaded := by intro a b hb; rw [memory]; exact state.loaded a b hb
    directionFlag := entered.directionFlagClear (by simp) state.directionFlag
    outside := outside
    rip := ripU
    index := by cases outer <;> exact index
    base := by
      have rspU : stackPtr u = base initial :=
        (entered.read (n := 64) (r := 4) (by simp)).trans state.rsp
      cases outer <;>
        change pointer = stackPtr u + BitVec.ofNat 64 120 <;>
        rw [rspU, base_add initial (by decide)]
    bytes := by rw [memory]; exact stored
    writable := ⟨⟨readable.low, readable.mem⟩, writable.tables, ?_⟩ }
  case refine_1 =>
    intro pair isCode i hi same
    have inside := stackRegion_contains_sub stack.2.2.1
      (offset := 336) (len := 64) (by decide) (by decide) ⟨i, hi, rfl⟩
    apply pre.call.stackAvoid (pointer + BitVec.ofNat 64 i) inside
    exact .inl ⟨pair.2, by simpa only [← same, Prod.eta] using isCode⟩
  obtain ⟨fuel, t, loop, readyT, ripT, _, loopFrame, written⟩ :=
    Pad.contract_of_loop (by cases outer <;> rfl) conditions readyU outside
  have agrees := Pad.agrees_trans (entered.mono (by simp [Pad.components])) loopFrame
  have memoryFrame := agrees.memoryWriteFrame (Pad.writesWithin readable.low)
  have within : WritesWithin (Pad.components pointer) #v[Stack.region initial 2264] := by
    intro c hc a ha
    obtain ⟨r, hr, inside⟩ := Pad.writesWithin readable.low c hc a ha
    have eq : r = padRegion initial := by simpa only [Pad.regions, Vector.mem_singleton] using hr
    exact ⟨_, by simp, slotRegion_within stack (by decide) (by decide) (eq ▸ inside)⟩
  have running := state.toRunning.of_agrees (enter.trans loop) readyT agrees within
    (stack_avoids pre) (by simp [Pad.components])
  have endFrame := state.of_frame stack running memoryFrame
    (agrees.read (n := 64) (r := 4) (by simp [Pad.components]))
    (agrees.mxcsr (by simp [Pad.components])) (agrees.fcw (by simp [Pad.components])) (by
      intro r member
      have eq : r = padRegion initial := by simpa only [Pad.regions, Vector.mem_singleton] using member
      have output : base initial + 80 = slot initial 376 := base_add initial (offset := 80) (by decide)
      rw [eq, output]
      exact ⟨slotRegion_disjoint stack (by decide) (by decide) (.inl (by decide)),
        slotRegion_disjoint stack (by decide) (by decide) (.inr (by decide))⟩)
  exact ⟨t, endFrame, by cases outer <;> exact ripT,
    by cases outer <;> exact written, agrees, memoryFrame⟩

end Hkdf.Proofs.NewExpand.Extract.Initialize.Pads
