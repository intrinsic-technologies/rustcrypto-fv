import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Standard.Initialization.Hash
import Hkdf.Proofs.Standard.Memory.Buffer
import Hkdf.Proofs.Common.Pad.Loop
import Hkdf.Proofs.Common.Pad.Permissions
import Hkdf.Proofs.Common.Pad.Model
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine

theorem outer_pad [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (ready : ReadyToStep s)
    (state : InnerHashed initial s salt) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      OuterReady initial t salt := by
  have outside := (Standard.returnBoundary_valid ctx).2.2
  have pointer : Standard.hmacBase initial = stackPtr initial - 400 := by
    change stackPtr initial - 520 + 120 = stackPtr initial - 400
    bv_omega
  have avoid : (Stack.region initial hkdfSha256Extract.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (ctx.call.stackSeparation.2 _ (by simp)).2
  obtain ⟨u, move, readyU, effect⟩ := (mov_r32_imm32_effect_step 0x10150b 0xb8
    (by decide) 3).advances ready
    (programText_slice (programLoaded_codeIn state.loaded) 0x150b
      [0xb8,3,0,0,0] (by decide) (by decide +kernel)) state.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x1510 (by decide)))
  have moveFrame : AgreesExcept [.reg 0, .rip] s u := effect.agrees
  have moved : AgreesExcept (Pad.components (Standard.hmacBase initial)) s u :=
    moveFrame.mono (by simp [Pad.components])
  have memory : u.external = s.external := moveFrame.external (by simp [Component.Covers])
  have runningU := state.toRunning.of_agrees move readyU moveFrame (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ha.elim) (by
      intro region member a contains inside
      have equal : region = Stack.region initial hkdfSha256Extract.minStackBytes := by
        simpa using member
      subst region
      exact avoid a contains (.inl inside)) (by simp)
  have rspU : u.regValue .rsp = Standard.frameBase initial :=
    (moveFrame.read (n := 64) (r := 4) (by simp)).trans state.rsp
  have writable := Common.Machine.stack_writable ctx.call.stack
    (used := 400) (by decide +kernel) avoid
  have converted : Hkdf.Proofs.Refine.Writable Extracted.programImage initial.external
      (Standard.hmacBase initial) (400 + 8) := by
    rw [pointer]
    exact writable
  have bufferWritable : Hkdf.Proofs.Refine.Writable Extracted.programImage initial.external
      (Standard.hmacBase initial) 64 :=
    converted.sub (Nat.le_refl _) (by omega)
  have pre : Pad.Pre .v101510 (returnBoundary initial) u (Standard.hmacBase initial)
      (HMAC.xorPad (HMAC.keyBlock (Standard.saltKey salt)) 0x36) := {
    machine := runningU.machine
    loaded := runningU.loaded
    directionFlag := runningU.directionFlag
    outside := outside
    rip := effect.rip
    index := effect.writes
    base := by
      change Standard.frameBase initial + 120 = u.regValue .rsp + 120
      rw [rspU]
    bytes := by rw [memory]; exact state.block
    writable := ⟨⟨bufferWritable.readable.low,
      fun i hi ↦ runningU.allocated _ (bufferWritable.readable.present i hi)⟩,
      bufferWritable.tables, bufferWritable.notCode⟩ }
  obtain ⟨fuel, t, loop, readyT, ripT, _, loopFrame, stored⟩ :=
    Pad.contract_of_loop (by rfl) pre readyU outside
  have frame := Pad.agrees_trans moved loopFrame
  have bufferFrame := frame.memoryWriteFrame (Pad.writesWithin bufferWritable.readable.low)
  have writes : WritesWithin (Pad.components (Standard.hmacBase initial))
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] := by
    rw [pointer]
    intro c hc a ha
    simp only [Pad.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact ha.elim
    · exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
        Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.call.stack.2.2.1
          (by decide +kernel) (by decide) ha⟩
    · exact ha.elim
  have run := move.trans loop
  have final := state.toRunning.of_agrees run readyT frame writes (by
    intro region member a contains inside
    have equal : region = Stack.region initial hkdfSha256Extract.minStackBytes := by
      simpa using member
    subst region
    exact avoid a contains (.inl inside)) (by simp [Pad.components])
  have rspT : t.regValue .rsp = Standard.frameBase initial :=
    (frame.read (n := 64) (r := 4) (by simp [Pad.components])).trans state.rsp
  have preserved := state.toPreserved.of_buffer_frame final bufferFrame rspT
  have hashAddress : Standard.frameBase initial + 56 = stackPtr initial - 464 := by
    change stackPtr initial - 520 + 56 = stackPtr initial - 464
    bv_omega
  have countAddress : Standard.frameBase initial + 88 = stackPtr initial - 432 := by
    change stackPtr initial - 520 + 88 = stackPtr initial - 432
    bv_omega
  have hashSame : (Component.mem (Standard.frameBase initial + 56) 32).Agrees s t := by
    rw [hashAddress]
    exact Standard.buffer_frame_agrees bufferFrame (by decide) (by
      unfold OffsetsApart; decide +kernel)
  have countSame : (Component.mem (Standard.frameBase initial + 88) 8).Agrees s t := by
    rw [countAddress]
    exact Standard.buffer_frame_agrees bufferFrame (by decide) (by
      unfold OffsetsApart; decide +kernel)
  refine ⟨1 + fuel, t, run, readyT, ⟨⟨preserved, ?_, ?_, ?_⟩, ripT, ?_⟩⟩
  · exact Hkdf.Proofs.Wrapper.hashState_of_bytes state.innerHash hashSame
  · exact (agrees_loadBytes countSame).trans state.innerBlocks
  · rcases state.ivRegisters with ⟨rbx, r14, r12, r13⟩
    exact ⟨(frame.read (n := 64) (r := 3) (by simp [Pad.components])).trans rbx,
      (frame.read (n := 64) (r := 14) (by simp [Pad.components])).trans r14,
      (frame.read (n := 64) (r := 12) (by simp [Pad.components])).trans r12,
      (frame.read (n := 64) (r := 13) (by simp [Pad.components])).trans r13⟩
  · simpa only [Pad.layout, Pad.xorPad_inner_to_outer] using stored

end Hkdf.Proofs.Standard.Initialization
