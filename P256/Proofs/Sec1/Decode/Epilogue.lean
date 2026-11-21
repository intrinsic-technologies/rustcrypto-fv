import P256.Proofs.Sec1.Decode.Frame
import P256.Proofs.Sec1.Decode.Restore
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) (state : Frame s t) (rip : t.RIP = 0x10e699)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 80 3680 ∧ u.external = t.external := by
  obtain ⟨v, av, rv, ev⟩ :=
    (add_r64_imm32_effect_step 0x10e699 0x48 0xc4 280
      (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xe699 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe6a0 (by decide)))
  have gv : AgreesExcept [.reg 4, .flags, .rip] t v := ev.agrees
  have mv : v.external = t.external := gv.external (by simp [Component.Covers])
  have spv : stackPtr v = stackPtr s - 32 := by
    have hw : stackPtr v = stackPtr t + 280 := ev.writes
    rw [hw, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have lv : ProgramLoaded v := by simpa only [ProgramLoaded, mv] using state.loaded
  have reads : ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      MemReadable v (stackPtr v + BitVec.ofNat 64 off) 8 := by
    intro off member
    have h : off ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have ha : stackPtr v + BitVec.ofNat 64 off = stackPtr s - BitVec.ofNat 64 (32-off) := by
      rw [ScalarFrame.scalar_stack_address spv (by decide) h]
    rw [ha]
    exact (readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega))
      state.allocated).of_external_eq mv
  obtain ⟨w, aw, rw', iw, spw, mw, gw, bx, r12, r14, r15⟩ :=
    restore_registers rv lv pre.outerBoundary ev.rip reads
  have mw' : w.external = t.external := mw.trans mv
  have spw' : stackPtr w = stackPtr s := by rw [spw, spv, BitVec.sub_add_cancel]
  have top : stackTop w = (returnBoundary s).rip := by
    change memLoad w.external (stackPtr w) 64 = _
    rw [spw', mw']
    exact state.returnAddress
  have lw : ProgramLoaded w := by simpa only [ProgramLoaded, mw'] using state.loaded
  obtain ⟨u, au, ru, eu⟩ := (ret_effect_step 0x10e6a7).advances rw'
    (programText_slice (programLoaded_codeIn lw) 0xe6a7 [0xc3]
      (by decide) (by decide +kernel))
    ⟨⟨iw, by
      rw [spw']
      simpa only [BitVec.sub_zero] using
        (readable_of_grow (stack_sub_readable pre.stack (offset := 0) (len := 8)
          (by decide) (by decide)) state.allocated).of_external_eq mw'⟩,
      top ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop w ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have gu : AgreesExcept [.reg 4, .rip] w u := eu.agrees
  have memory : u.external = t.external := (gu.external (by simp [Component.Covers])).trans mw'
  have all := (gv.trans gw).trans gu
  refine ⟨u, ⟨?_, eu.rip.trans top, ?_,
    bindingsSupported_of_ready_agrees state.bindingsSupported ru all,
    supportedMachine_of_ready_agrees state.machine ru all, ?_,
    all.directionFlagClear (by simp) state.directionFlag,
    (all.mxcsr (by simp)).trans state.mxcsr, (all.fcw (by simp)).trans state.fp87,
    ?_, ?_, fun a ha ↦ all.grow a (state.allocated a ha)⟩, memory⟩
  · obtain ⟨fuel, before⟩ := execution
    exact ⟨fuel + 1 + 4 + 1, ((before.trans av).trans aw).trans au⟩
  · have hw : stackPtr u = stackPtr w + 8 := eu.writes
    change stackPtr u = stackPtr s + 8
    rw [hw, spw']
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · apply (gu.read (n := 64) (r := 3) (by simp)).trans
      change w.regValue .rbx = s.regValue .rbx
      rw [bx, spv, mv]
      exact state.saved (.rbx,32) (by simp [savedSlots])
    · exact (all.read (n := 64) (r := 5) (by simp)).trans (state.registers .rbp (by simp))
    · apply (gu.read (n := 64) (r := 12) (by simp)).trans
      change w.regValue .r12 = s.regValue .r12
      rw [r12, spv, mv]
      have h := state.saved (.r12,24) (by simp [savedSlots])
      change memLoad t.external (stackPtr s - 24) 64 = _ at h
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] using h
    · exact (all.read (n := 64) (r := 13) (by simp)).trans (state.registers .r13 (by simp))
    · apply (gu.read (n := 64) (r := 14) (by simp)).trans
      change w.regValue .r14 = s.regValue .r14
      rw [r14, spv, mv]
      have h := state.saved (.r14,16) (by simp [savedSlots])
      change memLoad t.external (stackPtr s - 16) 64 = _ at h
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] using h
    · apply (gu.read (n := 64) (r := 15) (by simp)).trans
      change w.regValue .r15 = s.regValue .r15
      rw [r15, spv, mv]
      have h := state.saved (.r15,8) (by simp [savedSlots])
      change memLoad t.external (stackPtr s - 8) 64 = _ at h
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] using h
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) (state : Frame s t) (rip : t.RIP = 0x10e696)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 80 3680 ∧ u.external = t.external := by
  obtain ⟨v, av, rv, ev⟩ :=
    (mov_r64_r64_effect_step 0x10e696 0x48 0xf8 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xe696 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe699 (by decide)))
  have gv : AgreesExcept [.reg 0, .rip] t v := ev.agrees
  have sv := state.after_registers pre rv gv (by simp [Component.Covers]) (by simp)
  obtain ⟨u, result, memory⟩ := epilogue pre sv ev.rip (by
    obtain ⟨fuel, before⟩ := execution
    exact ⟨fuel+1, before.trans av⟩)
  exact ⟨u, result, memory.trans (gv.external (by simp [Component.Covers]))⟩

end P256.Proofs.Sec1.Decode
