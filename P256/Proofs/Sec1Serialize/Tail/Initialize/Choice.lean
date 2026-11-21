import P256.Proofs.Sec1Serialize.Tail.Initialize.State
import P256.Proofs.Sec1Serialize.Memory
import P256.Proofs.Sec1Serialize.Conversion.Stage
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.Instructions.LegacyLoad
import P256.Proofs.Field.Inverse.Tail.Support
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem Preparing.after_registers
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (h : Preparing s t boundary bytes infinity) {e : Effect}
    (step : Machine.step t = some (.next u)) (ready : ReadyToStep u)
    (effect : e.Holds t u)
    (hm : ∀ c ∈ e.components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ e.components) (bp : .reg 5 ∉ e.components)
    (next : InProgram e.rip)
    (df : Component.df ∉ e.components := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ e.components := by component_not_mem)
    (fcw : Component.fcw ∉ e.components := by component_not_mem) :
    Preparing s u boundary bytes infinity := by
  have memory := effect.agrees.external hm
  refine ⟨h.state.after_registers ready effect.agrees hm sp df mxcsr fcw,
    ?_, (effect.agrees.read (n := 64) bp).trans h.destination,
    memory ▸ h.source, ?_, memory ▸ h.inputFlag, memory ▸ h.zeroSource⟩
  · obtain ⟨n, run⟩ := h.execution
    exact ⟨n+1, run.trans (Advances.of_step step (.inl (by
      rw [effect.rip]
      exact boundary_ne_program pre.outerBoundary next)))⟩
  · change memLoad u.external _ _ = _
    rw [memory]
    exact h.savedInput

theorem prepare_choose (pre : CalleePre s boundary 0x110d70 72 65 328)
    (h : Preparing s t boundary bytes infinity) (rip : t.RIP = 0x111134) :
    ∃ u, Preparing s u boundary bytes infinity ∧ u.RIP = 0x111141 ∧
      u.regValue .rax = if infinity then 1 else 0 := by
  have code1 : CodeIn (codeRange 0x111134 [0x48, 0x8b, 0x44, 0x24, 0x78]) t :=
    programText_slice (programLoaded_codeIn h.state.loaded) 0x11134 _
      (by decide +kernel) (by decide +kernel)
  have addr1 : (AddrMode.sib 4 none 0 (.d8 120)).addr t 0x111139 = stackPtr s - 192 := by
    change stackPtr t + 120 = _
    rw [h.state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read1 : MemReadable t ((AddrMode.sib 4 none 0 (.d8 120)).addr t 0x111139) 8 := by
    rw [addr1]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 192)
      (by decide) (by decide)) h.state.allocated
  obtain ⟨t1, step1, ready1, effect1⟩ := mov_r64_m64_effect_step 0x111134 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl
    t (readyToStep h.state.machine h.state.bindingsSupported) code1 ⟨rip, read1⟩
  change (movR64M64Effect 0x111134 0 (.sib 4 none 0 (.d8 120)) t).Holds t t1 at effect1
  have h1 := h.after_registers pre step1 ready1 effect1
    (by simp [Component.Covers]) (by simp) (by simp)
    (inProgram_of_textOffset 0x11139 (by decide))
  have rax1 : t1.regValue .rax = s.regValue .rsi := by
    have e : t1.regValue .rax = (Operand.mem ((AddrMode.sib 4 none 0 (.d8 120)).addr t 0x111139) : Operand 64).read t := effect1.writes
    rw [e, addr1]
    exact h.savedInput
  have code2 : CodeIn (codeRange 0x111139 [0x8b, 0x78, 0x40]) t1 :=
    programText_slice (programLoaded_codeIn h1.state.loaded) 0x11139 _
      (by decide +kernel) (by decide +kernel)
  have addr2 : (AddrMode.base 0 (.d8 64)).addr t1 0x11113c = s.regValue .rsi + 64 := by
    change t1.regValue .rax + 64 = _
    rw [rax1]
  have read2 : MemReadable t1 ((AddrMode.base 0 (.d8 64)).addr t1 0x11113c) 4 := by
    rw [addr2]
    exact Conversion.input_readable pre h1.state.allocated (offset := 64) (by decide)
  obtain ⟨t2, step2, ready2, effect2⟩ :=
    P256.Proofs.Common.Instructions.LegacyLoad.mov_r32_m32_legacy_effect_step
      0x111139 7 (.base 0 (.d8 64)) (by decide) rfl rfl
      t1 ready1 code2 ⟨effect1.rip, read2⟩
  change (P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect
    0x111139 7 (.base 0 (.d8 64)) t1).Holds t1 t2 at effect2
  have h2 := h1.after_registers pre step2 ready2 effect2
    (by simp [P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components, Component.Covers])
    (by simp [P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components])
    (by simp [P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components])
    (inProgram_of_textOffset 0x1113c (by decide))
  have flag : (Operand.reg 7 : Operand 8).read t2 = if infinity then 1 else 0 := by
    have e : t2.regValue .rdi = ((Operand.mem ((AddrMode.base 0 (.d8 64)).addr t1 0x11113c) : Operand 32).read t1).setWidth 64 := effect2.writes
    change (t2.regValue .rdi).setWidth 8 = _
    rw [e, addr2]
    change ((memLoad t1.external (s.regValue .rsi + 64) 32).setWidth 64).setWidth 8 = _
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      P256.Proofs.Field.Inverse.memLoad32_lowByte]
    change ((t1.external[s.regValue .rsi + 64]?).getD 0).toBitVec = _
    rw [h1.inputFlag]
    cases infinity <;> rfl
  obtain ⟨u, run, ready, rsp, ip, value, agrees⟩ :=
    choice_step pre (frameOffset := 312) (by decide) (by decide)
      ready2 h2.state.loaded h2.state.allocated h2.state.rsp
      0x1113c 0x7f2f (by decide) (by decide +kernel) (by decide +kernel) effect2.rip
  have writes : WritesWithin (choiceClobbers s 312)
      #v[registerRegion s .rdi 65, workRegion s 328] := by
    intro c hc a ha
    simp only [choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s 328, by simp, work_contains pre (by decide) (by decide) ha⟩
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans h2.state.frame (output_work_frame pre memory)
  have state : FrameState s u 65 328 312 := by
    refine ⟨bindingsSupported_of_ready_agrees h2.state.bindingsSupported ready agrees,
      supportedMachine_of_ready_agrees h2.state.machine ready agrees,
      loaded_of_frame pre total, agrees.directionFlagClear (by simp [choiceClobbers]) h2.state.directionFlag,
      fun a ha => agrees.grow a (h2.state.allocated a ha), total,
      rsp.trans h2.state.rsp, ?_, ?_,
      (agrees.mxcsr (by simp [choiceClobbers])).trans h2.state.mxcsr,
      (agrees.fcw (by simp [choiceClobbers])).trans h2.state.fp87⟩
    · intro entry he
      have bound : entry.2 ≤ 48 := by
        simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (output_work_read pre (by decide) memory bound (by omega)).trans (h2.state.saved entry he)
    · have eq := output_work_read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
      simp only [BitVec.sub_zero] at eq
      exact eq.trans h2.state.returnAddress
  have apart (offset len : Nat) (ho : offset ≤ 312) (hl : len ≤ offset + 8) :
      ∀ a n, Component.mem a n ∈ choiceClobbers s 312 →
        RangeApart a n (stackPtr s - BitVec.ofNat 64 offset) len := by
    intro a n hc
    simp only [choiceClobbers, List.mem_cons, List.not_mem_nil, or_false,
      Component.mem.injEq, reduceCtorEq, false_or] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact stack_sub_apart pre.stack (a := 320) (na := 8)
        (by decide) (by omega) (by decide) hl (.inl (by omega))
    · exact stack_sub_apart pre.stack (a := 321) (na := 1)
        (by decide) (by omega) (by decide) hl (.inl (by omega))
  refine ⟨u, ⟨state, ?_, ?_, ?_, ?_, ?_, ?_⟩, ip, ?_⟩
  · obtain ⟨n, hn⟩ := h2.execution
    exact ⟨n+6, hn.trans run⟩
  · exact (agrees.read (n := 64) (r := 5) (by simp [choiceClobbers])).trans h2.destination
  · exact hasBytes_agrees_apart agrees (apart 113 65 (by decide) (by decide)) h2.source
  · exact (memLoad_agrees_apart agrees (apart 192 8 (by decide) (by decide))).trans h2.savedInput
  · exact (input_byte pre state (i := 64) (by decide)).trans
      ((input_byte pre h2.state (i := 64) (by decide)).symm.trans h2.inputFlag)
  · exact hasBytes_agrees_apart agrees (apart 184 65 (by decide) (by decide)) h2.zeroSource
  · rw [value, flag]
    cases infinity <;> rfl

end P256.Proofs.Sec1Serialize
