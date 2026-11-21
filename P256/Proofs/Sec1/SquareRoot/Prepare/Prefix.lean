import P256.Proofs.Sec1.SquareRoot.Prepare.Memory
import P256.Proofs.Sec1.SquareRoot.Prepare.InputCopy

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Field

theorem entry_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (entryComponents s) s t) :
    MemoryWriteFrame s t #v[registerRegion s .rdi 40, Stack.region s 2176] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  simp only [entryComponents, savedSources, pushSequenceFrame, Nat.reduceAdd,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals exact ⟨Stack.region s 2176, by simp,
    ScalarFrame.stack_contains pre (by decide) (by decide) ha⟩

theorem start [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 7 s t ∧ FrameState s t ∧ t.RIP = 0x114422 ∧
      t.regValue .rsi = s.regValue .rsi := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := field_sqrt_entry pre
  obtain ⟨u, step, readyU, effect⟩ :=
    (mov_r64_r64_effect_step 0x11441f 0x48 0xfb
      (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x1441f [0x48,0x89,0xfb]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14422 (by decide)))
  change (movR64R64Effect 0x11441f 3 7 t).Holds t u at effect
  have ag := agrees.trans effect.agrees
  have no (r : BitVec 5) (hr : r ≠ 3 ∧ r ≠ 4) :
      .reg r ∉ entryComponents s ++ (movR64R64Effect 0x11441f 3 7 t).components := by
    simpa [entryComponents, savedSources, pushSequenceFrame, and_comm] using hr
  have mem : u.external = t.external := effect.agrees.external (by simp [Component.Covers])
  refine ⟨u, run.trans step, ?_, effect.rip, ag.read (r := 6) (n := 64) (no 6 (by decide))⟩
  refine ⟨⟨bindingsSupported_of_ready_agrees pre.bindingsSupported readyU ag,
    supportedMachine_of_ready_agrees pre.machine readyU ag, ?_,
    ag.directionFlagClear (by simp [entryComponents, savedSources, pushSequenceFrame]) pre.directionFlag,
    ag.grow, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [ProgramLoaded, mem] using loaded
  · intro a ha
    rw [mem]
    exact entry_frame pre agrees a ha
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact ag.read (r := 13) (n := 64) (no _ (by decide))
  · exact effect.writes.trans (agrees.read (r := 7) (n := 64)
      (by simp [entryComponents, savedSources, pushSequenceFrame]))
  · exact ag.mxcsr (by simp [entryComponents, savedSources, pushSequenceFrame])
  · exact ag.fcw (by simp [entryComponents, savedSources, pushSequenceFrame])
  · exact entry_saved_words (mem.trans memory)
  · exact (effect.agrees.read (r := 4) (n := 64) (by simp)).trans rsp

theorem copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x114422) (rsi : t.regValue .rsi = s.regValue .rsi) :
    ScalarFrame.Copy32.Pre 0x114422
      (fun q => (Operand.reg 6 : Operand 64).read q + 0)
      (fun q => (Operand.reg 4 : Operand 64).read q + 192) t := by
  have dst (i : BitVec 64) :
      (Operand.reg 4 : Operand 64).read t + 192 + i = stackPtr s - (392 - i) := by
    rw [state.stack_address]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
    rw [← BitVec.add_assoc (-584)]
    rfl
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change MemReadable t (t.regValue .rsi + 0 + i) 8
    simp only [rsi, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact input_readable pre state.allocated (by decide)
  · intro i hi
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact (stack_buffer_writable pre.stack (pre.avoids _ (by simp))
      state.allocated (by decide) (by decide) (by decide))
  · change RangeApart ((Operand.reg 4 : Operand 64).read t + 192) 32
      (t.regValue .rsi + 0) 32
    rw [state.stack_address]
    simp only [rsi, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    simp only [BitVec.reduceSub]
    exact stack_input pre (by decide) (by decide)
  · intro i hi pc n hn
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_code pre (by decide) (by decide) hn

theorem input_copy [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Pre s boundary) (input : MontgomeryAt s (s.regValue .rsi) x) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t ∧ t.RIP = 0x114451 ∧
      MontgomeryAt t (stackPtr s - 392) x := by
  obtain ⟨t, run, state, rip, rsi⟩ := start pre
  have pc := copy_pre pre state rip rsi
  obtain ⟨n,u,runU,readyU,_,effect⟩ := InputCopy.run boundary pre.outerBoundary
    0x14422 (by decide) t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x14422 InputCopy.bytes
      (by decide +kernel) (by decide +kernel)) pc
  have dst : (Operand.reg 4 : Operand 64).read t + 192 = stackPtr s - 392 :=
    state.stack_address 192
  have ag := ScalarFrame.Copy32.frame effect
  rw [dst] at ag
  have frameU := frame_after pre state readyU ag (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [ScalarFrame.Copy32.components]) (by
      intro c hc a ha
      simp only [ScalarFrame.Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> try exact ha.elim
      exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩)
    (by simp [ScalarFrame.Copy32.components]) (by simp [ScalarFrame.Copy32.components])
    (by simp [ScalarFrame.Copy32.components])
  have copy := ScalarFrame.Copy32.copy_bytes effect
    (by change MemReadable t (t.regValue .rsi + 0) 32
        simp only [rsi, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        simpa only [BitVec.add_zero] using input_readable pre state.allocated (offset := 0) (by decide))
    (by rw [dst]; exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) frameU.allocated)
  have preserved (i : Nat) (hi : i < 32) :
      t.external[s.regValue .rsi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
    apply state.frame
    intro r hr hin
    have cases : r = registerRegion s .rdi 40 ∨ r = Stack.region s 2176 := by simpa using hr
    have src := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
    rcases cases with rfl | rfl
    · exact pre.separation (0 : Fin 3) 1 (by decide) _ src hin
    · exact pre.separation (0 : Fin 3) 2 (by decide) _ src hin
  refine ⟨7+n,u,run.trans runU,frameU,effect.rip,input.1,input.2.1,?_⟩
  intro i hi
  have h := copy i hi
  change u.external[((Operand.reg 4 : Operand 64).read t + 192) + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + 0 + BitVec.ofNat 64 i]? at h
  rw [dst] at h
  simp only [rsi, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h
  rw [preserved i hi] at h
  exact h.trans (input.2.2 i hi)

end P256.Proofs.Sec1.SquareRoot.Prepare
