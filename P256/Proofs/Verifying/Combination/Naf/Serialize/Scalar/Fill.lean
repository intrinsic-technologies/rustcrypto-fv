import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Setup
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Nested
import P256.Proofs.Program.Fill
import P256.Proofs.Program.Copy.Pointer

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

theorem memset_pointer {t : RamState} (loaded : ProgramLoaded t) :
    MemReadable t 0x204550 8 ∧ (Operand.mem 0x204550 : Operand 64).read t = 0x11c810 := by
  have hbytes : ∀ i : Fin 8,
      Extracted.programSections.fetchByte (0x204550 + BitVec.ofNat 64 i.val) =
        some (storedByte (0x11c810 : BitVec 64) i.val) := by decide +kernel
  have hb : Bytes t.external 0x204550 8 (storedByte (0x11c810 : BitVec 64)) :=
    fun i hi => loaded _ _ (hbytes ⟨i, hi⟩)
  exact ⟨hb.readable (by decide), hb.memLoad (by decide) (by decide)⟩

theorem fill_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : FrameState s t cursor) (rip : t.RIP = 0x10b31a) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x11c810) 0x10b320 t).Holds t u := by
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [call_address state]
    exact writable_of_grow
      (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
        (offset := 368) (by decide) (by decide)) state.allocated
  have apart : RangeApart (pushAddr t) 8 0x10b31a 6 := by
    rw [call_address state]
    exact stack_code_apart pre
      (offset := 368) (codeOffset := 0xb31a) (by decide) (by decide) (by decide)
  have pointer := memset_pointer state.loaded
  have target : callMemPtr 0x10b31a (.rip 0xf9230) t = 0x11c810 := pointer.2
  obtain ⟨u, step, ready, effect⟩ := call_m64_effect_step 0x10b31a (.rip 0xf9230)
    trivial rfl rfl t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xb31a _ (by decide) (by decide +kernel))
    ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide +kernel⟩, pointer.1⟩
  have atTarget : u.RIP = 0x11c810 := effect.rip.trans target
  refine ⟨u, Advances.of_step step (.inl ?_), ready,
    atTarget, effect.writes, effect.flags, effect.agrees⟩
  rw [atTarget]
  exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c810 (by decide))

theorem fill_digits [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (rip : t.RIP = 0x10b30b)
    (input : Nat256At t (stackPtr s-48) n) :
    ∃ fuel u, Advances boundary fuel t u ∧ Memory s u cursor point ∧
      u.RIP = 0x10b320 ∧ u.regValue .rbx = t.regValue .rbx ∧
      u.regValue .r14 = stackPtr s-344 ∧ Nat256At u (stackPtr s-48) n ∧
      Bytes u.external (stackPtr s-344) 257 (fun _ => 0) := by
  obtain ⟨fuelSetup, setup, runSetup, readySetup, _, effectSetup⟩ :=
    fillSetup_correct boundary pre.outerBoundary t (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xb30b fillSetupBytes
        (by decide) (by decide +kernel)) rip
  have agSetup : AgreesExcept [.reg 14, .reg 2, .reg 7, .reg 6, .flags, .rip] t setup := effectSetup.agrees
  have stateSetup : Memory s setup cursor point := state.registers readySetup agSetup
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp) (by simp)
  have memSetup : setup.external = t.external := agSetup.external (by simp [Component.Covers])
  have setupValues := effectSetup.writes
  change setup.regValue .r14 = stackPtr t+16 ∧ setup.regValue .rdx = 257 ∧
    setup.regValue .rdi = stackPtr t+16 ∧ setup.regValue .rsi = 0 at setupValues
  have destination : setup.regValue .rdi = stackPtr s-344 :=
    setupValues.2.2.1.trans (stack_address state.rsp (offset := 16) (by decide))
  have r14 : setup.regValue .r14 = stackPtr s-344 :=
    setupValues.1.trans (stack_address state.rsp (offset := 16) (by decide))
  have rbx : setup.regValue .rbx = t.regValue .rbx := agSetup.read (n := 64) (r := 3) (by simp)
  obtain ⟨called, runCall, readyCall, effectCall⟩ := fill_call pre stateSetup.toFrameState effectSetup.rip
  have frameCall := stateSetup.toFrameState.after_call pre readyCall effectCall
  have outputCall : called.regValue .rdi = stackPtr s-344 :=
    (effectCall.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have zeroCall : called.regValue .rsi = 0 :=
    (effectCall.agrees.read (n := 64) (r := 6) (by simp)).trans setupValues.2.2.2
  have lengthCall : called.regValue .rdx = 257 :=
    (effectCall.agrees.read (n := 64) (r := 2) (by simp)).trans setupValues.2.1
  have returnCall : (returnBoundary called).rip = 0x10b320 := (callEffect_stack effectCall).1
  have callee : CalleePre called boundary 0x11c810 0 257 0 :=
    empty_input_pre pre frameCall effectCall.rip outputCall (by decide) (by decide) (by decide)
      (by rw [zeroCall]; decide +kernel)
      (returnCall ▸ inProgram_of_textOffset 0xb320 (by decide))
  have cursorCall : memLoad called.external cursor 64 = point+128 := by
    apply Eq.trans (cursor_read_of_frame pre ?_) stateSetup.cursorValue
    intro a ha
    apply effectCall.agrees.memoryWriteFrame (call_writes pre stateSetup.toFrameState) a
    intro region hr hin
    have eq : region = Stack.region s 536 := by simpa using hr
    exact ha _ (by simp [eq]) hin
  have inputCall : Nat256At called (stackPtr s-48) n := by
    refine ⟨input.1, fun i hi => ?_⟩
    have kept := call_byte stateSetup.toFrameState effectCall (offset := 48) (len := 32)
      (by decide) (by decide) hi
    rw [memSetup] at kept
    exact kept.trans (input.2 i hi)
  obtain ⟨u, result, bytes, _⟩ := P256.Proofs.Program.memset_zero_correct callee
    (by rw [zeroCall]; decide +kernel) lengthCall (by decide)
  have work := stack_result_work_frame pre frameCall result outputCall (by decide) (by decide) (by decide)
  have finalState : Memory s u cursor point :=
    ⟨frameCall.after_result pre result work, (work_cursor_read pre work).trans cursorCall⟩
  obtain ⟨fuelFill, runFill⟩ := result.execution
  refine ⟨fuelSetup+1+fuelFill, u, (runSetup.trans runCall).trans runFill, finalState,
    result.rip.trans returnCall, ?_, ?_, ?_, ?_⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effectCall.agrees.read (n := 64) (r := 3) (by simp)).trans rbx)
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effectCall.agrees.read (n := 64) (r := 14) (by simp)).trans r14)
  · refine ⟨inputCall.1, fun i hi => ?_⟩
    exact (stack_result_byte pre frameCall result outputCall (offset := 48) (len := 32)
      (by decide) (by decide) (by decide) (.inl (by decide)) hi).trans (inputCall.2 i hi)
  · rw [outputCall] at bytes
    exact bytes

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
