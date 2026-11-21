import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Setup
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Nested
import P256.Proofs.Verifying.Combination.Naf.Machine.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.RecodeCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Program (stack_bounds stack_sub_toNat)
open P256.Proofs.Verifying.Combination.Naf
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat}
    (pre : ScalarPre s boundary cursor point) (state : Memory s t cursor point)
    (rip : t.RIP = 0x10b320) (r14 : t.regValue .r14 = stackPtr s-344)
    (input : Nat256At t (stackPtr s-48) n)
    (zeroes : Bytes t.external (stackPtr s-344) 257 (fun _ => 0)) :
    ∃ fuel w, Advances boundary fuel t w ∧ Memory s w cursor point ∧
      w.RIP = 0x10b346 ∧ w.regValue .rbx = t.regValue .rbx ∧
      w.regValue .rax = BitVec.ofNat 64 (digits n).length ∧
      ∀ i < 257, memLoad w.external (stackPtr s-344+BitVec.ofNat 64 i) 8 =
        BitVec.ofInt 8 (((digits n)[i]?).getD 0) := by
  obtain ⟨n0, a, run0, ready0, _, effect0⟩ := recodeSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xb320 recodeSetupBytes
      (by decide) (by decide +kernel)) rip
  have agrees0 : AgreesExcept [.reg 2, .reg 6, .reg 1, .reg 8, .reg 9, .reg 7, .rip] t a := effect0.agrees
  have memory0 : a.external = t.external := agrees0.external (by simp [Component.Covers])
  have stateA := state.registers ready0 agrees0 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have writes0 : a.regValue .rdx = stackPtr t+312 ∧ a.regValue .rsi = 257 ∧
      a.regValue .rcx = 32 ∧ a.regValue .r8 = 256 ∧ a.regValue .r9 = 5 ∧
      a.regValue .rdi = t.regValue .r14 := effect0.writes
  have src0 := writes0.1.trans (stack_address state.rsp (offset := 312) (by decide))
  have dst0 := writes0.2.2.2.2.2.trans r14
  obtain ⟨b, run1, ready1, effect1⟩ := direct_call pre stateA.toFrameState 0xb341 0x400a
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0xf350 (by decide)) effect0.rip
  change (callEffect (fun _ => 0x10f350) 0x10b346 a).Holds a b at effect1
  have frameB := stateA.toFrameState.after_call pre ready1 effect1
  have src1 : b.regValue .rdx = stackPtr s-48 :=
    (effect1.agrees.read (n := 64) (r := 2) (by simp)).trans src0
  have dst1 : b.regValue .rdi = stackPtr s-344 :=
    (effect1.agrees.read (n := 64) (r := 7) (by simp)).trans dst0
  have length1 : b.regValue .rsi = 257 :=
    (effect1.agrees.read (n := 64) (r := 6) (by simp)).trans writes0.2.1
  have ret : (returnBoundary b).rip = 0x10b346 := (callEffect_stack effect1).1
  have basePre : CalleePre b boundary 0x10f350 0 257 168 :=
    empty_input_pre pre frameB effect1.rip dst1 (by decide) (by decide) (by decide)
      (by rw [length1]; decide) (by rw [ret]; exact inProgram_of_textOffset 0xb346 (by decide))
  have recodePre : P256.Proofs.Verifying.Combination.Naf.Pre b boundary := {
    toCalleePre := basePre
    outputLength := length1
    inputLength := (effect1.agrees.read (n := 64) (r := 1) (by simp)).trans writes0.2.2.1
    inputBits := (effect1.agrees.read (n := 64) (r := 8) (by simp)).trans writes0.2.2.2.1
    window := (effect1.agrees.read (n := 64) (r := 9) (by simp)).trans writes0.2.2.2.2.1
    sourceBounded := stack_buffer_bound pre (by decide) (by decide) src1
    sourceAllocated := stack_buffer_allocated pre frameB (by decide) (by decide) src1
    sourceOutput := by
      have bounds := stack_bounds pre.stack
      have slo : (b.regValue .rdx).toNat = (stackPtr s).toNat-48 := by
        rw [src1]
        exact stack_sub_toNat pre.stack (offset := 48) (by decide)
      have dlo : (b.regValue .rdi).toNat = (stackPtr s).toNat-344 := by
        rw [dst1]
        exact stack_sub_toNat pre.stack (offset := 344) (by decide)
      intro address hs hd
      change (b.regValue .rdx).toNat ≤ address ∧ address < (b.regValue .rdx).toNat+32 at hs
      change (b.regValue .rdi).toNat ≤ address ∧ address < (b.regValue .rdi).toNat+257 at hd
      rw [slo] at hs
      rw [dlo] at hd
      omega
    sourceStack := stack_buffer_stack pre frameB (by decide) src1
  }
  have sourceB : Nat256At b (b.regValue .rdx) n := by
    rw [src1]
    refine ⟨input.1, ?_⟩
    intro i hi
    exact (call_byte stateA.toFrameState effect1 (offset := 48) (len := 32)
      (by decide) (by decide) hi).trans ((congrArg (fun m : Ram => m[_]?) memory0).trans (input.2 i hi))
  have zeroesB : Bytes b.external (b.regValue .rdi) 257 (fun _ => 0) := by
    rw [dst1]
    intro i hi
    exact (call_byte stateA.toFrameState effect1 (offset := 344) (len := 257)
      (by decide) (by decide) hi).trans ((congrArg (fun m : Ram => m[_]?) memory0).trans (zeroes i hi))
  have cursorB : memLoad b.external cursor 64 = point+128 := by
    apply (cursor_read_of_frame pre ?_).trans stateA.cursorValue
    intro address ha
    apply effect1.agrees.memoryWriteFrame (call_writes pre stateA.toFrameState) address
    intro region hr hin
    have hr' : region = Stack.region s 536 := by simpa using hr
    exact ha _ (by simp [hr']) hin
  obtain ⟨w, result, lengthW, digitsW⟩ := P256.Proofs.Verifying.Combination.Naf.Machine.recode_correct recodePre sourceB zeroesB
  have work := stack_result_work_frame pre frameB result dst1 (by decide) (by decide) (by decide)
  have stateW : Memory s w cursor point :=
    ⟨frameB.after_result pre result work, (work_cursor_read pre work).trans cursorB⟩
  obtain ⟨n2, run2⟩ := result.execution
  refine ⟨n0+1+n2, w, (run0.trans run1).trans run2, stateW, result.rip.trans ret,
    (result.calleeSaved .rbx (by simp)).trans
      ((effect1.agrees.read (n := 64) (r := 3) (by simp)).trans
        (agrees0.read (n := 64) (r := 3) (by simp))), lengthW, ?_⟩
  intro i hi
  have h := digitsW i hi
  rw [dst1] at h
  exact h

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.RecodeCall
