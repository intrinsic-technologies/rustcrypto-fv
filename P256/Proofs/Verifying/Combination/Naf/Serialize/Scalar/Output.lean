import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Setup
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Call
import P256.Proofs.Program.Copy
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.OutputFrame
import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Verifying.Combination.Naf.Output

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program
open P256.Proofs.Program (memcpy_pointer writable_of_grow stack_sub_writable8)

theorem copy_naf_output [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat}
    (pre : ScalarPre s boundary cursor point) (state : Memory s t cursor point)
    (rbx : t.regValue .rbx = s.regValue .rdi)
    (naf : NafAt t (stackPtr s - 352) n) (rip : t.RIP = 0x10b34b) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u cursor ∧ u.RIP = 0x10b35e ∧
      NafAt u (s.regValue .rdi) n ∧
      memLoad u.external cursor 64 = point+128 ∧ u.regValue .rbx = s.regValue .rdi := by
  obtain ⟨n0, t0, run0, ready0, _, effect0⟩ := outputSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xb34b outputSetupBytes
      (by decide) (by decide +kernel)) rip
  have agr0 : AgreesExcept [.reg 6, .reg 2, .reg 7, .rip] t t0 := effect0.agrees
  have mem0 := state.registers ready0 agr0 (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp) (by simp)
  have w0 : t0.regValue .rsi = stackPtr t + 8 ∧ t0.regValue .rdx = 272 ∧
      t0.regValue .rdi = t.regValue .rbx := effect0.writes
  have dst0 := w0.2.2.trans rbx
  have src0 : t0.regValue .rsi = stackPtr s - 352 :=
    w0.1.trans (stack_address state.rsp (offset := 8) (by decide))
  have naf0 : NafAt t0 (stackPtr s - 352) n := naf.of_copy
    (fun _ _ => by rw [agr0.external (by simp [Component.Covers])])
  have pointer := memcpy_pointer mem0.loaded
  have target : callMemPtr 0x10b358 (.rip 0xf919a) t0 = 0x11c930 := pointer.2
  have push : PushPre 0x10b358 6 t0 := by
    refine ⟨effect0.rip, ?_, ?_⟩
    · rw [call_address mem0.toFrameState]
      exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
        (offset := 368) (by decide) (by decide)) mem0.allocated
    · rw [call_address mem0.toFrameState]
      exact stack_code_apart pre
        (offset := 368) (codeOffset := 0xb358) (by decide) (by decide) (by decide)
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (call_m64_effect_step 0x10b358 (.rip 0xf919a) trivial rfl rfl).advances ready0
      (programText_slice (programLoaded_codeIn mem0.loaded) 0xb358 _ (by decide) (by decide +kernel))
      ⟨⟨push, by rw [target]; decide⟩, pointer.1⟩
      (by change callMemPtr 0x10b358 (.rip 0xf919a) t0 ≠ boundary.rip
          rw [target]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide)))
  have frame1 := mem0.toFrameState.after_call pre ready1 effect1
  have src1 : t1.regValue .rsi = stackPtr s - 352 :=
    (effect1.agrees.read (n := 64) (r := 6) (by simp)).trans src0
  have dst1 : t1.regValue .rdi = s.regValue .rdi :=
    (effect1.agrees.read (n := 64) (r := 7) (by simp)).trans dst0
  have ret : (returnBoundary t1).rip = 0x10b35e := (callEffect_stack effect1).1
  have cp := output_copy_pre pre frame1 (effect1.rip.trans target) src1 dst1
    (by rw [ret]; exact inProgram_of_textOffset 0xb35e (by decide))
  have count1 : t1.regValue .rdx = BitVec.ofNat 64 272 :=
    (effect1.agrees.read (n := 64) (r := 2) (by simp)).trans w0.2.1
  have naf1 : NafAt t1 (stackPtr s - 352) n :=
    naf0.of_copy (fun _ hi => call_byte mem0.toFrameState effect1 (by decide) (by decide) hi)
  obtain ⟨u, result, bytes, _⟩ := P256.Proofs.Program.memcpy_correct cp count1 (by decide)
  obtain ⟨n2, run2⟩ := result.execution
  have cursor1 : memLoad t1.external cursor 64 = point + 128 := by
    apply (cursor_read_of_frame pre ?_).trans mem0.cursorValue
    intro a ha
    apply effect1.agrees.memoryWriteFrame (call_writes pre mem0.toFrameState) a
    intro region hr hin
    have hr' : region = Stack.region s 536 := by simpa using hr
    exact ha _ (by simp [hr']) hin
  refine ⟨n0+1+n2, u, (run0.trans run1).trans run2,
    frame1.after_output_copy pre result dst1, result.rip.trans ret, ?_,
    (output_copy_cursor pre frame1 result dst1).trans cursor1, ?_⟩
  · apply naf1.of_copy
    intro i hi
    have h := bytes i hi
    rwa [dst1, src1] at h
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect1.agrees.read (n := 64) (r := 3) (by simp)).trans ((agr0.read (n := 64) (r := 3) (by simp)).trans rbx))

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
