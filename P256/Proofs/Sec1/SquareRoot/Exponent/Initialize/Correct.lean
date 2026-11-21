import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.WindowExecution
import P256.Proofs.Sec1.SquareRoot.Exponent.Window

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ t fuel, Advances boundary fuel s t ∧ ExponentLoopState s t x 64 := by
  obtain ⟨t,fuel,run,state⟩ := initialize_window_ready ctx
  obtain ⟨u,window,frame,rip,bp,r14,bx,r13,r15,r11,r12,memory⟩ := initialize_window ctx state
  have output : exponentWordAt u (exponentFrameBase s+0x2a0) (s.regValue .rdi) := by
    change memLoad u.external _ 64=_
    rw [memory]
    exact (setupMemory_output s t.external).trans state.frame.outputPointer
  have fullFrame := ExponentFrame.of_scalarFrame frame output
  have bytes {off : Nat} (lo : 824≤off) (hi : off<1368) :
      u.external[exponentFrameBase s+BitVec.ofNat 64 off]?=
        t.external[exponentFrameBase s+BitVec.ofNat 64 off]? := by
    rw [memory]
    exact setupMemory_byte s t.external lo hi
  have constants : ExponentConstants s u x := by
    refine ⟨fullFrame.input_residue ctx,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i hi
      apply (state.table i hi).of_bytes_eq
      intro j hj
      simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
        bytes (off := 824+32*i+j) (by omega) (by omega)
    · refine ⟨state.exponent.1,?_⟩
      intro j hj
      have h := bytes (off := 1336+j) (by omega) (by omega)
      simp only [BitVec.ofNat_add,← BitVec.add_assoc] at h
      exact h.trans (state.exponent.2 j hj)
    · change memLoad u.external _ 32=_
      rw [memory]
      exact setupMemory_window s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_modulus0 s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_modulus1 s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_modulus2 s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_modulus3 s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_firstWindow s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_parameter s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_firstWord s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_inverse s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact setupMemory_mask s t.external
    · change memLoad u.external _ 64=_
      rw [memory]
      exact (setupMemory_negativeInverse s t.external).trans state.negativeInverse
  have savedWord : exponentWordAt u (exponentFrameBase s+0x2c0) 3 := by
    change memLoad u.external _ 64=_
    rw [memory]
    exact setupMemory_word s t.external
  have accumulator : Field.MontgomeryAt u (exponentFrameBase s+0x30) 1 := by
    have one := parameters_one ctx.residue.2
    apply Field.montgomeryAt_of_memLoad_limbs one.1
    · have h := ScalarFrame.stack_readable (frameOffset := 1416) ctx.toCalleePre frame
        (offset := 48) (len := 32) (by decide) (by decide)
      have sp : stackPtr u=exponentFrameBase s := frame.rsp
      rw [sp] at h
      exact h.mem
    · intro j hj
      have h := one.memLoad_limb j hj
      change memLoad s.external ((s.regValue .rsi+32)+32+BitVec.ofNat 64 (8*j)) 64=_ at h
      have addr : ((s.regValue .rsi+32)+32+BitVec.ofNat 64 (8*j))=
          s.regValue .rsi+BitVec.ofNat 64 (64+8*j) := by
        rw [BitVec.add_assoc (s.regValue .rsi) 32 32]
        change (s.regValue .rsi+64#64)+BitVec.ofNat 64 (8*j)=_
        rw [BitVec.ofNat_add,BitVec.add_assoc]
      rw [addr] at h
      have copied := setupMemory_one s t.external hj
      rw [← memory] at copied
      have eq : memLoad u.external (exponentFrameBase s+0x30+BitVec.ofNat 64 (8*j)) 64=
          memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (64+8*j)) 64 := by
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using copied
      exact eq.trans h
  refine ⟨u,fuel+44,run.trans window,fullFrame,constants,rip,bp,savedWord,r14,bx,r13,r15,r11,r12,?_⟩
  simpa only [sqrtExponent_initial_prefix,Nat.pow_zero,
    show 1%P256.Spec.Operations.domain.p=1 from by decide +kernel] using accumulator

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
