import P256.Proofs.Field.Subtract.Loads
import P256.Proofs.Field.Subtract.Low
import P256.Proofs.Field.Subtract.Middle
import P256.Proofs.Field.Subtract.High
import P256.Proofs.Field.Subtract.Top
import P256.Proofs.Field.Subtract.Correction

set_option autoImplicit false

namespace P256.Proofs.Field.Subtract

open P256.Spec.Program.Routines P256.Spec P256.Spec.Program P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Field.Montgomery.Reduction (BorrowSlotPre)

def bodyClobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 8, .reg 9, .reg 10, .reg 11, .reg 14, .flags, .rip]

def bodyComponents (s : RamState) : List Component :=
  bodyClobbers ++ [.mem (stackPtr s) 8]

structure BodyPre (s : RamState) : Prop where
  rip : s.RIP = 0x113f24
  left : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8
  right : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 2 : Operand 64).read s + i) 8
  scratch : MemWritable s (stackPtr s) 8
  avoids : ∀ a, (Component.mem (stackPtr s) 8).Covers a → ¬ InProgram a

def BodyTrace (s t : RamState) : Prop :=
  ∃ s1 s2 s3 s4 s5,
    (loadLimbsEffect s).Holds s s1 ∧
    (borrowLowEffect s1).Holds s1 s2 ∧
    (borrowMiddleEffect s2).Holds s2 s3 ∧
    (borrowHighEffect s3).Holds s3 s4 ∧
    (borrowTopEffect s4).Holds s4 s5 ∧
    (correctionEffect s5 ⟨s5.regValue .rax, s5.regValue .rdx, s5.regValue .r8, s5.regValue .r10⟩ (s5.regValue .rcx)).Holds s5 t

theorem body_loaded {s t : RamState} (pre : BodyPre s)
    (frame : AgreesExcept (bodyComponents s) s t) (loaded : ProgramLoaded s) :
    ProgramLoaded t := by
  intro address byte hf
  rw [frame.memory address]
  · exact loaded address byte hf
  · intro c hc hv
    simp only [bodyComponents, bodyClobbers, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact hv.elim
    exact pre.avoids _ hv ⟨byte, hf⟩

theorem body_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s) (pre : BodyPre s) :
    ∃ t, (∃ fuel, Advances boundary fuel s t) ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11403d ∧ AgreesExcept (bodyComponents s) s t ∧ BodyTrace s t := by
  have pre1 : LoadLimbsPre s := by
    exact ⟨pre.rip, pre.left, pre.right⟩
  obtain ⟨n1, s1, run1, ready1, _, e1⟩ :=
    load_limbs_correct boundary hout s ready
      (programText_slice (programLoaded_codeIn loaded) 0x13f24 loadLimbsBytes
        (by decide +kernel) (by decide +kernel)) pre1
  have frame1 : AgreesExcept (bodyComponents s) s s1 := by
    apply (e1.agrees).mono
    simp [bodyComponents, bodyClobbers, loadLimbsEffect, Effect.components]
  have loaded1 := body_loaded pre frame1 loaded
  have sp1 : stackPtr s1 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s1 = (Operand.reg 4 : Operand 64).read s
    exact frame1.read (by simp [bodyComponents, bodyClobbers])
  have writable1 : MemWritable s1 (stackPtr s) 8 :=
    MemWritable.of_holds e1 pre.scratch
  have pre2 : BorrowSlotPre 0x113f42 s1 := by
    refine ⟨e1.rip, ?_, ?_⟩
    · rw [sp1]
      exact writable1
    · simpa only [sp1] using pre.avoids
  obtain ⟨n2, s2, run2, ready2, _, e2⟩ :=
    borrow_low_correct boundary hout s1 ready1
      (programText_slice (programLoaded_codeIn loaded1) 0x13f42 borrowLowBytes
        (by decide +kernel) (by decide +kernel)) pre2
  have frame2 : AgreesExcept (bodyComponents s) s s2 := by
    apply (frame1.trans e2.agrees).mono
    simp [bodyComponents, bodyClobbers, borrowLowEffect, Effect.components, sp1]
  have loaded2 := body_loaded pre frame2 loaded
  have sp2 : stackPtr s2 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s2 = (Operand.reg 4 : Operand 64).read s
    exact frame2.read (by simp [bodyComponents, bodyClobbers])
  have writable2 : MemWritable s2 (stackPtr s) 8 :=
    MemWritable.of_holds e2 writable1
  have pre3 : BorrowSlotPre 0x113f6e s2 := by
    refine ⟨e2.rip, ?_, ?_⟩
    · rw [sp2]
      exact writable2
    · simpa only [sp2] using pre.avoids
  obtain ⟨n3, s3, run3, ready3, _, e3⟩ :=
    borrow_middle_correct boundary hout s2 ready2
      (programText_slice (programLoaded_codeIn loaded2) 0x13f6e borrowMiddleBytes
        (by decide +kernel) (by decide +kernel)) pre3
  have frame3 : AgreesExcept (bodyComponents s) s s3 := by
    apply (frame2.trans e3.agrees).mono
    simp [bodyComponents, bodyClobbers, borrowMiddleEffect, Effect.components, sp2]
  have loaded3 := body_loaded pre frame3 loaded
  have sp3 : stackPtr s3 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s3 = (Operand.reg 4 : Operand 64).read s
    exact frame3.read (by simp [bodyComponents, bodyClobbers])
  have writable3 : MemWritable s3 (stackPtr s) 8 :=
    MemWritable.of_holds e3 writable2
  have pre4 : BorrowSlotPre 0x113f9b s3 := by
    refine ⟨e3.rip, ?_, ?_⟩
    · rw [sp3]
      exact writable3
    · simpa only [sp3] using pre.avoids
  obtain ⟨n4, s4, run4, ready4, _, e4⟩ :=
    borrow_high_correct boundary hout s3 ready3
      (programText_slice (programLoaded_codeIn loaded3) 0x13f9b borrowHighBytes
        (by decide +kernel) (by decide +kernel)) pre4
  have frame4 : AgreesExcept (bodyComponents s) s s4 := by
    apply (frame3.trans e4.agrees).mono
    simp [bodyComponents, bodyClobbers, borrowHighEffect, Effect.components, sp3]
  have loaded4 := body_loaded pre frame4 loaded
  have sp4 : stackPtr s4 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s4 = (Operand.reg 4 : Operand 64).read s
    exact frame4.read (by simp [bodyComponents, bodyClobbers])
  have writable4 : MemWritable s4 (stackPtr s) 8 :=
    MemWritable.of_holds e4 writable3
  have pre5 : BorrowSlotPre 0x113fcc s4 := by
    refine ⟨e4.rip, ?_, ?_⟩
    · rw [sp4]
      exact writable4
    · simpa only [sp4] using pre.avoids
  obtain ⟨n5, s5, run5, ready5, _, e5⟩ :=
    borrow_top_correct boundary hout s4 ready4
      (programText_slice (programLoaded_codeIn loaded4) 0x13fcc borrowTopBytes
        (by decide +kernel) (by decide +kernel)) pre5
  have frame5 : AgreesExcept (bodyComponents s) s s5 := by
    apply (frame4.trans e5.agrees).mono
    simp [bodyComponents, bodyClobbers, borrowTopEffect, Effect.components, sp4]
  have loaded5 := body_loaded pre frame5 loaded
  have sp5 : stackPtr s5 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s5 = (Operand.reg 4 : Operand 64).read s
    exact frame5.read (by simp [bodyComponents, bodyClobbers])
  have writable5 : MemWritable s5 (stackPtr s) 8 :=
    MemWritable.of_holds e5 writable4
  have last : CorrectionPre s5
      ⟨s5.regValue .rax, s5.regValue .rdx, s5.regValue .r8, s5.regValue .r10⟩
      (s5.regValue .rcx) := ⟨e5.rip, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨s6, run6, ready6, loaded6, e6⟩ := correction_correct last ready5 loaded5 hout
  have frame6 : AgreesExcept (bodyComponents s) s s6 := by
    apply (frame5.trans e6.agrees).mono
    simp [bodyComponents, bodyClobbers, correctionEffect, Effect.components]
  refine ⟨s6, ⟨n1 + n2 + n3 + n4 + n5 + 14, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6)⟩, ready6, loaded6, e6.rip, frame6, ?_⟩
  exact ⟨s1, s2, s3, s4, s5, e1, e2, e3, e4, e5, e6⟩

end P256.Proofs.Field.Subtract
