import P256.Proofs.Common.Field.SquareRoot.Multiply.Prologue
import P256.Proofs.Sec1.SquareRoot.Square.Interface
import P256.Proofs.Program.Push
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field.SquareRoot.Multiply (prologueComponents pushAfter_external pushAfter_read_ne savedMemory)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field.SquareRoot

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_setup [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x11cba0 32 64 88) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11cbae ∧ stackPtr t = stackPtr s - 88 ∧
      t.external = savedMemory s ∧ AgreesExcept (prologueComponents s) s t := by
  let s1 := pushAfter s 5
  let s2 := pushAfter s1 15
  let s3 := pushAfter s2 14
  let s4 := pushAfter s3 13
  let s5 := pushAfter s4 12
  let s6 := pushAfter s5 3
  have f1 : AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s s1 :=
    AgreesExcept.afterStep_push s _ _ _
  have f2 : AgreesExcept [.reg 4, .mem (pushAddr s1) 8, .rip] s1 s2 :=
    AgreesExcept.afterStep_push s1 _ _ _
  have f3 : AgreesExcept [.reg 4, .mem (pushAddr s2) 8, .rip] s2 s3 :=
    AgreesExcept.afterStep_push s2 _ _ _
  have f4 : AgreesExcept [.reg 4, .mem (pushAddr s3) 8, .rip] s3 s4 :=
    AgreesExcept.afterStep_push s3 _ _ _
  have f5 : AgreesExcept [.reg 4, .mem (pushAddr s4) 8, .rip] s4 s5 :=
    AgreesExcept.afterStep_push s4 _ _ _
  have f6 : AgreesExcept [.reg 4, .mem (pushAddr s5) 8, .rip] s5 s6 :=
    AgreesExcept.afterStep_push s5 _ _ _
  obtain ⟨e1, r1, l1, i1, p1⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h) 5 0 0x1cba0
    (by simp) pre.rip (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨e2, r2, l2, i2, p2⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r1 l1 f1.grow 15 8 0x1cba1 p1 i1
    (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨e3, r3, l3, i3, p3⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r2 l2 (f1.trans f2).grow 14 16 0x1cba3 p2 i2
    (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨e4, r4, l4, i4, p4⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r3 l3 ((f1.trans f2).trans f3).grow 13 24 0x1cba5 p3 i3
    (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨e5, r5, l5, i5, p5⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r4 l4 (((f1.trans f2).trans f3).trans f4).grow 12 32 0x1cba7 p4 i4
    (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨e6, r6, l6, i6, p6⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r5 l5 ((((f1.trans f2).trans f3).trans f4).trans f5).grow 3 40 0x1cba9 p5 i5
    (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨t, e7, ready, effect⟩ :=
    (sub_r64_imm8_effect_step 0x11cbaa 0x48 0xec 0x28
      (by simp [RexWPrefix]) (by decide) (by decide)).advances r6
      (programText_slice (programLoaded_codeIn l6) 0x1cbaa _
        (by decide) (by decide +kernel)) i6
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1cbae (by decide)))
  have ext : t.external = s6.external := effect.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, (((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7,
    ready, ?_, effect.rip, ?_, ?_, ?_⟩
  · intro a b h
    rw [ext]
    exact l6 a b h
  · have he : stackPtr t = stackPtr s6 - 40 := effect.writes
    rw [he, p6, BitVec.sub_sub]
    rfl
  · rw [ext]
    simp only [s6, s5, s4, s3, s2, s1, pushAfter_external]
    simp only [pushAddr, pushAfter_rsp, BitVec.sub_sub]
    simp (disch := decide +kernel) only [pushAfter_read_ne]
    rfl
  · apply ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans effect.agrees).mono
    intro c hc
    simp only [subR64Imm8Effect_components, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((((((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;>
      simp [prologueComponents, s1, s2, s3, s4, s5, pushAddr,
        pushAfter_rsp, BitVec.sub_sub, gprNumber, rexB, modrmRm]

theorem prologue_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x11cba0 32 64 88)
    (length : s.regValue .rdx = 4) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11cbb8 ∧ stackPtr t = stackPtr s - 88 ∧
      t.external = savedMemory s ∧ AgreesExcept (prologueComponents s) s t := by
  obtain ⟨u, hu, ready, loaded, rip, rsp, mem, frame⟩ := stack_setup pre
  have left : (Operand.reg 2 : Operand 64).read u = 4 :=
    (frame.read (by simp [prologueComponents])).trans length
  have code := programLoaded_codeIn loaded
  obtain ⟨u1, h1, r1, e1⟩ :=
    (cmp_r64_imm8_effect_step 0x11cbae 0x48 0xfa 4
      (by simp [RexWPrefix]) (by decide) (by decide)).advances ready
      (programText_slice code 0x1cbae _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1cbb2 (by decide)))
  change (cmpR64Imm8Effect 0x11cbae 2 4 u).Holds u u1 at e1
  have m1 : u1.external = u.external := e1.agrees.external (by simp [Component.Covers])
  have z1 : (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = true := by
    have hz := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u1.RFLAGS).ZF =
      (cmpSpec ((Operand.reg 2 : Operand 64).read u) (4 : BitVec 64)).ZF at hz
    rw [left] at hz
    exact hz
  obtain ⟨u2, hs2, r2, e2'⟩ := jcc_rel32_effect_step 0x11cbb2 5 0x13b u1 r1
    (programText_slice (code.of_external_eq m1) 0x1cbb2 _
      (by decide) (by decide +kernel)) ⟨e1.rip, fun _ => by decide⟩
  have e2 := jccEffect_not_taken (show condHolds 5 (StatusFlags.ofRFLAGS u1.RFLAGS) = false by
    change (!(StatusFlags.ofRFLAGS u1.RFLAGS).ZF) = false
    rw [z1]; rfl) e2'
  have h2 := Advances.of_step (boundary := boundary) hs2 (.inl
    (e2.rip ▸ boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1cbb8 (by decide))))
  have f2 := e1.agrees.trans e2.agrees
  have m2 : u2.external = u.external := f2.external
    (by simp [cmpR64Imm8Effect, nopEffect, Effect.components, Component.Covers])
  refine ⟨u2, (hu.trans h1).trans h2, r2, ?_, e2.rip,
    (f2.read (n := 64) (r := 4) (by simp [cmpR64Imm8Effect, nopEffect, Effect.components])).trans rsp,
    m2.trans mem, ?_⟩
  · intro a b h
    rw [m2]
    exact loaded a b h
  · exact (frame.trans f2).mono
      (by simp [prologueComponents, cmpR64Imm8Effect, nopEffect, Effect.components])

end P256.Proofs.Sec1.SquareRoot.Square.Wide
