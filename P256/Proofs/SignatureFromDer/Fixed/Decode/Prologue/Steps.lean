import P256.Proofs.Program.Push
import P256.Proofs.Program.Interface
import P256.Proofs.Program.SavePair
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_setup [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x109aca ∧ stackPtr t = stackPtr s - 184 ∧
      t.external = P256.Proofs.Program.SavePair.savedMemory s ∧
      AgreesExcept (P256.Proofs.Program.SavePair.saveComponents s) s t := by
  obtain ⟨s1, a1, r1, l1, i1, p1, f1, m1⟩ :=
    P256.Proofs.Program.push_exists pre.stack
      (pre.avoids (Stack.region s 560) (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h) 14 0 0x9ac0
      (by simp) pre.rip (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  obtain ⟨s2, a2, r2, l2, i2, p2, f2, m2⟩ :=
    P256.Proofs.Program.push_exists pre.stack
      (pre.avoids (Stack.region s 560) (by simp)) pre.outerBoundary r1 l1 f1.grow 3 8 0x9ac2
      p1 i1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t, a3, ready, effect⟩ :=
    (sub_r64_imm32_effect_step 0x109ac3 0x48 0xec 168
      (by constructor <;> decide +kernel) rfl rfl).advances r2
      (programText_slice (programLoaded_codeIn l2) 0x9ac3 _
        (by decide +kernel) (by decide +kernel)) i2
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9aca (by decide +kernel)))
  have f3 : AgreesExcept [.reg 4, .flags, .rip] s2 t := effect.agrees
  have ext : t.external = s2.external := f3.external (by simp [Component.Covers])
  refine ⟨t, (a1.trans a2).trans a3, ready, ?_, effect.rip, ?_, ?_, ?_⟩
  · intro a b h
    rw [ext]
    exact l2 a b h
  · have hw : stackPtr t = stackPtr s2 - 168 := effect.writes
    rw [hw, p2, BitVec.sub_sub]
    rfl
  · have bx : (Operand.reg 3 : Operand 64).read s1 = s.regValue .rbx :=
      f1.read (by simp)
    rw [ext, m2, m1]
    change memStore (memStore s.external (stackPtr s - 8) (s.regValue .r14))
      (stackPtr s - 16) ((Operand.reg 3 : Operand 64).read s1) = _
    rw [bx]
    rfl
  · exact ((f1.trans f2).trans f3).mono (by simp [P256.Proofs.Program.SavePair.saveComponents])

theorem length_gate [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x109aca)
    (length : s.regValue .rdx = 64) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x109ada ∧
      t.regValue .rbx = s.regValue .rdi ∧ t.regValue .r14 = s.regValue .rsi ∧
      AgreesExcept [.reg 3, .reg 14, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_r64_effect_step 0x109aca 0x48 0xfb
      (by constructor <;> decide +kernel) rfl).advances ready
      (programText_slice code 0x9aca _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x9acd (by decide +kernel)))
  change (movR64R64Effect 0x109aca 3 7 s).Holds s s1 at e1
  have f1 : AgreesExcept [.reg 3, .rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have dx : s1.regValue .rdx = 64 := (f1.read (n := 64) (r := 2) (by simp)).trans length
  obtain ⟨s2, a2, r2, e2⟩ :=
    (cmp_r64_imm8_effect_step 0x109acd 0x48 0xfa 64
      (by constructor <;> decide +kernel) rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x9acd _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x9ad1 (by decide +kernel)))
  change (cmpR64Imm8Effect 0x109acd 2 64 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.flags, .rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have z2 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = true := by
    have hz := e2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = (cmpSpec (s1.regValue .rdx) (64 : BitVec 64)).ZF at hz
    rw [dx] at hz
    exact hz
  obtain ⟨s3, step3, r3, raw3⟩ := jcc_rel32_effect_step 0x109ad1 5 0x180 s2 r2
    (programText_slice (code.of_external_eq m2) 0x9ad1 _
      (by decide +kernel) (by decide +kernel)) ⟨e2.rip, fun _ => by decide +kernel⟩
  have e3 := jccEffect_not_taken (show condHolds 5 (StatusFlags.ofRFLAGS s2.RFLAGS) = false by
    change (!(StatusFlags.ofRFLAGS s2.RFLAGS).ZF) = false
    rw [z2]
    rfl) raw3
  have a3 : Advances boundary 1 s2 s3 := Advances.of_step step3 (.inl (by
    rw [e3.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x9ad7 (by decide +kernel))))
  have f3 : AgreesExcept [.rip] s2 s3 := e3.agrees
  have m3 := (f3.external (by simp [Component.Covers])).trans m2
  obtain ⟨t, a4, r4, e4⟩ :=
    (mov_r64_r64_effect_step 0x109ad7 0x49 0xf6
      (by simp [RexWPrefix]) rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0x9ad7 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x9ada (by decide +kernel)))
  change (movR64R64Effect 0x109ad7 14 6 s3).Holds s3 t at e4
  have f4 : AgreesExcept [.reg 14, .rip] s3 t := e4.agrees
  refine ⟨t, ((a1.trans a2).trans a3).trans a4, r4, e4.rip, ?_, ?_, ?_⟩
  · exact (((f2.trans f3).trans f4).read (n := 64) (r := 3) (by simp)).trans e1.writes
  · exact e4.writes.trans (((f1.trans f2).trans f3).read (n := 64) (r := 6) (by simp))
  · exact (((f1.trans f2).trans f3).trans f4).mono (by simp)

theorem length_reject [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x109aca)
    (length : s.regValue .rdx ≠ 64) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x109c57 ∧
      t.regValue .rbx = s.regValue .rdi ∧
      AgreesExcept [.reg 3, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_r64_effect_step 0x109aca 0x48 0xfb
      (by constructor <;> decide +kernel) rfl).advances ready
      (programText_slice code 0x9aca _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x9acd (by decide +kernel)))
  change (movR64R64Effect 0x109aca 3 7 s).Holds s s1 at e1
  have f1 : AgreesExcept [.reg 3, .rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have dx : s1.regValue .rdx ≠ 64 := by
    exact fun h => length ((f1.read (n := 64) (r := 2) (by simp)).symm.trans h)
  obtain ⟨s2, a2, r2, e2⟩ :=
    (cmp_r64_imm8_effect_step 0x109acd 0x48 0xfa 64
      (by constructor <;> decide +kernel) rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x9acd _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x9ad1 (by decide +kernel)))
  change (cmpR64Imm8Effect 0x109acd 2 64 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.flags, .rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have z2 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = false := by
    have hz := e2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = (cmpSpec (s1.regValue .rdx) (64 : BitVec 64)).ZF at hz
    apply hz.trans
    change (s1.regValue .rdx - 64 == (0 : BitVec 64)) = false
    apply beq_eq_false_iff_ne.mpr
    intro h
    exact dx ((BitVec.sub_eq_iff_eq_add.mp h).trans (BitVec.zero_add _))
  obtain ⟨s3, step3, r3, raw3⟩ := jcc_rel32_effect_step 0x109ad1 5 0x180 s2 r2
    (programText_slice (code.of_external_eq m2) 0x9ad1 _
      (by decide +kernel) (by decide +kernel)) ⟨e2.rip, fun _ => by decide +kernel⟩
  have e3 := jccEffect_taken (show condHolds 5 (StatusFlags.ofRFLAGS s2.RFLAGS) = true by
    change (!(StatusFlags.ofRFLAGS s2.RFLAGS).ZF) = true
    rw [z2]
    rfl) raw3
  have a3 : Advances boundary 1 s2 s3 := Advances.of_step step3 (.inl (by
    rw [e3.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x9c57 (by decide +kernel))))
  have f3 : AgreesExcept [.rip] s2 s3 := e3.agrees
  refine ⟨s3, (a1.trans a2).trans a3, r3, e3.rip, ?_, ?_⟩
  · exact ((f2.trans f3).read (n := 64) (r := 3) (by simp)).trans e1.writes
  · exact ((f1.trans f2).trans f3).mono (by simp)

end P256.Proofs.SignatureFromDer.Fixed.Decode
