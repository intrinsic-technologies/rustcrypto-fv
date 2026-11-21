import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality.Frame
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Model
import P256.Proofs.Generate.Zero.Prefix
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.SecretKeyFromBytes.Choice
import X86Proofs.Instructions.Pop.Triple
import P256.Proofs.Field.Jump

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.Generate.Zero
open P256.Proofs.SecretKeyFromBytes

theorem field_equal_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x1143f0 32 32 32)
    (left : MontgomeryAt s (s.regValue .rdi) x)
    (right : MontgomeryAt s (s.regValue .rsi) y) :
    ∃ t, CalleeResult s t boundary 32 32 ∧
      (t.regValue .rax).setWidth 8 = if x = y then 1 else 0 := by
  obtain ⟨a, state⟩ := prefix_correct (offset := 0x143f0) (disp := 0x4e6d) pre
    (by constructor <;> decide +kernel) left.2 right.2
  have av : (a.regValue .rax).setWidth 8 = if x = y then 1 else 0 := by
    simpa only [montgomery_injective left.1 right.1] using state.value
  obtain ⟨b, runB, readyB, agreesB, ripB, valueB⟩ := mask_arguments boundary 0x114403 state.ready
    (programText_slice (programLoaded_codeIn state.loaded) 0x14403 maskBytes
      (by decide) (by decide +kernel)) state.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14405 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14408 (by decide)))
  have ab : AgreesExcept (clobbers s) s b :=
    (state.agrees.trans agreesB).mono (by simp [clobbers, prefixClobbers])
  have spB : stackPtr b = stackPtr s-8 :=
    (agreesB.read (n := 64) (r := 4) (by simp)).trans state.rsp
  have diB : b.regValue .rdi = if x=y then 1 else 0 := by
    rw [valueB, av]
    split <;> rfl
  obtain ⟨c, runC, readyC, ec⟩ :=
    (pop_r64_effect_step 0x114408 0x58 (by decide) (by decide)).advances readyB
      (programText_slice (programLoaded_codeIn (loaded pre ab)) 0x14408 [0x58]
        (by decide) (by decide +kernel))
      ⟨ripB, by
        rw [spB]
        exact readable_of_grow (stack_sub_readable pre.stack
          (offset := 8) (len := 8) (by decide) (by decide)) ab.grow⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14409 (by decide)))
  change (popR64Effect 0x114408 1 0 b).Holds b c at ec
  have ac : AgreesExcept (clobbers s) s c :=
    (ab.trans ec.agrees).mono (by simp [clobbers, prefixClobbers])
  have spC : stackPtr c = stackPtr s := by
    have h : stackPtr c = stackPtr b + 8 := ec.writes.2
    rw [h, spB, BitVec.sub_add_cancel]
  obtain ⟨d, runD, readyD, ed⟩ :=
    (jmp_rel32_effect_step 0x114409 0x4c62 (by decide +kernel)).advances readyC
      (programText_slice (programLoaded_codeIn (loaded pre ac)) 0x14409 _
        (by decide) (by decide +kernel)) ec.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19070 (by decide)))
  have gd : AgreesExcept [.rip] c d := ed.agrees
  have ad : AgreesExcept (clobbers s) s d := (ac.trans gd).mono (by simp [clobbers, prefixClobbers])
  have spD : stackPtr d = stackPtr s :=
    (gd.read (n := 64) (r := 4) (by simp)).trans spC
  have topD : stackTop d = (returnBoundary s).rip := by
    change memLoad d.external (stackPtr d) 64 = memLoad s.external (stackPtr s) 64
    rw [spD]
    exact return_address ad
  have choicePre : ChoicePre d := by
    refine ⟨ed.rip, ?_, ?_, ?_, ?_⟩
    · rw [spD]
      exact writable_of_grow (stack_sub_writable pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
        (offset := 1) (len := 1) (by decide) (by decide) (by decide)
        (by have h := Nat.mod_lt (stackPtr s-1).toNat (by decide : 0<4096); omega)) ad.grow
    · rw [spD]
      exact readable_of_grow
        (by simpa only [BitVec.sub_zero] using (stack_sub_readable pre.stack
          (offset := 0) (len := 8) (by decide) (by decide))) ad.grow
    · rw [topD]
      exact inProgram_low pre.returnInProgram
    · rw [spD]
      intro i hi j hj eq
      apply pre.avoids (Stack.region s 32) (by simp) _
        (ScalarFrame.stack_contains pre (offset := 1) (len := 1) (by decide) (by decide) ⟨i, hi, rfl⟩)
      left
      change InProgram (stackPtr s - 1 + BitVec.ofNat 64 i)
      rw [eq]
      have h := inProgram_of_textOffset (0x19070+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨t, runT, readyT, et⟩ := choice_correct readyD (choice_code_loaded (loaded pre ad)) choicePre (by
    intro q member
    apply boundary_ne_program pre.outerBoundary
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact inProgram_of_textOffset 0x19074 (by decide)
    · exact inProgram_of_textOffset 0x19078 (by decide)
    · exact inProgram_of_textOffset 0x1907c (by decide)
    · exact inProgram_of_textOffset 0x19080 (by decide)
    · rw [topD]; exact pre.returnInProgram)
  have finalAgrees : AgreesExcept (clobbers s) s t :=
    (ad.trans et.agrees).mono (by simp [clobbers, prefixClobbers, spD])
  obtain ⟨n, runA⟩ := state.execution
  refine ⟨t, ⟨⟨_, (((runA.trans runB).trans runC).trans runD).trans runT⟩,
    et.rip.trans topD, ?_, bindingsSupported_of_ready_agrees pre.bindingsSupported readyT finalAgrees,
    supportedMachine_of_ready_agrees pre.machine readyT finalAgrees, ?_,
    finalAgrees.directionFlagClear (by simp [clobbers, prefixClobbers]) pre.directionFlag,
    finalAgrees.mxcsr (by simp [clobbers, prefixClobbers]), finalAgrees.fcw (by simp [clobbers, prefixClobbers]),
    ?_, loaded pre finalAgrees, finalAgrees.grow⟩, ?_⟩
  · change stackPtr t = stackPtr s+8
    exact et.rsp.trans (congrArg (fun v : BitVec 64 => v+8) spD)
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact finalAgrees.read (n := 64) (r := 3) (by simp [clobbers, prefixClobbers])
    · exact finalAgrees.read (n := 64) (r := 5) (by simp [clobbers, prefixClobbers])
    · exact finalAgrees.read (n := 64) (r := 12) (by simp [clobbers, prefixClobbers])
    · exact finalAgrees.read (n := 64) (r := 13) (by simp [clobbers, prefixClobbers])
    · exact finalAgrees.read (n := 64) (r := 14) (by simp [clobbers, prefixClobbers])
    · exact finalAgrees.read (n := 64) (r := 15) (by simp [clobbers, prefixClobbers])
  · apply finalAgrees.memoryWriteFrame
    intro c hc a ha
    obtain ⟨r, hr, hin⟩ := writes pre c hc a ha
    have eq : r = Stack.region s 32 := by simpa using hr
    subst r
    exact ⟨Stack.region s 32, by simp, hin⟩
  · have diD : d.regValue .rdi = if x=y then 1 else 0 :=
      ((ec.agrees.trans gd).read (n := 64) (r := 7) (by simp)).trans diB
    have ax : t.regValue .rax = ((d.regValue .rdi).setWidth 8).setWidth 64 := et.rax
    rw [ax, diD]
    split <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality
