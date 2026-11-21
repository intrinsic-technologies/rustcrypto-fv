import P256.Proofs.Scalar.Select.Memory
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Scalar.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113260 32 32 16)
    (agrees : AgreesExcept (clobbers s) s t)
    (ready : ReadyToStep t) (rip : t.RIP = 0x1132b6)
    (rsp : stackPtr t = stackPtr s - 1)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 32 16 ∧ u.external = t.external := by
  have code := programLoaded_codeIn (loaded_of_agrees pre agrees)
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (add_r64_imm8_effect_step 0x1132b6 0x48 0xc4 1
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice code 0x132b6 [0x48,0x83,0xc4,1] (by decide +kernel) (by decide +kernel))
      rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132ba (by decide)))
  change (addR64Imm8Effect 0x1132b6 4 1 t).Holds t a at effectA
  have memA : a.external = t.external := effectA.agrees.external (by simp [Component.Covers])
  have rspA : stackPtr a = stackPtr s := by
    have hw : stackPtr a = stackPtr t + 1 := effectA.writes
    rw [hw, rsp, BitVec.sub_add_cancel]
  have topA : stackTop a = (returnBoundary s).rip := by
    rw [stackTop, rspA]
    change memLoad a.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    rw [memA]
    exact return_address pre agrees
  have readableA : MemReadable a (stackPtr a) 8 := by
    rw [rspA]
    apply P256.Proofs.Program.readable_of_grow _ (agrees.trans effectA.agrees).grow
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using
      P256.Proofs.Program.stack_sub_readable pre.stack (offset := 0) (len := 8)
        (by decide) (by decide)
  obtain ⟨u, runU, readyU, effectU⟩ := (ret_effect_step 0x1132ba).advances readyA
    (programText_slice (code.of_external_eq memA) 0x132ba [0xc3] (by decide +kernel) (by decide +kernel))
    ⟨⟨effectA.rip, readableA⟩, topA ▸ P256.Proofs.Program.inProgram_low pre.returnInProgram⟩
    (by change stackTop a ≠ boundary.rip
        rw [topA]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have memU : u.external = t.external :=
    (effectU.agrees.external (by simp [Component.Covers])).trans memA
  have whole : AgreesExcept (clobbers s) s u :=
    ((agrees.trans effectA.agrees).trans effectU.agrees).mono (by simp [clobbers])
  obtain ⟨fuel, run⟩ := execution
  refine ⟨u, ⟨⟨fuel + 1 + 1, (run.trans runA).trans runU⟩,
    effectU.rip.trans topA, ?_,
    bindingsSupported_of_ready_agrees pre.bindingsSupported readyU whole,
    supportedMachine_of_ready_agrees pre.machine readyU whole, ?_,
    whole.directionFlagClear (by simp [clobbers]) pre.directionFlag,
    whole.mxcsr (by simp [clobbers]), whole.fcw (by simp [clobbers]),
    whole.memoryWriteFrame (writes_within pre), loaded_of_agrees pre whole, whole.grow⟩, memU⟩
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr a + 8 := effectU.writes
    rw [hw, rspA]
  · intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact whole.read (r := 3) (n := 64) (by simp [clobbers])
    · exact whole.read (r := 5) (n := 64) (by simp [clobbers])
    · exact whole.read (r := 12) (n := 64) (by simp [clobbers])
    · exact whole.read (r := 13) (n := 64) (by simp [clobbers])
    · exact whole.read (r := 14) (n := 64) (by simp [clobbers])
    · exact whole.read (r := 15) (n := 64) (by simp [clobbers])

end P256.Proofs.Scalar.Select
