import P256.Proofs.Field.Subtract.Entry
import P256.Proofs.Program.Pop
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Field.Subtract.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def epilogueComponents : List Component :=
  [.reg 4, .reg 3, .reg 14, .flags, .rip]

structure EpiloguePre [Bindings] (s t : RamState) (components : List Component) : Prop where
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = 0x11404c
  rsp : stackPtr t = stackPtr s - 24
  saved : (Operand.mem (stackPtr s - 16) : Operand 64).read t = s.regValue .rbx
  saved14 : (Operand.mem (stackPtr s - 8) : Operand 64).read t = s.regValue .r14
  returnSlot : (Operand.mem (stackPtr s) : Operand 64).read t = (returnBoundary s).rip
  agrees : AgreesExcept components s t

structure EpilogueResult [bindings : Bindings] (s t u : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 4 t u
  ready : ReadyToStep u
  loaded : ProgramLoaded u
  rip : u.RIP = (returnBoundary s).rip
  rsp : stackPtr u = (returnBoundary s).rsp
  bindingsSupported : MachineRamUnitStrideDecodable bindings u
  machine : SupportedIntegerMachineState bindings.processor u
  calleeSaved : CalleeSavedRegistersUnchanged s u
  directionFlag : DirectionFlagUnset u
  mxcsr : u.MXCSR = s.MXCSR
  fp87 : u.FP87_Control = s.FP87_Control
  external : u.external = t.external
  agrees : AgreesExcept epilogueComponents t u

theorem epilogue_correct [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {components : List Component}
    (pre : CalleePre s boundary 0x113f20 32 32 24)
    (stage : EpiloguePre s t components)
    (unc : ∀ r ∈ ([5, 12, 13, 15] : List (BitVec 5)), Component.reg r ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    ∃ u, EpilogueResult s t u boundary := by
  have code := programLoaded_codeIn stage.loaded
  have hRead (offset : Nat) (ho : offset ≤ 24) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack ho (by omega)) stage.agrees.grow
  have hc2 : CodeIn (codeRange 0x11404c [0x48, 0x83, 0xc4, 0x08]) t :=
    programText_slice (code.of_external_eq (Eq.refl t.external)) 0x1404c _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (add_r64_imm8_effect_step 0x11404c 0x48 0xc4 8
      (by simp [RexWPrefix]) (by decide) (by decide)).advances stage.ready hc2 stage.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14050 (by decide)))
  change (addR64Imm8Effect 0x11404c 4 8 t).Holds t t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans (Eq.refl t.external)
  have hsp2 : stackPtr t2 = stackPtr s - 16 := by
    have hw : stackPtr t2 = stackPtr t + 8 := he2.writes
    rw [hw, stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 16 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x114050 (encodePopR64 3)) t2 :=
    programText_slice (code.of_external_eq hm2) 0x14050 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (pop_register_effect_step 0x114050 3 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14051 (by decide)))
  change (popR64Effect 0x114050 1 3 t2).Holds t2 t3 at he3
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr s - 8 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 3 : Operand 64).read t3 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr s - 16) 64 = _
    rw [hm2]
    exact stage.saved
  have hreadPop : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 8 (by decide)).of_external_eq hm3
  have hc4 : CodeIn (codeRange 0x114051 (encodePopR64 14)) t3 :=
    programText_slice (code.of_external_eq hm3) 0x14051 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (pop_register_effect_step 0x114051 14 (by decide)).advances hr3 hc4
      ⟨he3.rip, hreadPop⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14053 (by decide)))
  change (popR64Effect 0x114051 2 14 t3).Holds t3 t4 at he4
  have hm4 : t4.external = t.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hsp4 : stackPtr t4 = stackPtr s := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := he4.writes.2
    rw [hw, hsp3]
    simp only [BitVec.sub_add_cancel]
  have hv4 : (Operand.reg 14 : Operand 64).read t4 = s.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t4 =
        (Operand.mem (stackPtr t3) : Operand 64).read t3 := he4.writes.1
    rw [hw, hsp3]
    change memLoad t3.external (stackPtr s - 8) 64 = _
    rw [hm3]
    exact stage.saved14
  have hsp3' : stackPtr t4 = stackPtr s := by simpa using hsp4
  have hread3 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp3']
    simpa using (hRead 0 (by decide)).of_external_eq hm4
  have htop3 : stackTop t4 = (returnBoundary s).rip := by
    rw [stackTop, hsp3']
    change memLoad t4.external (stackPtr s) 64 = _
    rw [hm4]
    exact stage.returnSlot
  have hc9 : CodeIn (codeRange 0x114053 [0xc3]) t4 :=
    programText_slice (code.of_external_eq hm4) 0x14053 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, ha9, hr9, he9⟩ := (ret_effect_step 0x114053).advances hr4 hc9
    ⟨⟨he4.rip, hread3⟩, htop3 ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t4 ≠ boundary.rip
        rw [htop3]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm9 : u.external = t.external :=
    (he9.agrees.external (by simp [Component.Covers])).trans hm4
  have hf' := ((he2.agrees.trans he3.agrees).trans he4.agrees).trans he9.agrees
  have hf := stage.agrees.trans hf'
  refine ⟨u, ⟨?_, hr9, ?_, he9.rip.trans htop3, ?_,
    bindingsSupported_of_ready_agrees pre.bindingsSupported hr9 hf,
    supportedMachine_of_ready_agrees pre.machine hr9 hf, ?_, ?_, ?_, ?_, hm9, ?_⟩⟩
  · exact ((ha2.trans ha3).trans ha4).trans ha9
  · intro address byte hfetch
    rw [hm9]
    exact stage.loaded address byte hfetch
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t4 + 8 := he9.writes
    rw [hw, hsp3']
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (he9.agrees.read (n := 64) (r := 3) (by simp)).trans
        ((he4.agrees.read (n := 64) (r := 3) (by simp)).trans hv3)
    · change (Operand.reg 5 : Operand 64).read u = (Operand.reg 5 : Operand 64).read s
      exact hf.read (by
        simp only [List.mem_append, not_or]
        exact ⟨unc 5 (by simp), by simp⟩)
    · change (Operand.reg 12 : Operand 64).read u = (Operand.reg 12 : Operand 64).read s
      exact hf.read (by
        simp only [List.mem_append, not_or]
        exact ⟨unc 12 (by simp), by simp⟩)
    · change (Operand.reg 13 : Operand 64).read u = (Operand.reg 13 : Operand 64).read s
      exact hf.read (by
        simp only [List.mem_append, not_or]
        exact ⟨unc 13 (by simp), by simp⟩)
    · exact (he9.agrees.read (n := 64) (r := 14) (by simp)).trans hv4
    · change (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read s
      exact hf.read (by
        simp only [List.mem_append, not_or]
        exact ⟨unc 15 (by simp), by simp⟩)
  · exact hf.directionFlagClear (by simpa using hdf) pre.directionFlag
  · exact hf.mxcsr (by simpa using hmxcsr)
  · exact hf.fcw (by simpa using hfcw)
  · exact hf'.mono (by simp [epilogueComponents])

end P256.Proofs.Field.Subtract.Return
