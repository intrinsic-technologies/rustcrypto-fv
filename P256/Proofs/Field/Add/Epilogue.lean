import P256.Proofs.Field.Add.Entry
import P256.Proofs.Program.Pop
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Field.Add.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def epilogueComponents : List Component :=
  [.reg 4, .reg 3, .flags, .rip]

structure EpiloguePre [Bindings] (s t : RamState) (components : List Component) : Prop where
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = 0x113f15
  rsp : stackPtr t = stackPtr s - 16
  saved : (Operand.mem (stackPtr s - 8) : Operand 64).read t = s.regValue .rbx
  returnSlot : (Operand.mem (stackPtr s) : Operand 64).read t = (returnBoundary s).rip
  agrees : AgreesExcept components s t

structure EpilogueResult [bindings : Bindings] (s t u : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 3 t u
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
    (pre : CalleePre s boundary 0x113e10 32 32 16)
    (stage : EpiloguePre s t components)
    (unc : ∀ r ∈ ([5, 12, 13, 14, 15] : List (BitVec 5)), Component.reg r ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    ∃ u, EpilogueResult s t u boundary := by
  have code := programLoaded_codeIn stage.loaded
  have hRead (offset : Nat) (ho : offset ≤ 16) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack ho (by omega)) stage.agrees.grow
  have hc2 : CodeIn (codeRange 0x113f15 [0x48, 0x83, 0xc4, 0x08]) t :=
    programText_slice (code.of_external_eq (Eq.refl t.external)) 0x13f15 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (add_r64_imm8_effect_step 0x113f15 0x48 0xc4 8
      (by simp [RexWPrefix]) (by decide) (by decide)).advances stage.ready hc2 stage.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13f19 (by decide)))
  change (addR64Imm8Effect 0x113f15 4 8 t).Holds t t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans (Eq.refl t.external)
  have hsp2 : stackPtr t2 = stackPtr s - 8 := by
    have hw : stackPtr t2 = stackPtr t + 8 := he2.writes
    rw [hw, stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 8 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x113f19 (encodePopR64 3)) t2 :=
    programText_slice (code.of_external_eq hm2) 0x13f19 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (pop_register_effect_step 0x113f19 3 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13f1a (by decide)))
  change (popR64Effect 0x113f19 1 3 t2).Holds t2 t3 at he3
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr s - 0 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 3 : Operand 64).read t3 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr s - 8) 64 = _
    rw [hm2]
    exact stage.saved
  have hsp3' : stackPtr t3 = stackPtr s := by simpa using hsp3
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3']
    simpa using (hRead 0 (by decide)).of_external_eq hm3
  have htop3 : stackTop t3 = (returnBoundary s).rip := by
    rw [stackTop, hsp3']
    change memLoad t3.external (stackPtr s) 64 = _
    rw [hm3]
    exact stage.returnSlot
  have hc9 : CodeIn (codeRange 0x113f1a [0xc3]) t3 :=
    programText_slice (code.of_external_eq hm3) 0x13f1a _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, ha9, hr9, he9⟩ := (ret_effect_step 0x113f1a).advances hr3 hc9
    ⟨⟨he3.rip, hread3⟩, htop3 ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t3 ≠ boundary.rip
        rw [htop3]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm9 : u.external = t.external :=
    (he9.agrees.external (by simp [Component.Covers])).trans hm3
  have hf' := (he2.agrees.trans he3.agrees).trans he9.agrees
  have hf := stage.agrees.trans hf'
  refine ⟨u, ⟨?_, hr9, ?_, he9.rip.trans htop3, ?_,
    bindingsSupported_of_ready_agrees pre.bindingsSupported hr9 hf,
    supportedMachine_of_ready_agrees pre.machine hr9 hf, ?_, ?_, ?_, ?_, hm9, ?_⟩⟩
  · exact (ha2.trans ha3).trans ha9
  · intro address byte hfetch
    rw [hm9]
    exact stage.loaded address byte hfetch
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t3 + 8 := he9.writes
    rw [hw, hsp3']
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (he9.agrees.read (n := 64) (r := 3) (by simp)).trans hv3
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
    · change (Operand.reg 14 : Operand 64).read u = (Operand.reg 14 : Operand 64).read s
      exact hf.read (by
        simp only [List.mem_append, not_or]
        exact ⟨unc 14 (by simp), by simp⟩)
    · change (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read s
      exact hf.read (by
        simp only [List.mem_append, not_or]
        exact ⟨unc 15 (by simp), by simp⟩)
  · exact hf.directionFlagClear (by simpa using hdf) pre.directionFlag
  · exact hf.mxcsr (by simpa using hmxcsr)
  · exact hf.fcw (by simpa using hfcw)
  · exact hf'.mono (by simp [epilogueComponents])

end P256.Proofs.Field.Add.Return
