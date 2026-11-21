import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.Pop
import P256.Proofs.Program.Code
import P256.Proofs.Program.State
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore [bindings : Bindings] {initial t : RamState}
    (stack : Stack.Valid initial 4104)
    (hb : MachineRamUnitStrideDecodable bindings t)
    (hm : SupportedIntegerMachineState bindings.processor t)
    (loaded : ProgramLoaded t) (direction : DirectionFlagUnset t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t=stackPtr initial-504)
    (saved : ∀ reg ∈ savedRegisters,
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64=initial.regValue reg.1)
    (returnAddress : memLoad t.external (stackPtr initial) 64=(returnBoundary initial).rip)
    (rip : t.RIP=0x106cdc) (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat<2^32) :
    ∃ u, Returns (returnBoundary initial) 8 t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧
      u.external=t.external ∧ u.regValue .rax=t.regValue .rax := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s0,h0,r0,e0⟩ := (add_r64_imm32_effect_step 0x106cdc 0x48 0xc4 456
    (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep hm hb)
    (programText_slice code 0x6cdc _ (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ce3 (by decide)))
  change (addR64Imm32Effect 0x106cdc 4 456 t).Holds t s0 at e0
  have m0 : s0.external=t.external := e0.agrees.external (by simp [Component.Covers])
  have sp0 : stackPtr s0=stackPtr initial-48 := by
    have h : stackPtr s0=stackPtr t+456 := e0.writes
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have readable (u : RamState) (memory : u.external=t.external) (off : Nat) (bound : off≤4104) :
      MemReadable u (stackPtr initial-BitVec.ofNat 64 off) 8 :=
    (readable_of_grow (stack_sub_readable stack bound (by omega)) grow).of_external_eq memory
  obtain ⟨s1,h1,r1,e1⟩ := (pop_register_effect_step 0x106ce3 3 (by decide)).advances r0
    (programText_slice (code.of_external_eq m0) 0x6ce3 _ (by decide) (by decide +kernel))
    ⟨e0.rip,by rw [sp0]; exact readable s0 m0 48 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ce4 (by decide)))
  have m1 : s1.external=t.external := (e1.agrees.external (by simp [Component.Covers])).trans m0
  have sp1 : stackPtr s1=stackPtr initial-40 := by
    have h : stackPtr s1=stackPtr s0+8 := e1.writes.2
    rw [h,sp0]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have v1 : s1.regValue .rbx=initial.regValue .rbx := by
    have h : s1.regValue .rbx=memLoad s0.external (stackPtr s0) 64 := e1.writes.1
    rw [h,sp0,m0]
    exact saved (.rbx,48) (by simp [savedRegisters])
  obtain ⟨s2,h2,r2,e2⟩ := (pop_register_effect_step 0x106ce4 12 (by decide)).advances r1
    (programText_slice (code.of_external_eq m1) 0x6ce4 _ (by decide) (by decide +kernel))
    ⟨e1.rip,by rw [sp1]; exact readable s1 m1 40 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ce6 (by decide)))
  have m2 : s2.external=t.external := (e2.agrees.external (by simp [Component.Covers])).trans m1
  have sp2 : stackPtr s2=stackPtr initial-32 := by
    have h : stackPtr s2=stackPtr s1+8 := e2.writes.2
    rw [h,sp1]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have v2 : s2.regValue .r12=initial.regValue .r12 := by
    have h : s2.regValue .r12=memLoad s1.external (stackPtr s1) 64 := e2.writes.1
    rw [h,sp1,m1]
    exact saved (.r12,40) (by simp [savedRegisters])
  obtain ⟨s3,h3,r3,e3⟩ := (pop_register_effect_step 0x106ce6 13 (by decide)).advances r2
    (programText_slice (code.of_external_eq m2) 0x6ce6 _ (by decide) (by decide +kernel))
    ⟨e2.rip,by rw [sp2]; exact readable s2 m2 32 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ce8 (by decide)))
  have m3 : s3.external=t.external := (e3.agrees.external (by simp [Component.Covers])).trans m2
  have sp3 : stackPtr s3=stackPtr initial-24 := by
    have h : stackPtr s3=stackPtr s2+8 := e3.writes.2
    rw [h,sp2]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have v3 : s3.regValue .r13=initial.regValue .r13 := by
    have h : s3.regValue .r13=memLoad s2.external (stackPtr s2) 64 := e3.writes.1
    rw [h,sp2,m2]
    exact saved (.r13,32) (by simp [savedRegisters])
  obtain ⟨s4,h4,r4,e4⟩ := (pop_register_effect_step 0x106ce8 14 (by decide)).advances r3
    (programText_slice (code.of_external_eq m3) 0x6ce8 _ (by decide) (by decide +kernel))
    ⟨e3.rip,by rw [sp3]; exact readable s3 m3 24 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cea (by decide)))
  have m4 : s4.external=t.external := (e4.agrees.external (by simp [Component.Covers])).trans m3
  have sp4 : stackPtr s4=stackPtr initial-16 := by
    have h : stackPtr s4=stackPtr s3+8 := e4.writes.2
    rw [h,sp3]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have v4 : s4.regValue .r14=initial.regValue .r14 := by
    have h : s4.regValue .r14=memLoad s3.external (stackPtr s3) 64 := e4.writes.1
    rw [h,sp3,m3]
    exact saved (.r14,24) (by simp [savedRegisters])
  obtain ⟨s5,h5,r5,e5⟩ := (pop_register_effect_step 0x106cea 15 (by decide)).advances r4
    (programText_slice (code.of_external_eq m4) 0x6cea _ (by decide) (by decide +kernel))
    ⟨e4.rip,by rw [sp4]; exact readable s4 m4 16 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cec (by decide)))
  have m5 : s5.external=t.external := (e5.agrees.external (by simp [Component.Covers])).trans m4
  have sp5 : stackPtr s5=stackPtr initial-8 := by
    have h : stackPtr s5=stackPtr s4+8 := e5.writes.2
    rw [h,sp4]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have v5 : s5.regValue .r15=initial.regValue .r15 := by
    have h : s5.regValue .r15=memLoad s4.external (stackPtr s4) 64 := e5.writes.1
    rw [h,sp4,m4]
    exact saved (.r15,16) (by simp [savedRegisters])
  obtain ⟨s6,h6,r6,e6⟩ := (pop_register_effect_step 0x106cec 5 (by decide)).advances r5
    (programText_slice (code.of_external_eq m5) 0x6cec _ (by decide) (by decide +kernel))
    ⟨e5.rip,by rw [sp5]; exact readable s5 m5 8 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ced (by decide)))
  have m6 : s6.external=t.external := (e6.agrees.external (by simp [Component.Covers])).trans m5
  have sp6 : stackPtr s6=stackPtr initial-0 := by
    have h : stackPtr s6=stackPtr s5+8 := e6.writes.2
    rw [h,sp5]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have v6 : s6.regValue .rbp=initial.regValue .rbp := by
    have h : s6.regValue .rbp=memLoad s5.external (stackPtr s5) 64 := e6.writes.1
    rw [h,sp5,m5]
    exact saved (.rbp,8) (by simp [savedRegisters])
  have sp : stackPtr s6=stackPtr initial := by simpa only [BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using sp6
  have top : stackTop s6=(returnBoundary initial).rip := by
    rw [stackTop,sp]
    change memLoad s6.external (stackPtr initial) 64=_
    rw [m6]; exact returnAddress
  obtain ⟨u,step,ready,e⟩ := ret_effect_step 0x106ced s6 r6
    (programText_slice (code.of_external_eq m6) 0x6ced _ (by decide) (by decide +kernel))
    ⟨⟨e6.rip,by rw [sp]; simpa only [BitVec.sub_zero] using readable s6 m6 0 (by decide)⟩,
      by rw [top]; exact low⟩
  have ret : Returns (returnBoundary initial) 1 s6 u := Returns.of_step step
    (e.rip.trans top) (by
      change stackPtr u=stackPtr initial+8
      have h : stackPtr u=stackPtr s6+8 := e.writes
      rw [h,sp])
  have frame := (((((((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e.agrees)
  refine ⟨u,((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).returns ret,supportedMachine_of_ready_agrees hm ready frame,
    bindingsSupported_of_ready_agrees hb ready frame,?_,
    frame.directionFlagClear (by simp) direction,frame.external (by simp [Component.Covers]),
    frame.read (n := 64) (r := 0) (by simp)⟩
  intro reg hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ((((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e.agrees).read (n := 64) (r := 3) (by simp)).trans v1
  · exact (e.agrees.read (n := 64) (r := 5) (by simp)).trans v6
  · exact (((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e.agrees).read (n := 64) (r := 12) (by simp)).trans v2
  · exact ((((e4.agrees.trans e5.agrees).trans e6.agrees).trans e.agrees).read (n := 64) (r := 13) (by simp)).trans v3
  · exact (((e5.agrees.trans e6.agrees).trans e.agrees).read (n := 64) (r := 14) (by simp)).trans v4
  · exact ((e6.agrees.trans e.agrees).read (n := 64) (r := 15) (by simp)).trans v5

end P256.Proofs.EcdhWrapper.Finish.Return
