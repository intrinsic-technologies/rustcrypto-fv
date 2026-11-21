import P256.Proofs.Generate.Wrapper.Tail.Output
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem restore [bindings : Bindings] {initial t : RamState} {input : ByteArray}
    (stack : Stack.Valid initial 4024) (state : OutputState initial t input)
    (rip : t.RIP = 0x106ede)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32) :
    ∃ u, Returns (returnBoundary initial) 5 t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧
      u.external = t.external ∧ u.regValue .rax = t.regValue .rax := by
  have code := programLoaded_codeIn state.loaded
  obtain ⟨a,ha,ra,ea⟩ := (add_r64_imm32_effect_step 0x106ede 0x48 0xc4 240
    (by simp [RexWPrefix]) (by decide) (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice code 0x6ede _ (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ee5 (by decide)))
  change (addR64Imm32Effect 0x106ede 4 240 t).Holds t a at ea
  have ma : a.external = t.external := ea.agrees.external (by simp [Component.Covers])
  have spa : stackPtr a = stackPtr initial-24 := by
    have h : stackPtr a = stackPtr t+240 := ea.writes
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have readable (u : RamState) (hm : u.external = t.external) (off : Nat) (ho : off ≤ 4024) :
      MemReadable u (stackPtr initial - BitVec.ofNat 64 off) 8 :=
    (readable_of_grow (stack_sub_readable stack ho (by omega)) state.allocated).of_external_eq hm
  obtain ⟨b,hb,rb,eb⟩ := (pop_register_effect_step 0x106ee5 3 (by decide)).advances ra
    (programText_slice (code.of_external_eq ma) 0x6ee5 _ (by decide) (by decide +kernel))
    ⟨ea.rip,by rw [spa]; exact readable a ma 24 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ee6 (by decide)))
  have mb : b.external = t.external :=
    (eb.agrees.external (by simp [Component.Covers])).trans ma
  have spb : stackPtr b = stackPtr initial-16 := by
    have h : stackPtr b = stackPtr a+8 := eb.writes.2
    rw [h,spa]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have savedb : b.regValue .rbx = initial.regValue .rbx := by
    have h : b.regValue .rbx = memLoad a.external (stackPtr a) 64 := eb.writes.1
    rw [h,spa,ma]
    exact state.savedRbx
  obtain ⟨c,hc,rc,ec⟩ := (pop_register_effect_step 0x106ee6 14 (by decide)).advances rb
    (programText_slice (code.of_external_eq mb) 0x6ee6 _ (by decide) (by decide +kernel))
    ⟨eb.rip,by rw [spb]; exact readable b mb 16 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ee8 (by decide)))
  have mc : c.external = t.external :=
    (ec.agrees.external (by simp [Component.Covers])).trans mb
  have spc : stackPtr c = stackPtr initial-8 := by
    have h : stackPtr c = stackPtr b+8 := ec.writes.2
    rw [h,spb]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have savedc : c.regValue .r14 = initial.regValue .r14 := by
    have h : c.regValue .r14 = memLoad b.external (stackPtr b) 64 := ec.writes.1
    rw [h,spb,mb]
    exact state.savedR14
  obtain ⟨d,hd,rd,ed⟩ := (pop_register_effect_step 0x106ee8 15 (by decide)).advances rc
    (programText_slice (code.of_external_eq mc) 0x6ee8 _ (by decide) (by decide +kernel))
    ⟨ec.rip,by rw [spc]; exact readable c mc 8 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6eea (by decide)))
  have md : d.external = t.external :=
    (ed.agrees.external (by simp [Component.Covers])).trans mc
  have spd : stackPtr d = stackPtr initial-0 := by
    have h : stackPtr d = stackPtr c+8 := ed.writes.2
    rw [h,spc]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have savedd : d.regValue .r15 = initial.regValue .r15 := by
    have h : d.regValue .r15 = memLoad c.external (stackPtr c) 64 := ed.writes.1
    rw [h,spc,mc]
    exact state.savedR15
  have spd' : stackPtr d = stackPtr initial := by simpa only [BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using spd
  have top : stackTop d = (returnBoundary initial).rip := by
    rw [stackTop,spd']
    change memLoad d.external (stackPtr initial) 64 = _
    rw [md]
    exact state.returnAddress
  obtain ⟨u,step,ready,effect⟩ := ret_effect_step 0x106eea d rd
    (programText_slice (code.of_external_eq md) 0x6eea _ (by decide) (by decide +kernel))
    ⟨⟨ed.rip,by rw [spd']; simpa only [BitVec.sub_zero] using readable d md 0 (by decide)⟩,
      by rw [top]; exact low⟩
  have ret : Returns (returnBoundary initial) 1 d u := Returns.of_step step
    (effect.rip.trans top) (by
      change stackPtr u = stackPtr initial+8
      have h : stackPtr u = stackPtr d+8 := effect.writes
      rw [h,spd'])
  have frame := (((ea.agrees.trans eb.agrees).trans ec.agrees).trans ed.agrees).trans effect.agrees
  refine ⟨u,(((ha.trans hb).trans hc).trans hd).returns ret,
    supportedMachine_of_ready_agrees state.machine ready frame,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready frame,?_,
    frame.directionFlagClear (by simp) state.directionFlag,
    frame.external (by simp [Component.Covers]),frame.read (n := 64) (r := 0) (by simp)⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (((ec.agrees.trans ed.agrees).trans effect.agrees).read (n := 64) (r := 3) (by simp)).trans savedb
  · exact (frame.read (n := 64) (r := 5) (by simp)).trans (state.otherRegisters .rbp (by simp))
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans (state.otherRegisters .r12 (by simp))
  · exact (frame.read (n := 64) (r := 13) (by simp)).trans (state.otherRegisters .r13 (by simp))
  · exact ((ed.agrees.trans effect.agrees).read (n := 64) (r := 14) (by simp)).trans savedc
  · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans savedd

end P256.Proofs.Generate.Wrapper.Finish
