import P256.Proofs.EcdhWrapper.Scalar.SelectArguments
import P256.Proofs.EcdhWrapper.Scalar.Call
import P256.Proofs.Scalar.Select
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

def selectLayout : StackCallLayout 4104 32 32 16 :=
  ⟨512,456,264,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

def selectComponents (initial : RamState) : List Component :=
  [.reg 5,.reg 14,.reg 6,.reg 7,.reg 2,.reg 1,.reg 4,
    .mem (stackPtr initial-512) 8,.rip]

theorem select_argument_choice {s u : RamState}
    (effect : (selectArgumentEffect s).Holds s u)
    (tag : s.external[stackPtr s+408]? = some 1) : (u.regValue .rcx).setWidth 8 = 1 := by
  have cx : u.regValue .rcx = (memLoad s.external (stackPtr s+408) 32).setWidth 64 :=
    effect.writes.2.2.2.2.2
  rw [cx,BitVec.setWidth_setWidth_of_le _ (by decide),
    Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)]
  have h := storedByte_memLoad s.external (stackPtr s+408) 0 (by decide : 0 < 8/8)
  have h' : memLoad s.external (stackPtr s+408) 8 =
      (s.external[stackPtr s+408]?.getD 0).toBitVec := by
    simpa [storedByte,memByte,PhysicalMemory.read] using congrArg UInt8.toBitVec h
  simpa only [tag,Option.getD_some,show (1 : UInt8).toBitVec = (1 : BitVec 8) by decide] using h'

theorem select_enter [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {value : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x1068b6) (rsp : stackPtr s = stackPtr initial-504)
    (rbx : s.regValue .rbx = stackPtr initial-128)
    (tag : s.external[stackPtr initial-96]? = some 1)
    (input : Nat256At s (stackPtr initial-128) value) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      CalleePre t (returnBoundary initial) 0x113260 32 32 16 ∧
      Nat256At t (t.regValue .rdx) value ∧ (t.regValue .rcx).setWidth 8 = 1 ∧
      stackPtr t = stackPtr initial-512 ∧ t.regValue .rdi = stackPtr initial-264 ∧
      t.regValue .rdx = stackPtr initial-128 ∧ t.regValue .r14 = stackPtr initial-264 ∧
      (t.regValue .rbp).setWidth 8 = 1 ∧ (returnBoundary t).rip = 0x1068d7 ∧
      AgreesExcept (selectComponents initial) s t := by
  have tagAddress : stackPtr s+408 = stackPtr initial-96 := by
    rw [rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have readable : MemReadable s (stackPtr s+408) 4 := by
    rw [tagAddress]
    exact readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 96) (len := 4) (by decide) (by decide)) grow
  obtain ⟨fuel,u,run,ready,_,effect⟩ := select_arguments (returnBoundary initial) outside s
    (readyToStep hm hb) (select_arguments_loaded loaded) ⟨rip,readable⟩
  have ag : AgreesExcept [.reg 5,.reg 14,.reg 6,.reg 7,.reg 2,.reg 1,.rip] s u := by
    simpa [selectArgumentEffect,Effect.components,Write.component,Operand.component] using effect.agrees
  have memory := ag.external (by simp [Component.Covers])
  have rspU : stackPtr u = stackPtr initial-504 :=
    (ag.read (n := 64) (r := 4) (by simp)).trans rsp
  have inputU : u.regValue .rsi = stackPtr initial-456 := by
    have h : u.regValue .rsi = stackPtr s+48 := effect.writes.2.2.1
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have outputU : u.regValue .rdi = stackPtr initial-264 := by
    have h : u.regValue .rdi = stackPtr s+240 := effect.writes.2.2.2.1
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have sourceU : u.regValue .rdx = stackPtr initial-128 := effect.writes.2.2.2.2.1.trans rbx
  have r14U : u.regValue .r14 = stackPtr initial-264 := by
    have h : u.regValue .r14 = stackPtr s+240 := effect.writes.2.1
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have choiceU := select_argument_choice effect (tagAddress ▸ tag)
  have rbpU : (u.regValue .rbp).setWidth 8 = 1 := by
    have eq : u.regValue .rbp = u.regValue .rcx :=
      effect.writes.1.trans effect.writes.2.2.2.2.2.symm
    rw [eq]
    exact choiceU
  have loadedU : ProgramLoaded u := by simpa only [ProgramLoaded,memory] using loaded
  obtain ⟨t,step,readyT,loadedT,ce,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside ready loadedU (fun a ha => ag.grow a (grow a ha))
    504 0x68d2 0xc989 rspU effect.rip (by decide) (by decide) (by decide)
    (by decide +kernel) (inProgram_of_textOffset 0x13260 (by decide))
  have push : pushAddr u = stackPtr initial-512 := by
    rw [pushAddr,rspU,BitVec.sub_sub]
    rfl
  have ca : AgreesExcept [.reg 4,.mem (stackPtr initial-512) 8,.rip] u t := by
    simpa only [pushEffect_components,push] using ce.agrees
  have total : AgreesExcept (selectComponents initial) s t :=
    (ag.trans ca).mono (by simp [selectComponents])
  have rspT : stackPtr t = stackPtr initial-512 := ce.writes.1.trans push
  have inputT : t.regValue .rsi = stackPtr initial-456 :=
    (ca.read (n := 64) (r := 6) (by simp)).trans inputU
  have outputT : t.regValue .rdi = stackPtr initial-264 :=
    (ca.read (n := 64) (r := 7) (by simp)).trans outputU
  have sourceT : t.regValue .rdx = stackPtr initial-128 :=
    (ca.read (n := 64) (r := 2) (by simp)).trans sourceU
  have r14T : t.regValue .r14 = stackPtr initial-264 :=
    (ca.read (n := 64) (r := 14) (by simp)).trans r14U
  have rbpT : (t.regValue .rbp).setWidth 8 = 1 :=
    (congrArg (BitVec.setWidth 8) (ca.read (n := 64) (r := 5) (by simp))).trans rbpU
  have ret : (returnBoundary t).rip = 0x1068d7 := (callEffect_stack ce).1
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside selectLayout (bindingsSupported_of_ready_agrees hb readyT total)
    (supportedMachine_of_ready_agrees hm readyT total)
    (total.directionFlagClear (by simp [selectComponents]) direction) loadedT
    (fun a ha => total.grow a (grow a ha)) ce.rip rspT inputT outputT
    (by rw [ret]; exact inProgram_of_textOffset 0x68d7 (by decide))
  refine ⟨t,⟨fuel+1,run.trans step⟩,pre,?_,?_,rspT,outputT,sourceT,r14T,rbpT,ret,total⟩
  · rw [sourceT]
    refine ⟨input.1,fun i hi => ?_⟩
    rw [ca.byte]
    · rw [memory]
      exact input.2 i hi
    · intro c hc cover
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact cover.elim
      · obtain ⟨j,hj,eq⟩ := cover
        exact stack_sub_apart call.stackAvailable.1 (a := 512) (b := 128)
          (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm
      · exact cover.elim
  · exact (congrArg (BitVec.setWidth 8) (ca.read (n := 64) (r := 1) (by simp))).trans choiceU


theorem select_correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {value : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x1068b6) (rsp : stackPtr s = stackPtr initial-504)
    (rbx : s.regValue .rbx = stackPtr initial-128)
    (tag : s.external[stackPtr initial-96]? = some 1)
    (input : Nat256At s (stackPtr initial-128) value) :
    ∃ called t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      CalleeResult called t (returnBoundary initial) 32 16 ∧
      AgreesExcept (selectComponents initial) s called ∧
      stackPtr called = stackPtr initial-512 ∧
      called.regValue .rdi = stackPtr initial-264 ∧
      t.RIP = 0x1068d7 ∧ stackPtr t = stackPtr initial-504 ∧
      t.regValue .r14 = stackPtr initial-264 ∧ (t.regValue .rbp).setWidth 8 = 1 ∧
      Nat256At t (stackPtr initial-264) value := by
  obtain ⟨called,⟨prefixFuel,prefixRun⟩,pre,scalar,choice,stack,output,source,r14,rbp,ret,agrees⟩ :=
    select_enter call hb hm direction loaded grow outside rip rsp rbx tag input
  have readable : MemReadable called (called.regValue .rdx) 32 := by
    rw [source]
    exact readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 128) (len := 32) (by decide) (by decide))
      (fun a ha => agrees.grow a (grow a ha))
  have apart : RangeApart (stackPtr called-1) 1 (called.regValue .rdx) 32 := by
    rw [stack,source,BitVec.sub_sub]
    exact stack_sub_apart call.stackAvailable.1 (a := 513) (b := 128)
      (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
  obtain ⟨t,result,valueAt⟩ := P256.Proofs.Scalar.Select.correct pre readable apart scalar choice
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨called,t,⟨prefixFuel+fuel,prefixRun.trans run⟩,result,agrees,stack,output,
    result.rip.trans ret,?_,(result.calleeSaved .r14 (by simp)).trans r14,
    (congrArg (BitVec.setWidth 8) (result.calleeSaved .rbp (by simp))).trans rbp,?_⟩
  · have h : stackPtr t = stackPtr called+8 := result.rsp
    rw [h,stack]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · simpa only [output] using valueAt

end P256.Proofs.EcdhWrapper.Scalar
