import P256.Proofs.EcdhWrapper.Nonzero.Memory
import P256.Proofs.Generate.Zero.Correct

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

def zeroLayout : StackCallLayout 4104 32 32 32 :=
  ⟨512,336,264,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem zero_call [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {x : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x106912) (rsp : stackPtr s = stackPtr initial-504)
    (rdi : s.regValue .rdi = stackPtr initial-264)
    (rsi : s.regValue .rsi = stackPtr initial-336)
    (scalar : Nat256At s (stackPtr initial-264) x)
    (zero : Nat256At s (stackPtr initial-336) 0) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧ ReadyToStep u ∧
      u.RIP = 0x106917 ∧ stackPtr u = stackPtr initial-504 ∧
      (u.regValue .rax).setWidth 8 = (if x=0 then 1 else 0) ∧
      AgreesExcept (clobbers initial) s u := by
  obtain ⟨t,run,rt,lt,e,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside (readyToStep hm hb) loaded grow 504 0x6912 0xc9a9 rsp rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x132c0 (by decide))
  have push : pushAddr s = stackPtr initial-512 := by
    rw [pushAddr,rsp,BitVec.sub_sub]; rfl
  have st : stackPtr t = stackPtr initial-512 := e.writes.1.trans push
  have top : (returnBoundary t).rip = 0x106917 := (callEffect_stack e).1
  have ag : AgreesExcept [.reg 4,.mem (stackPtr initial-512) 8,.rip] s t := by
    simpa only [pushEffect_components,push] using e.agrees
  have di : t.regValue .rdi = stackPtr initial-264 :=
    (ag.read (n := 64) (r := 7) (by simp)).trans rdi
  have si : t.regValue .rsi = stackPtr initial-336 :=
    (ag.read (n := 64) (r := 6) (by simp)).trans rsi
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside zeroLayout (bindingsSupported_of_ready_agrees hb rt ag)
    (supportedMachine_of_ready_agrees hm rt ag) (ag.directionFlagClear (by simp) direction)
    lt (fun a ha => ag.grow a (grow a ha)) e.rip st si di
    (by rw [top]; exact inProgram_of_textOffset 0x6917 (by decide))
  have keep (off : Nat) (h : off=264 ∨ off=336) {v : Nat}
      (value : Nat256At s (stackPtr initial-BitVec.ofNat 64 off) v) :
      Nat256At t (stackPtr initial-BitVec.ofNat 64 off) v := by
    refine ⟨value.1,fun i hi => ?_⟩
    rw [ag.byte]
    · exact value.2 i hi
    · intro c hc cover
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl <;> try exact cover.elim
      obtain ⟨j,hj,eq⟩ := cover
      exact stack_sub_apart call.stackAvailable.1 (a := 512) (b := off)
        (by decide) (by rcases h with rfl | rfl <;> decide) (by decide)
        (by rcases h with rfl | rfl <;> decide)
        (.inl (by rcases h with rfl | rfl <;> decide)) j hj i hi eq.symm
  obtain ⟨u,result,value,gu,_⟩ := Generate.Zero.zero_correct pre
    (by rw [di]; exact keep 264 (.inl rfl) scalar)
    (by rw [si]; exact keep 336 (.inr rfl) zero)
  obtain ⟨fuel,ru⟩ := result.execution
  refine ⟨u,⟨1+fuel,run.trans ru⟩,readyToStep result.machine result.bindingsSupported,
    result.rip.trans top,?_,value,?_⟩
  · have h : stackPtr u = stackPtr t+8 := result.rsp
    rw [h,st]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · simp only [Generate.Zero.clobbers,Generate.Zero.prefixClobbers,st,BitVec.sub_sub,
      BitVec.reduceAdd] at gu
    exact (ag.trans gu).mono (by simp [clobbers])

end P256.Proofs.EcdhWrapper.Nonzero
