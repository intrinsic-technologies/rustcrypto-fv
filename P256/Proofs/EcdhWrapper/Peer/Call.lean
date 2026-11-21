import P256.Proofs.EcdhWrapper.Peer.Arguments
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.State
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Sec1.EncodedPoint

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def layout : StackCallLayout 4104 65 80 3360 :=
  ⟨512,264,128,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

def callComponents (initial : RamState) : List Component :=
  [.reg 7,.reg 6,.reg 4,.mem (stackPtr initial-512) 8,.rip]

theorem enter [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106b70) (rsp : stackPtr s = stackPtr initial-504)
    (bytes : Sec1.EncodedPointAt s (stackPtr initial-264) peer) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      Sec1.AffineDecodePre t (returnBoundary initial) peer ∧
      stackPtr t = stackPtr initial-512 ∧ t.regValue .rdi = stackPtr initial-128 ∧
      (returnBoundary t).rip = 0x106b85 ∧ AgreesExcept (callComponents initial) s t := by
  obtain ⟨n,u,run,ready,_,effect⟩ := arguments (returnBoundary initial) outside s
    (readyToStep hm hb)
    (programText_slice (programLoaded_codeIn loaded) 0x6b70 argumentBytes
      (by decide) (by decide +kernel)) rip
  have ag : AgreesExcept [.reg 7,.reg 6,.rip] s u := by
    simpa [argumentEffect,Effect.components,Write.component,Operand.component] using effect.agrees
  have memory := ag.external (by simp [Component.Covers])
  have rspU : stackPtr u = stackPtr initial-504 :=
    (ag.read (n := 64) (r := 4) (by simp)).trans rsp
  have inputU : u.regValue .rsi = stackPtr initial-264 := by
    have h : u.regValue .rsi = stackPtr s+240 := effect.writes.2
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have outputU : u.regValue .rdi = stackPtr initial-128 := by
    have h : u.regValue .rdi = stackPtr s+376 := effect.writes.1
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have loadedU : ProgramLoaded u := by simpa only [ProgramLoaded,memory] using loaded
  obtain ⟨t,step,readyT,loadedT,ce,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside ready loadedU (fun a ha => ag.grow a (grow a ha))
    504 0x6b80 0x954b rspU effect.rip (by decide) (by decide) (by decide)
    (by decide +kernel) (inProgram_of_textOffset 0x100d0 (by decide))
  have push : pushAddr u = stackPtr initial-512 := by
    rw [pushAddr,rspU,BitVec.sub_sub]
    rfl
  have ca : AgreesExcept [.reg 4,.mem (stackPtr initial-512) 8,.rip] u t := by
    simpa only [pushEffect_components,push] using ce.agrees
  have total : AgreesExcept (callComponents initial) s t :=
    (ag.trans ca).mono (by simp [callComponents])
  have rspT : stackPtr t = stackPtr initial-512 := ce.writes.1.trans push
  have inputT : t.regValue .rsi = stackPtr initial-264 :=
    (ca.read (n := 64) (r := 6) (by simp)).trans inputU
  have outputT : t.regValue .rdi = stackPtr initial-128 :=
    (ca.read (n := 64) (r := 7) (by simp)).trans outputU
  have ret : (returnBoundary t).rip = 0x106b85 := (callEffect_stack ce).1
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside layout (bindingsSupported_of_ready_agrees hb readyT total)
    (supportedMachine_of_ready_agrees hm readyT total)
    (total.directionFlagClear (by simp [callComponents]) direction) loadedT
    (fun a ha => total.grow a (grow a ha)) ce.rip rspT inputT outputT
    (by rw [ret]; exact inProgram_of_textOffset 0x6b85 (by decide))
  refine ⟨t,⟨n+1,run.trans step⟩,⟨pre,?_⟩,rspT,outputT,ret,total⟩
  rw [inputT]
  refine ⟨bytes.1,fun i hi => ?_⟩
  rw [ca.byte]
  · rw [memory]
    exact bytes.2 i hi
  · intro c hc cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact cover.elim
    · obtain ⟨j,hj,eq⟩ := cover
      exact stack_sub_apart call.stackAvailable.1 (a := 512) (b := 264)
        (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm
    · exact cover.elim

end P256.Proofs.EcdhWrapper.Peer
