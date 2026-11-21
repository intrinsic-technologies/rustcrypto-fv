import P256.Proofs.Verifying.Wrapper.KeyCopied
import P256.Proofs.Verifying.Wrapper.KeyArguments
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.Call
import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def keyLayout : StackCallLayout 10280 65 80 3680 :=
  ⟨288,280,208,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

def keyCallComponents (initial : RamState) : List Component :=
  [.reg 7,.reg 6,.reg 2,.reg 4,.mem (stackPtr initial-288) 8,.rip]

theorem enter_key_decoder [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (state : KeyCopied initial s key)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, Sec1.DecodePre t (returnBoundary initial) key ∧
      t.regValue .rdi = stackPtr initial-208 ∧ stackPtr t = stackPtr initial-288 ∧
      (returnBoundary t).rip = 0x1030f8 ∧
      AgreesExcept (keyCallComponents initial) s t ∧
      ∃ fuel, Advances (returnBoundary initial) fuel s t := by
  obtain ⟨n,u,run,ready,_,effect⟩ := key_arguments (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x30e6 keyArgumentBytes
      (by decide) (by decide +kernel)) state.rip
  have ag : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] s u := by
    simpa only [keyArgumentEffect, Effect.components, Write.component, Operand.component,
      List.map, List.cons_append, List.nil_append] using effect.agrees
  have su := state.toReturnState.after_registers ready ag
    (by simp [Component.Covers]) (by simp) (by simp)
  have values : u.regValue .rdi = stackPtr s+72 ∧ u.regValue .rsi = stackPtr s ∧
      u.regValue .rdx = 65 := effect.writes
  have input : u.regValue .rsi = stackPtr initial-280 := values.2.1.trans state.rsp
  have output : u.regValue .rdi = stackPtr initial-208 := by
    rw [values.1,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨t,runT,readyT,loadedT,ce,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside ready su.loaded su.allocated 280 0x30f3 0xb3e8 su.rsp
    effect.rip (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0xe4e0 (by decide))
  have push : pushAddr u = stackPtr initial-288 := by
    rw [pushAddr,su.rsp,BitVec.sub_sub]
    rfl
  have ca : AgreesExcept [.reg 4,.mem (stackPtr initial-288) 8,.rip] u t := by
    simpa only [pushEffect_components,push] using ce.agrees
  have inputT : t.regValue .rsi = stackPtr initial-280 :=
    (ca.read (n := 64) (r := 6) (by simp)).trans input
  have outputT : t.regValue .rdi = stackPtr initial-208 :=
    (ca.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary t).rip = 0x1030f8 := (callEffect_stack ce).1
  have sp : stackPtr t = stackPtr initial-288 := ce.writes.1.trans push
  have ripT : t.RIP = 0x10e4e0 := ce.rip
  have child := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside keyLayout (bindingsSupported_of_ready_agrees su.bindingsSupported readyT ca)
    (supportedMachine_of_ready_agrees su.machine readyT ca)
    (ca.directionFlagClear (by simp) su.directionFlag) loadedT
    (fun a ha => ca.grow a (su.allocated a ha)) ripT sp inputT outputT
    (by rw [ret]; exact inProgram_of_textOffset 0x30f8 (by decide))
  have size : key.size = 65 := state.bytes.1
  have keyBytes : (registerRegion t .rsi key.size).HasBytes t.external key := by
    change (MemoryRegion.mk (t.regValue .rsi).toNat key.size).HasBytes t.external key
    rw [inputT,size]
    apply hasBytes_agrees_apart ca
    · intro a len member
      have eq : a = stackPtr initial-288 ∧ len = 8 := by simpa using member
      obtain ⟨rfl,rfl⟩ := eq
      exact stack_sub_apart (a := 288) (b := 280) (na := 8) (nb := 65)
        call.stackAvailable.1 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
    · rw [ag.external (by simp [Component.Covers])]
      simpa only [state.rsp] using state.bytes
  refine ⟨t,⟨?_,keyBytes,?_⟩,outputT,sp,ret,?_,⟨n+1,run.trans runT⟩⟩
  · simpa only [size] using (child : CalleePre t (returnBoundary initial) 0x10e4e0 65 80 3680)
  · rw [size]
    exact (ca.read (n := 64) (r := 2) (by simp)).trans values.2.2
  · apply (ag.trans ca).mono
    intro c hc
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl <;> simp [keyCallComponents]

end P256.Proofs.Verifying.Wrapper
