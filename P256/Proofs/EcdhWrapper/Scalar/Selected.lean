import P256.Proofs.EcdhWrapper.Scalar.ClearFacts
import P256.Proofs.EcdhWrapper.Scalar.SelectCall

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem decode_select_correct [bindings : Bindings] {initial : RamState}
    {secret peer : ByteArray} {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ first decoded cleared called t,
      Entry initial first secret ∧ CalleeResult first decoded (returnBoundary initial) 33 72 ∧
      (clearEffect decoded).Holds decoded cleared ∧
      AgreesExcept (selectComponents initial) cleared called ∧
      CalleeResult called t (returnBoundary initial) 32 16 ∧
      stackPtr called = stackPtr initial-512 ∧
      called.regValue .rdi = stackPtr initial-264 ∧
      (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      t.RIP = 0x1068d7 ∧ stackPtr t = stackPtr initial-504 ∧
      t.regValue .r14 = stackPtr initial-264 ∧ (t.regValue .rbp).setWidth 8 = 1 ∧
      Nat256At t (stackPtr initial-264) (Arith.uint secret) := by
  obtain ⟨first,decoded,entry,result,⟨prefixFuel,prefixRun⟩,_,rsp,value,tag,_⟩ :=
    decode_correct hb hm call
  obtain ⟨clearFuel,cleared,clearRun,ready,effect⟩ := clear_after_decode call entry result
  have loaded := clear_loaded_after call rsp effect result.loaded
  have bindings := bindingsSupported_of_ready_agrees result.bindingsSupported ready effect.agrees
  have machine := supportedMachine_of_ready_agrees result.machine ready effect.agrees
  have direction := effect.agrees.directionFlagClear
    (by simp [clearEffect,Effect.components]) result.directionFlag
  have stack : stackPtr cleared = stackPtr initial-504 :=
    (effect.agrees.read (n := 64) (r := 4) (by simp [clearEffect,Effect.components])).trans rsp
  have rbx : cleared.regValue .rbx = stackPtr initial-128 :=
    (effect.agrees.read (n := 64) (r := 3) (by simp [clearEffect,Effect.components])).trans
      (entry.result_registers call result).1
  have selectedTag : cleared.external[stackPtr initial-96]? = some 1 := by
    have same := clear_preserved call rsp effect (offset := 96) (len := 1)
      (by decide) (by decide) (i := 0) (by decide)
    simp only [BitVec.add_zero] at same
    exact same.trans tag
  have selectedValue : Nat256At cleared (stackPtr initial-128) (Arith.uint secret) := by
    refine ⟨value.1,fun i hi => ?_⟩
    have same := clear_preserved call rsp effect (offset := 128) (len := 32)
      (by decide) (by decide) hi
    exact same.trans (value.2 i hi)
  obtain ⟨called,t,⟨fuel,run⟩,selected,agrees,stackCall,outputCall,ripT,rspT,r14T,rbpT,valueT⟩ :=
    select_correct call bindings machine direction loaded
      (fun a ha => effect.agrees.grow a (result.allocated a (entry.allocated a ha)))
      entry.pre.outerBoundary effect.rip stack rbx selectedTag selectedValue
  exact ⟨first,decoded,cleared,called,t,entry,result,effect,agrees,selected,
    stackCall,outputCall,⟨prefixFuel+clearFuel+fuel,(prefixRun.trans clearRun).trans run⟩,
    ripT,rspT,r14T,rbpT,valueT⟩

end P256.Proofs.EcdhWrapper.Scalar
