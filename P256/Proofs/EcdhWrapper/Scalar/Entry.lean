import P256.Proofs.EcdhWrapper.Scalar.Call
import P256.Proofs.EcdhWrapper.Copy.Compose
import P256.Proofs.Generate.Scalar.Correct

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.EcdhWrapper.Copy (CopyResult copyComponents)

structure Entry [bindings : Bindings] (initial t : RamState) (secret : ByteArray) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial t
  pre : CalleePre t (returnBoundary initial) 0x112ed0 32 33 72
  bytes : (registerRegion t .rsi 32).HasBytes t.external secret
  rsp : stackPtr t = stackPtr initial - 512
  output : t.regValue .rdi = stackPtr initial - 128
  rbx : t.regValue .rbx = stackPtr initial - 128
  ret : (returnBoundary t).rip = 0x106892
  history : ∃ s u v, GuardedEntry initial s secret ∧
    (Copy.setupEffect s).Holds s u ∧
    CopyResult (returnBoundary initial) secret u v 0x10687d ∧
    AgreesExcept (callComponents initial) v t

theorem enter_correct [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret, peer] slices) :
    ∃ t, Entry initial t secret := by
  obtain ⟨s,u,v,guarded,⟨setupFuel,setupRun⟩,setup,copied⟩ := copy_entry_correct hb hm call
  have setupAgrees :
      AgreesExcept [.reg 13,.mem (stackPtr s+32) 8,.mem (stackPtr s+40) 8,.rip] s u := by
    simpa [Copy.setupEffect,Effect.components,Write.component,Operand.component] using setup.agrees
  have initialAgrees := (guarded.agrees.trans setupAgrees).trans copied.agrees
  have copiedBindings := bindingsSupported_of_ready_agrees hb copied.ready initialAgrees
  have copiedMachine := supportedMachine_of_ready_agrees hm copied.ready initialAgrees
  have copiedDirection : DirectionFlagUnset v :=
    initialAgrees.directionFlagClear (by
      simp [saveFrame,arenaComponents,guardComponents,copyComponents]) call.directionFlagUnset
  have setupRsp : stackPtr u = stackPtr initial - 504 :=
    (setupAgrees.read (n := 64) (r := 4) (by simp)).trans guarded.rsp
  have inputAddress : stackPtr u + 112 = stackPtr initial - 392 := by
    rw [setupRsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have bytes : (MemoryRegion.mk (stackPtr initial - 392).toNat 32).HasBytes v.external secret := by
    simpa only [inputAddress] using copied.bytes
  obtain ⟨t,⟨callFuel,callRun⟩,pre,input,rsp,output,rbx,ret,agrees⟩ :=
    enter call copiedBindings copiedMachine copiedDirection copied.loaded initialAgrees.grow
      (outer_boundary call hm hb) copied.rip (copied.rsp.trans setupRsp) bytes
  obtain ⟨guardFuel,guardRun⟩ := guarded.execution
  obtain ⟨copyFuel,copyRun⟩ := copied.execution
  exact ⟨t,⟨⟨guardFuel+setupFuel+copyFuel+callFuel,
    ((guardRun.trans setupRun).trans copyRun).trans callRun⟩,
    pre,input,rsp,output,rbx,ret,⟨s,u,v,guarded,setup,copied,agrees⟩⟩⟩

theorem decode_correct [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret, peer] slices) :
    ∃ s t, Entry initial s secret ∧
      CalleeResult s t (returnBoundary initial) 33 72 ∧
      (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      t.RIP = 0x106892 ∧ stackPtr t = stackPtr initial - 504 ∧
      SecretKeyFromBytes.Scalar.Nat256At t (stackPtr initial - 128) (Arith.uint secret) ∧
      t.external[stackPtr initial - 96]? = some 1 ∧
      t.regValue .rax = stackPtr initial - 128 := by
  obtain ⟨s,entry⟩ := enter_correct hb hm call
  obtain ⟨t,result,value,tag,output⟩ := Generate.Scalar.from_repr_correct entry.pre entry.bytes
  have range : Arith.uint secret < Operations.domain.n :=
    ((arguments_iff secret peer).mp call.argumentsValid).2.2.1
  have tagAddress : stackPtr initial - 128 + 32 = stackPtr initial - 96 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  rw [entry.output,ite_eq_left range,tagAddress] at tag
  rw [entry.output] at value output
  obtain ⟨prefixFuel,prefixRun⟩ := entry.execution
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨s,t,entry,result,⟨prefixFuel+fuel,prefixRun.trans run⟩,
    result.rip.trans entry.ret,?_,value,tag,output⟩
  have rsp : stackPtr t = stackPtr s + 8 := result.rsp
  rw [rsp,entry.rsp]
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

end P256.Proofs.EcdhWrapper.Scalar
