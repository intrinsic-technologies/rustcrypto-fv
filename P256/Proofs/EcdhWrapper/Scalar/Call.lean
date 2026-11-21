import P256.Proofs.EcdhWrapper.Scalar.Arguments
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.State
import P256.Proofs.Program.WrapperMemory
import P256.Spec.Program.Functions

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def layout : StackCallLayout 4104 32 33 72 :=
  ⟨512, 392, 128, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

def callComponents (initial : RamState) : List Component :=
  [.reg 3, .reg 6, .reg 7, .reg 4, .mem (stackPtr initial - 512) 8, .rip]

theorem enter [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret, peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x10687d) (rsp : stackPtr s = stackPtr initial - 504)
    (bytes : (MemoryRegion.mk (stackPtr initial - 392).toNat 32).HasBytes s.external secret) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      CalleePre t (returnBoundary initial) 0x112ed0 32 33 72 ∧
      (registerRegion t .rsi 32).HasBytes t.external secret ∧
      stackPtr t = stackPtr initial - 512 ∧
      t.regValue .rdi = stackPtr initial - 128 ∧
      t.regValue .rbx = stackPtr initial - 128 ∧
      (returnBoundary t).rip = 0x106892 ∧
      AgreesExcept (callComponents initial) s t := by
  obtain ⟨n,u,run,ready,_,effect⟩ := arguments (returnBoundary initial) outside s
    (readyToStep hm hb)
    (programText_slice (programLoaded_codeIn loaded) 0x687d argumentBytes
      (by decide +kernel) (by decide +kernel)) rip
  have ag : AgreesExcept [.reg 3,.reg 6,.reg 7,.rip] s u := by
    simpa [argumentEffect,Effect.components,Write.component,Operand.component] using effect.agrees
  have memory := ag.external (by simp [Component.Covers])
  have rspU : stackPtr u = stackPtr initial - 504 :=
    (ag.read (n := 64) (r := 4) (by simp)).trans rsp
  have inputU : u.regValue .rsi = stackPtr initial - 392 := by
    have h : u.regValue .rsi = stackPtr s + 112 := effect.writes.2.1
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have outputU : u.regValue .rdi = stackPtr initial - 128 := by
    have h : u.regValue .rdi = stackPtr s + 376 := effect.writes.2.2
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have rbxU : u.regValue .rbx = stackPtr initial - 128 := by
    have h : u.regValue .rbx = stackPtr s + 376 := effect.writes.1
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have loadedU : ProgramLoaded u := by simpa only [ProgramLoaded,memory] using loaded
  obtain ⟨t,step,readyT,loadedT,ce,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside ready loadedU
    (fun a ha => ag.grow a (grow a ha)) 504 0x688d 0xc63e rspU effect.rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x12ed0 (by decide))
  have push : pushAddr u = stackPtr initial - 512 := by
    rw [pushAddr,rspU,BitVec.sub_sub]
    rfl
  have ca : AgreesExcept [.reg 4,.mem (stackPtr initial - 512) 8,.rip] u t := by
    simpa only [pushEffect_components,push] using ce.agrees
  have total : AgreesExcept (callComponents initial) s t :=
    (ag.trans ca).mono (by simp [callComponents])
  have inputT : t.regValue .rsi = stackPtr initial - 392 :=
    (ca.read (n := 64) (r := 6) (by simp)).trans inputU
  have outputT : t.regValue .rdi = stackPtr initial - 128 :=
    (ca.read (n := 64) (r := 7) (by simp)).trans outputU
  have rbxT : t.regValue .rbx = stackPtr initial - 128 :=
    (ca.read (n := 64) (r := 3) (by simp)).trans rbxU
  have rspT : stackPtr t = stackPtr initial - 512 := ce.writes.1.trans push
  have ret : (returnBoundary t).rip = 0x106892 := (callEffect_stack ce).1
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside layout (bindingsSupported_of_ready_agrees hb readyT total)
    (supportedMachine_of_ready_agrees hm readyT total)
    (total.directionFlagClear (by simp [callComponents]) direction) loadedT
    (fun a ha => total.grow a (grow a ha)) ce.rip rspT inputT outputT
    (by rw [ret]; exact inProgram_of_textOffset 0x6892 (by decide))
  refine ⟨t,⟨n+1,run.trans step⟩,pre,?_,rspT,outputT,rbxT,ret,total⟩
  change (MemoryRegion.mk (t.regValue .rsi).toNat 32).HasBytes t.external secret
  rw [inputT]
  apply hasBytes_agrees_apart ca
  · intro a len member
    have eq : a = stackPtr initial - 512 ∧ len = 8 := by simpa using member
    obtain ⟨rfl,rfl⟩ := eq
    exact stack_sub_apart call.stackAvailable.1 (a := 512) (b := 392)
      (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
  · simpa only [memory] using bytes

end P256.Proofs.EcdhWrapper.Scalar
