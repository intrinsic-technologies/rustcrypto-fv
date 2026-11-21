import P256.Proofs.EcdhWrapper.Multiply.Arguments
import P256.Proofs.EcdhWrapper.Multiply.Memory
import P256.Proofs.Ecdh.Correct
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {d : Nat} {point : Standards.SECG.ECC.Curve.Point}
    (hbi : MachineRamUnitStrideDecodable bindings initial)
    (hmi : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (rip : s.RIP=0x106bc5) (rsp : stackPtr s=stackPtr initial-504)
    (rdx : s.regValue .rdx=stackPtr initial-336)
    (scalar : Nat256At s (stackPtr initial-160) d)
    (affine : Sec1.AffineAt s (stackPtr initial-336) point) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      u.RIP=0x106bd5 ∧ stackPtr u=stackPtr initial-504 ∧
      (MemoryRegion.mk (stackPtr initial-504).toNat 32).HasBytes u.external
        (Points.xBytes (Projective.Multiply.model (ProjectiveWrapper.Decode.projective point) d).toAffine) ∧
      MachineRamUnitStrideDecodable bindings u ∧ SupportedIntegerMachineState bindings.processor u ∧
      DirectionFlagUnset u ∧ ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      CalleeSavedRegistersUnchanged s u ∧ u.MXCSR=s.MXCSR ∧ u.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s u #v[work initial] ∧
      MemoryWriteFrame initial u (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ offset≤472, memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) := by
  have outside := outer_boundary call hmi hbi
  obtain ⟨n,a,ra,readyA,_,ea⟩ := arguments (returnBoundary initial) outside s (readyToStep hm hb)
    (programText_slice (programLoaded_codeIn loaded) 0x6bc5 argumentBytes
      (by decide) (by decide +kernel)) rip
  have ga : AgreesExcept [.reg 7,.reg 6,.rip] s a := by
    simpa [argumentEffect,Effect.components,Write.component,Operand.component] using ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have ha := bindingsSupported_of_ready_agrees hb readyA ga
  have hmA := supportedMachine_of_ready_agrees hm readyA ga
  have da := ga.directionFlagClear (by simp) direction
  have la : ProgramLoaded a := by simpa only [ProgramLoaded,ma] using loaded
  have sa : stackPtr a=stackPtr initial-504 := (ga.read (n := 64) (r := 4) (by simp)).trans rsp
  have diA : a.regValue .rdi=stackPtr initial-504 := ea.writes.1.trans rsp
  have siA : a.regValue .rsi=stackPtr initial-160 := by
    have h : a.regValue .rsi=stackPtr s+344 := ea.writes.2
    rw [h,rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨t,rc,readyT,lt,et,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids (routine := ecdhDiffieHellman) call) outside readyA la
    (fun z hz ↦ ga.grow z (grow z hz)) 504 0x6bd0 0xffff942b sa ea.rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x0 (by decide))
  have effect : (callEffect (fun _ ↦ 0x100000) 0x106bd5 a).Holds a t := et
  have push : pushAddr a=stackPtr initial-512#64 := by rw [pushAddr,sa,BitVec.sub_sub]; rfl
  have st : stackPtr t=stackPtr initial-512 := effect.writes.1.trans push
  have ret : (returnBoundary t).rip=0x106bd5 := (callEffect_stack effect).1
  have gt : AgreesExcept [.reg 4,.mem (stackPtr initial-512) 8,.rip] a t := by
    simpa only [pushEffect_components,push,BitVec.ofNat_eq_ofNat] using effect.agrees
  have ag : AgreesExcept [.reg 7,.reg 6,.reg 4,.mem (stackPtr initial-512) 8,.rip] s t :=
    (ga.trans gt).mono (by simp)
  have di : t.regValue .rdi=stackPtr initial-504 :=
    (gt.read (n := 64) (r := 7) (by simp)).trans diA
  have si : t.regValue .rsi=stackPtr initial-160 :=
    (gt.read (n := 64) (r := 6) (by simp)).trans siA
  have dx : t.regValue .rdx=stackPtr initial-336 :=
    (ag.read (n := 64) (r := 2) (by simp)).trans rdx
  have pre := child_pre call outside (bindingsSupported_of_ready_agrees ha readyT gt)
    (supportedMachine_of_ready_agrees hmA readyT gt) (gt.directionFlagClear (by simp) da)
    lt (fun z hz ↦ ag.grow z (grow z hz)) effect.rip st di si dx ret
  have scalarT : Nat256At t (t.regValue .rsi) d := by
    rw [si]
    refine ⟨scalar.1,fun i hi ↦ ?_⟩
    change t.external[stackPtr initial-160#64+BitVec.ofNat 64 i]?=_
    rw [ScalarFrame.call_byte (frameOffset := 504) (len := 32) (by decide) sa effect
      (by decide : 160≤504) (by decide) hi,ma]
    exact scalar.2 i hi
  have affineT : Sec1.AffineAt t (t.regValue .rdx) point := by
    rw [dx]
    apply affine.of_bytes_eq
    intro i hi
    change t.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=_
    rw [ScalarFrame.call_byte (frameOffset := 504) (len := 65) (by decide) sa effect
      (by decide : 336≤504) (by decide) hi,ma]
    rfl
  obtain ⟨u,result,bytes⟩ := Ecdh.callee_correct pre scalarT affineT
  have prefixFrame : MemoryWriteFrame s t #v[work initial] :=
    memoryWriteFrame_trans (by intro z _; rw [ma])
      (effect.agrees.memoryWriteFrame (push_writes call.stackAvailable.1 sa))
  have finalFrame : MemoryWriteFrame s u #v[work initial] := memoryWriteFrame_trans prefixFrame
    (result.stack_frame call.stackAvailable.1 st di (by decide) (by decide) (by decide) (by decide))
  obtain ⟨m,ru⟩ := result.execution
  refine ⟨u,⟨n+1+m,(ra.trans rc).trans ru⟩,result.rip.trans ret,?_,?_,
    result.bindingsSupported,result.machine,result.directionFlag,result.loaded,
    fun z hz ↦ result.allocated z (ag.grow z (grow z hz)),?_,
    result.mxcsr.trans (ag.mxcsr (by simp)),result.fp87.trans (ag.fcw (by simp)),
    finalFrame,memoryWriteFrame_trans frame (wrapper_memory call finalFrame),
    fun offset ho ↦ upper_read call.stackAvailable.1 finalFrame ho (by omega)⟩
  · have h : stackPtr u=stackPtr t+8 := result.rsp
    rw [h,st]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · simpa only [registerRegion,di] using bytes
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ag.read (n := 64) (r := 3) (by simp)
    · exact ag.read (n := 64) (r := 5) (by simp)
    · exact ag.read (n := 64) (r := 12) (by simp)
    · exact ag.read (n := 64) (r := 13) (by simp)
    · exact ag.read (n := 64) (r := 14) (by simp)
    · exact ag.read (n := 64) (r := 15) (by simp)

end P256.Proofs.EcdhWrapper.Multiply
