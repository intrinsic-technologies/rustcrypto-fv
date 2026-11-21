import P256.Proofs.EcdhWrapper.Peer.Pad.Setup
import P256.Proofs.EcdhWrapper.Peer.Pad.Fill

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray} {slices : Array Input}

theorem prepare (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP=0x106a04) (rsp : stackPtr s=stackPtr initial-504)
    (shape : Sec1.EncodingShape peer) (length : s.regValue .rbp=BitVec.ofNat 64 peer.size) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      MachineRamUnitStrideDecodable bindings u ∧ SupportedIntegerMachineState bindings.processor u ∧
      DirectionFlagUnset u ∧ ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      u.RIP=0x106a29 ∧ stackPtr u=stackPtr initial-504 ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r=s.regValue r) ∧
      u.MXCSR=s.MXCSR ∧ u.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s u #v[work initial] ∧
      (∀ offset, offset=464 ∨ offset=472 →
        memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) ∧
      (∀ i<65, peer.size≤i → u.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=some 0) := by
  obtain ⟨n,a,ra,readyA,_,ea⟩ := setup (returnBoundary initial) outside peer.size shape.size s
    (readyToStep hm hb)
    (programText_slice (programLoaded_codeIn loaded) 0x6a04 setupBytes
      (by decide) (by decide +kernel)) ⟨rip,length⟩
  have ga : AgreesExcept [.reg 0,.reg 2,.reg 7,.reg 6,.flags,.rip] s a := by
    simpa [setupEffect,Effect.components,Write.component,Operand.component] using ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have ha := bindingsSupported_of_ready_agrees hb readyA ga
  have hmA := supportedMachine_of_ready_agrees hm readyA ga
  have da := ga.directionFlagClear (by simp) direction
  have la : ProgramLoaded a := by simpa only [ProgramLoaded,ma] using loaded
  have sa : stackPtr a=stackPtr initial-504 := (ga.read (n := 64) (r := 4) (by simp)).trans rsp
  have dest : a.regValue .rdi=stackPtr initial-336#64+BitVec.ofNat 64 peer.size := by
    have h : a.regValue .rdi=stackPtr s+BitVec.ofNat 64 peer.size+168 := ea.writes.2.2.1
    rw [h,rsp]
    rw [BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 peer.size) 168,← BitVec.add_assoc]
    congr 1
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨u,⟨m,ru⟩,hu,mu,du,lu,gu,iu,su,cu,xu,fu,frame,words,padding⟩ :=
    fill call outside ha hmA da la (fun b h ↦ ga.grow b (grow b h)) ea.rip sa
      (by have := shape.size; omega) dest ea.writes.2.2.2 ea.writes.2.1
  refine ⟨u,⟨n+m,ra.trans ru⟩,hu,mu,du,lu,gu,iu,su,?_,
    xu.trans (ga.mxcsr (by simp)),fu.trans (ga.fcw (by simp)),?_,?_,padding⟩
  · intro r hr
    apply (cu r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ga.read (n := 64) (r := 3) (by simp)
    · exact ga.read (n := 64) (r := 5) (by simp)
    · exact ga.read (n := 64) (r := 12) (by simp)
    · exact ga.read (n := 64) (r := 13) (by simp)
    · exact ga.read (n := 64) (r := 14) (by simp)
    · exact ga.read (n := 64) (r := 15) (by simp)
  · exact memoryWriteFrame_trans (by intro b _; rw [ma]) frame
  · intro offset ho
    simpa only [ma] using words offset ho

end P256.Proofs.EcdhWrapper.Peer.Pad
