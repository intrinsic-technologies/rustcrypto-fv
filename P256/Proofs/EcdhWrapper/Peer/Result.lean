import P256.Proofs.EcdhWrapper.Peer.Result.Flag
import P256.Proofs.EcdhWrapper.Peer.Result.Setup
import P256.Proofs.EcdhWrapper.Peer.Result.Copy

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Result

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {point : Standards.SECG.ECC.Curve.Point}
    (hbi : MachineRamUnitStrideDecodable bindings initial)
    (hmi : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (rip : s.RIP=0x106b85) (rsp : stackPtr s=stackPtr initial-504)
    (affine : Sec1.AffineAt s (stackPtr initial-128) point)
    (valid : s.external[stackPtr initial-56]?=some 1) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      u.RIP=0x106bc5 ∧ stackPtr u=stackPtr initial-504 ∧
      u.regValue .rdx=stackPtr initial-336 ∧ Sec1.AffineAt u (stackPtr initial-336) point ∧
      MachineRamUnitStrideDecodable bindings u ∧ SupportedIntegerMachineState bindings.processor u ∧
      DirectionFlagUnset u ∧ ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      CalleeSavedRegistersUnchanged s u ∧ u.MXCSR=s.MXCSR ∧ u.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s u #v[MemoryRegion.mk (stackPtr initial-336).toNat 72] ∧
      MemoryWriteFrame initial u (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ offset≤264, memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) ∧
      AgreesExcept (components initial) s u := by
  have outside := outer_boundary call hmi hbi
  obtain ⟨a,ra,readyA,ia,ga⟩ := flag call outside (readyToStep hm hb) loaded grow rip rsp valid
  have ga' : AgreesExcept (components initial) s a := ga.mono (by simp [components])
  have la := loaded_after call ga' loaded
  have ha := bindingsSupported_of_ready_agrees hb readyA ga
  have ma := supportedMachine_of_ready_agrees hm readyA ga
  have da := ga.directionFlagClear (by simp) direction
  have sa : stackPtr a=stackPtr initial-504 := (ga.read (n := 64) (r := 4) (by simp)).trans rsp
  have affineA := affine_preserved call.stackAvailable.1 ga' affine
  obtain ⟨n,b,rb,readyB,_,eb⟩ := setup (returnBoundary initial) outside a readyA
    (programText_slice (programLoaded_codeIn la) 0x6baa setupBytes
      (by decide) (by decide +kernel)) ia
  have gb : AgreesExcept [.reg 2,.reg 6,.reg 1,.reg 7,.rip] a b := by
    simpa [setupEffect,Effect.components,Write.component,Operand.component] using eb.agrees
  have mb := gb.external (by simp [Component.Covers])
  have lb : ProgramLoaded b := by simpa only [ProgramLoaded,mb] using la
  have hbB := bindingsSupported_of_ready_agrees ha readyB gb
  have db := gb.directionFlagClear (by simp) da
  have dst : b.regValue .rdx=stackPtr initial-336#64 := by
    have h : b.regValue .rdx=stackPtr a+168 := eb.writes.1
    rw [h,sa]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have src : b.regValue .rsi=stackPtr initial-128#64 := by
    have h : b.regValue .rsi=stackPtr a+376 := eb.writes.2.1
    rw [h,sa]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have dest : b.regValue .rdi=stackPtr initial-336#64 := by
    have h : b.regValue .rdi=stackPtr a+168 := eb.writes.2.2.2
    rw [h,sa]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have affineB : Sec1.AffineAt b (stackPtr initial-128) point :=
    affineA.of_bytes_eq (fun _ _ ↦ by rw [mb])
  obtain ⟨u,ru,readyU,iu,gu,bytes⟩ := copy call outside hbB readyB db lb
    (fun z hz ↦ gb.grow z (ga.grow z (grow z hz))) eb.rip src dest eb.writes.2.2.1
  have total : AgreesExcept (components initial) s u := ((ga.trans gb).trans gu).mono (by simp [components])
  refine ⟨u,⟨5+n+9,(ra.trans rb).trans ru⟩,iu,
    (total.read (n := 64) (r := 4) (by simp [components])).trans rsp,
    (gu.read (n := 64) (r := 2) (by simp)).trans dst,
    affineB.of_bytes_eq (fun i hi ↦ bytes i (by omega)),
    bindingsSupported_of_ready_agrees hb readyU total,
    supportedMachine_of_ready_agrees hm readyU total,
    total.directionFlagClear (by simp [components]) direction,loaded_after call total loaded,
    fun z hz ↦ total.grow z (grow z hz),?_,total.mxcsr (by simp [components]),
    total.fcw (by simp [components]),exact_frame call.stackAvailable.1 total,
    memoryWriteFrame_trans frame (Pad.wrapper_memory call (work_frame call.stackAvailable.1 total)),?_,total⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact total.read (n := 64) (r := 3) (by simp [components])
    · exact total.read (n := 64) (r := 5) (by simp [components])
    · exact total.read (n := 64) (r := 12) (by simp [components])
    · exact total.read (n := 64) (r := 13) (by simp [components])
    · exact total.read (n := 64) (r := 14) (by simp [components])
    · exact total.read (n := 64) (r := 15) (by simp [components])
  · intro offset ho
    exact Pad.upper_read call.stackAvailable.1 (work_frame call.stackAvailable.1 total) ho (by omega)

end P256.Proofs.EcdhWrapper.Peer.Result
