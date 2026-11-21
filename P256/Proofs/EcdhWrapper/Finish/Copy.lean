import P256.Proofs.EcdhWrapper.Finish.Copy.Capacity
import P256.Proofs.EcdhWrapper.Finish.Copy.Run
import P256.Proofs.EcdhWrapper.Finish.Copy.Frame

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [bindings : Bindings] {initial s : RamState} {secret peer bytes : ByteArray}
    {slices : Array Input}
    (hbi : MachineRamUnitStrideDecodable bindings initial)
    (hmi : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (rip : s.RIP=0x106bd5) (rsp : stackPtr s=stackPtr initial-504)
    (output : memLoad s.external (stackPtr initial-472) 64=initial.regValue .rcx)
    (size : memLoad s.external (stackPtr initial-464) 64=initial.regValue .r8)
    (source : (MemoryRegion.mk (stackPtr initial-504).toNat 32).HasBytes s.external bytes) :
    ∃ t, Advances (returnBoundary initial) 12 s t ∧
      MachineRamUnitStrideDecodable bindings t ∧ SupportedIntegerMachineState bindings.processor t ∧
      DirectionFlagUnset t ∧ ProgramLoaded t ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) ∧
      t.RIP=0x106c0c ∧ stackPtr t=stackPtr initial-504 ∧
      t.regValue .rcx=initial.regValue .rcx ∧ t.regValue .r8=initial.regValue .r8 ∧
      (MemoryRegion.mk (initial.regValue .rcx+8).toNat 32).HasBytes t.external bytes ∧
      CalleeSavedRegistersUnchanged s t ∧ t.MXCSR=s.MXCSR ∧ t.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s t #v[MemoryRegion.mk (initial.regValue .rcx+8).toNat 32] ∧
      MemoryWriteFrame initial t #v[outputRegion ecdhDiffieHellman initial [secret,peer],
        allocatorStateRegion,randomSourceRegion,callStack ecdhDiffieHellman initial] ∧
      (∀ off n, off≤4104 → n/8≤off+8 →
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) n=
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) n) ∧
      AgreesExcept (components initial) s t := by
  have outside := outer_boundary call hmi hbi
  obtain ⟨a,ra,readyA,ripA,r8A,ga⟩ :=
    check_capacity call outside (readyToStep hm hb) loaded grow rsp rip size
  have memA := ga.external (by simp [Component.Covers])
  have spA : stackPtr a=stackPtr initial-504 := (ga.read (n := 64) (r := 4) (by simp)).trans rsp
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded,memA] using loaded
  have outputA : memLoad a.external (stackPtr initial-472) 64=initial.regValue .rcx := by
    simpa only [memA] using output
  obtain ⟨t,rt,readyT,loadedT,ripT,cxT,r8eq,gt,words⟩ := copy_words call outside readyA loadedA
    (fun a h ↦ ga.grow a (grow a h)) spA ripA outputA
  have total : AgreesExcept (components initial) s t :=
    (ga.trans gt).mono (by simp [components])
  have r8T : t.regValue .r8=initial.regValue .r8 := r8eq.trans r8A
  have sourceA : (MemoryRegion.mk (stackPtr initial-504).toNat 32).HasBytes a.external bytes := by
    simpa only [memA] using source
  have copied : (MemoryRegion.mk (initial.regValue .rcx+8).toNat 32).HasBytes t.external bytes := by
    have allocated := (output_writable call (s := t) (fun a h ↦ total.grow a (grow a h))).add 8
      (len := 32) (by decide) |>.mem
    have bytesT := bytes_of_memLoad_eq (count := 4) sourceA allocated words
    refine ⟨source.1,?_⟩
    intro i
    change t.external[BitVec.ofNat 64 ((initial.regValue .rcx+8).toNat+i.val)]?=some bytes.data[i.val]
    have h := bytesT i.val i.isLt
    simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.ofNat_eq_ofNat,
      getElem!_pos bytes.data i.val (by simpa only [ByteArray.size_data] using i.isLt)] using h
  exact ⟨t,ra.trans rt,bindingsSupported_of_ready_agrees hb readyT total,
    supportedMachine_of_ready_agrees hm readyT total,total.directionFlagClear (by simp [components]) direction,
    loadedT,fun a h ↦ total.grow a (grow a h),ripT,
    (total.read (n := 64) (r := 4) (by simp [components])).trans rsp,cxT,r8T,copied,
    registers_preserved total,total.mxcsr (by simp [components]),total.fcw (by simp [components]),
    payload_frame call total,final_frame call frame total,
    fun off n ho hn ↦ stack_read call total ho hn,total⟩

end P256.Proofs.EcdhWrapper.Finish.Copy
