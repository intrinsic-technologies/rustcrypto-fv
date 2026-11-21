import P256.Proofs.EcdhWrapper.Finish.Return.Zero
import P256.Proofs.EcdhWrapper.Finish.Return.Control
import P256.Proofs.EcdhWrapper.Finish.Return.Store
import P256.Proofs.EcdhWrapper.Finish.Return.Memory
import P256.Proofs.EcdhWrapper.Finish.Return.Restore

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
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
    (rip : s.RIP=0x106c0c) (rsp : stackPtr s=stackPtr initial-504)
    (output : s.regValue .rcx=initial.regValue .rcx)
    (capacity : s.regValue .r8=initial.regValue .r8)
    (saved : ∀ reg ∈ savedRegisters,
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64=initial.regValue reg.1)
    (returnAddress : memLoad s.external (stackPtr initial) 64=(returnBoundary initial).rip)
    (frame : MemoryWriteFrame initial s #v[outputRegion ecdhDiffieHellman initial [secret,peer],
      allocatorStateRegion,randomSourceRegion,callStack ecdhDiffieHellman initial])
    (data : (MemoryRegion.mk (initial.regValue .rcx+8).toNat 32).HasBytes s.external bytes)
    (execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      SuccessfulStatus final ∧
      MemoryWriteFrame initial final #v[outputRegion ecdhDiffieHellman initial [secret,peer],
        allocatorStateRegion,randomSourceRegion,callStack ecdhDiffieHellman initial] ∧
      readOutput ecdhDiffieHellman initial final=.ok bytes := by
  have boundary := initial_boundary call hmi hbi
  obtain ⟨ret,eq,low,outside⟩ := call.returnAddress
  rw [boundary] at eq
  cases eq
  obtain ⟨a,ra,readyA,loadedA,ripA,ga⟩ := zero call outside (readyToStep hm hb) loaded grow rsp rip
  have capA : 7<(a.regValue .r8).toNat := by
    have h : a.regValue .r8=initial.regValue .r8 := (ga.read (n := 64) (r := 8) (by simp)).trans capacity
    rw [h]
    have := Copy.capacity call
    omega
  obtain ⟨b,rb,readyB,ripB,count,gb⟩ := control outside readyA loadedA ripA capA
  have memB := gb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded,memB] using loadedA
  have outB : b.regValue .rcx=initial.regValue .rcx :=
    ((ga.trans gb).read (n := 64) (r := 1) (by simp)).trans output
  have growB := fun a h ↦ gb.grow a (ga.grow a (grow a h))
  have writable := (Copy.output_writable call growB).add 0 (len := 8) (by decide)
  have apart := Copy.output_code call (off := 0) (len := 8) (pc := 0x6cd5) (n := 7)
    (by decide) (by decide)
  obtain ⟨c,rc,readyC,ripC,status,length,gc⟩ := store outside readyB loadedB ripB outB count
    (by simpa only [BitVec.add_zero] using writable)
    (by simpa only [BitVec.add_zero,Extracted.textAddress,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using apart)
  have total : AgreesExcept (components initial) s c := ((ga.trans gb).trans gc).mono (by simp [components])
  have growC := fun a h ↦ total.grow a (grow a h)
  have savedC : ∀ reg ∈ savedRegisters,
      memLoad c.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64=initial.regValue reg.1 := by
    intro reg hr
    have bound : reg.2≤48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (stack_word call total bound).trans (saved reg hr)
  have returnC : memLoad c.external (stackPtr initial) 64=(returnBoundary initial).rip := by
    have h := stack_word call total (off := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans returnAddress
  obtain ⟨final,run,machine,bindingsSupported,calleeSaved,df,memory,rax⟩ :=
    restore call.stackAvailable.1 (bindingsSupported_of_ready_agrees hb readyC total)
      (supportedMachine_of_ready_agrees hm readyC total) (loaded_after call loaded total)
      (total.directionFlagClear (by simp [components]) direction) growC
      ((total.read (n := 64) (r := 4) (by simp [components])).trans rsp)
      savedC returnC ripC outside low
  obtain ⟨n,prefixRun⟩ := execution
  obtain ⟨fuel,unique⟩ := ((((prefixRun.trans ra).trans rb).trans rc).returns run).unique_of_boundary boundary
  refine ⟨fuel,final,unique,machine,bindingsSupported,calleeSaved,df,?_,?_,?_⟩
  · change (final.regValue .rax).setWidth 32=0
    rw [rax,status]; rfl
  · intro a ha
    rw [memory]
    exact memoryWriteFrame_trans frame (local_frame call total) a ha
  · have size : bytes.size=32 := data.1
    have payloadC := payload call total data
    apply readOutput_of_bytes (by omega)
    · change Bytes final.external (initial.regValue .rcx) 8 (storedByte (BitVec.ofNat 64 bytes.size))
      rw [memory,size]
      have allocated := (Copy.output_writable call growC).add 0 (len := 8) (by decide)
      have hb := Bytes.of_memLoad (n := 64) (by
        intro i hi
        simpa only [BitVec.add_zero] using allocated.mem i hi)
      rw [length] at hb
      exact hb
    · intro i hi
      change final.external[initial.regValue .rcx+8+BitVec.ofNat 64 i]?=some bytes.data[i]!
      rw [memory]
      have h := payloadC.2 ⟨i,hi⟩
      simpa only [ByteArray.getElem_eq_getElem_data,BitVec.ofNat_add,BitVec.ofNat_toNat,
        BitVec.setWidth_eq,getElem!_pos bytes.data i (by simpa only [ByteArray.size_data] using hi)] using h

end P256.Proofs.EcdhWrapper.Finish.Return
