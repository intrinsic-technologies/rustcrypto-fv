import P256.Proofs.EcdhWrapper.Peer.Pad.Prepare
import P256.Proofs.EcdhWrapper.Peer.Pad.CopySetup
import P256.Proofs.EcdhWrapper.Peer.Pad.Copy

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {address : BitVec 64}
    (hbi : MachineRamUnitStrideDecodable bindings initial)
    (hmi : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (rip : s.RIP=0x106a04) (rsp : stackPtr s=stackPtr initial-504)
    (source : s.regValue .r12=address) (length : s.regValue .rbp=BitVec.ofNat 64 peer.size)
    (pointer : memLoad initial.external (initial.regValue .rdi+8) 64=address) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      MachineRamUnitStrideDecodable bindings u ∧ SupportedIntegerMachineState bindings.processor u ∧
      DirectionFlagUnset u ∧ ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      u.RIP=0x106a3d ∧ stackPtr u=stackPtr initial-504 ∧
      CalleeSavedRegistersUnchanged s u ∧ u.MXCSR=s.MXCSR ∧ u.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s u #v[ScalarFrame.Work.region initial 4104 264] ∧
      MemoryWriteFrame initial u (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ offset≤264, memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) ∧
      (∀ offset, offset=464 ∨ offset=472 →
        memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) ∧
      Sec1.EncodedPointAt u (stackPtr initial-336) peer := by
  have outside := outer_boundary call hmi hbi
  obtain ⟨point,_,_,_,_,_,shape⟩ := arguments_decoded call.argumentsValid
  obtain ⟨addr,old,_,bound,bytes,_⟩ := Guards.preserved_peer call frame
  have eq : addr=address := old.symm.trans pointer
  rw [eq] at bound bytes
  obtain ⟨a,⟨n,ra⟩,ha,ma,da,la,gra,ia,sa,ca,xa,fa,fra,wordsA,pad⟩ :=
    prepare call outside hb hm direction loaded grow rip rsp shape length
  have bytesA := peer_bytes call pointer bound fra bytes
  have srcA : a.regValue .r12=address := (ca .r12 (by simp)).trans source
  have lenA : a.regValue .rbp=BitVec.ofNat 64 peer.size := (ca .rbp (by simp)).trans length
  obtain ⟨m,b,rb,readyB,_,eb⟩ := copy_setup (returnBoundary initial) outside a
    (readyToStep ma ha)
    (programText_slice (programLoaded_codeIn la) 0x6a29 copySetupBytes
      (by decide) (by decide +kernel)) ia
  have gb : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] a b := by
    simpa [copySetupEffect,Effect.components,Write.component,Operand.component] using eb.agrees
  have mb := gb.external (by simp [Component.Covers])
  have hbB := bindingsSupported_of_ready_agrees ha readyB gb
  have hmB := supportedMachine_of_ready_agrees ma readyB gb
  have db := gb.directionFlagClear (by simp) da
  have lb : ProgramLoaded b := by simpa only [ProgramLoaded,mb] using la
  have sb : stackPtr b=stackPtr initial-504 := (gb.read (n := 64) (r := 4) (by simp)).trans sa
  have dest : b.regValue .rdi=stackPtr initial-336#64 := by
    have h : b.regValue .rdi=stackPtr a+168 := eb.writes.1
    rw [h,sa]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have src : b.regValue .rsi=address := eb.writes.2.1.trans srcA
  have count : b.regValue .rdx=BitVec.ofNat 64 peer.size := eb.writes.2.2.trans lenA
  have bytesB : (MemoryRegion.mk address.toNat peer.size).HasBytes b.external peer := by
    simpa only [mb] using bytesA
  have padB : ∀ i<65, peer.size≤i → b.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=some 0 := by
    simpa only [mb] using pad
  obtain ⟨u,⟨k,ru⟩,hu,mu,du,lu,gu,iu,su,cu,xu,fu,fru,wordsU,encoded⟩ :=
    copy call outside hbB hmB db lb (fun c h ↦ gb.grow c (gra c h)) eb.rip sb shape
      dest src count pointer bound bytesB padB
  have memory : MemoryWriteFrame s u #v[work initial] :=
    memoryWriteFrame_trans fra (memoryWriteFrame_trans (by intro c _; rw [mb]) fru)
  refine ⟨u,⟨n+m+k,(ra.trans rb).trans ru⟩,hu,mu,du,lu,gu,iu,su,?_,
    xu.trans ((gb.mxcsr (by simp)).trans xa),fu.trans ((gb.fcw (by simp)).trans fa),
    memory,memoryWriteFrame_trans frame (wrapper_memory call memory),?_,?_,encoded⟩
  · intro r hr
    apply (cu r hr).trans
    apply Eq.trans _ (ca r hr)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact gb.read (n := 64) (r := 3) (by simp)
    · exact gb.read (n := 64) (r := 5) (by simp)
    · exact gb.read (n := 64) (r := 12) (by simp)
    · exact gb.read (n := 64) (r := 13) (by simp)
    · exact gb.read (n := 64) (r := 14) (by simp)
    · exact gb.read (n := 64) (r := 15) (by simp)
  · intro offset ho
    exact upper_read call.stackAvailable.1 memory ho (by omega)
  · intro offset ho
    exact (wordsU offset ho).trans (by simpa only [mb] using wordsA offset ho)

end P256.Proofs.EcdhWrapper.Peer.Pad
