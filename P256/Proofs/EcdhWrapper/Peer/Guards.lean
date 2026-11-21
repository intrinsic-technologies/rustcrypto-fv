import P256.Proofs.EcdhWrapper.Peer.Guards.Branches
import P256.Proofs.EcdhWrapper.Peer.Guards.Load
import P256.Proofs.EcdhWrapper.Peer.Guards.Header
import P256.Proofs.EcdhWrapper.Peer.Guards.Input
import P256.Proofs.EcdhWrapper.Model
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (rip : s.RIP = 0x1069b6) (count : s.regValue .r13 = 2)
    (pointers : s.regValue .r12 = initial.regValue .rdi)
    (lengths : s.regValue .r15 = initial.regValue .rdx) :
    ∃ address t, Advances (returnBoundary initial) 17 s t ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ t.RIP = 0x106a04 ∧
      t.regValue .r12 = address ∧ t.regValue .rbp = BitVec.ofNat 64 peer.size ∧
      memLoad initial.external (initial.regValue .rdi+8) 64 = address ∧ address ≠ 0 ∧
      (MemoryRegion.mk address.toNat peer.size).Bounded ∧
      (MemoryRegion.mk address.toNat peer.size).HasBytes t.external peer ∧
      t.external = s.external ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      AgreesExcept [.reg 0,.reg 1,.reg 5,.reg 12,.flags,.rip] s t := by
  have outside := outer_boundary call hm hb
  obtain ⟨point,_,_,_,_,_,shape⟩ := arguments_decoded call.argumentsValid
  have sizes := shape.size
  have sizePositive : peer.size > 0 := by omega
  have sizeNonzero : BitVec.ofNat 64 peer.size ≠ 0 := by
    intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hn
    rw [Nat.mod_eq_of_lt (by omega : peer.size < 2^64)] at hn
    change peer.size = 0 at hn
    omega
  obtain ⟨address,original,nonzero,bounded,bytes,hp,hl,pv,lv⟩ := preserved_peer call frame
  obtain ⟨a,ra,readyA,ripA,ga⟩ := count_guard ready loaded outside rip count
  have ma := ga.external (by simp [Component.Covers])
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded,ma] using loaded
  have pa : a.regValue .r12 = initial.regValue .rdi :=
    (ga.read (n := 64) (r := 12) (by simp)).trans pointers
  have la : a.regValue .r15 = initial.regValue .rdx :=
    (ga.read (n := 64) (r := 15) (by simp)).trans lengths
  obtain ⟨b,rb,readyB,ripB,ptrB,lenB,gb⟩ := load readyA loadedA outside ripA
    (by rw [pa]; exact ⟨hp.low,by simpa only [ma] using hp.mem⟩)
    (by rw [la]; exact ⟨hl.low,by simpa only [ma] using hl.mem⟩)
  have mb := gb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded,mb] using loadedA
  have pointerB : b.regValue .r12 = address := by simpa only [ma,pa,pv] using ptrB
  have lengthB : b.regValue .rbp = BitVec.ofNat 64 peer.size := by
    simpa only [ma,la,lv] using lenB
  obtain ⟨c,rc,readyC,ripC,gc⟩ := pointer_guard readyB loadedB outside ripB
    (by rw [pointerB]; exact nonzero)
  have mc := gc.external (by simp [Component.Covers])
  have loadedC : ProgramLoaded c := by simpa only [ProgramLoaded,mc] using loadedB
  have lengthC : c.regValue .rbp = BitVec.ofNat 64 peer.size :=
    (gc.read (n := 64) (r := 5) (by simp)).trans lengthB
  obtain ⟨d,rd,readyD,ripD,gd⟩ := nonempty_guard readyC loadedC outside ripC
    (by rw [lengthC]; exact sizeNonzero)
  have md := gd.external (by simp [Component.Covers])
  have loadedD : ProgramLoaded d := by simpa only [ProgramLoaded,md] using loadedC
  have pointerD : d.regValue .r12 = address :=
    ((gc.trans gd).read (n := 64) (r := 12) (by simp)).trans pointerB
  have lengthD : d.regValue .rbp = BitVec.ofNat 64 peer.size :=
    (gd.read (n := 64) (r := 5) (by simp)).trans lengthC
  have bytesD : (registerRegion d .r12 peer.size).HasBytes d.external peer := by
    simpa only [registerRegion,pointerD,md,mc,mb,ma] using bytes
  have boundedD : (registerRegion d .r12 peer.size).Bounded := by
    simpa only [registerRegion,pointerD] using bounded
  obtain ⟨t,rt,readyT,ripT,gt⟩ := header readyD loadedD outside ripD lengthD boundedD bytesD shape
  have total : AgreesExcept [.reg 0,.reg 1,.reg 5,.reg 12,.flags,.rip] s t :=
    ((((ga.trans gb).trans gc).trans gd).trans gt).mono (by simp)
  have memory := total.external (by simp [Component.Covers])
  refine ⟨address,t,(((ra.trans rb).trans rc).trans rd).trans rt,readyT,?_,ripT,
    (gt.read (n := 64) (r := 12) (by simp)).trans pointerD,
    (gt.read (n := 64) (r := 5) (by simp)).trans lengthD,original,nonzero,bounded,?_,memory,?_,total⟩
  · simpa only [ProgramLoaded,memory] using loaded
  · simpa only [memory] using bytes
  · intro a ha
    rw [memory]
    exact frame a ha

end P256.Proofs.EcdhWrapper.Peer.Guards
