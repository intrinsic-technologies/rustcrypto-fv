import ChaCha20Poly1305.Proofs.Decrypt.ShortResult
import ChaCha20Poly1305.Proofs.Decrypt.Output

namespace ChaCha20Poly1305.Proofs.Decrypt
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

structure Returned (fr : Activation) (footprint : List MemoryRegion) (o : Output Value Ram Reg.count) : Prop where
  tag : o.tag = some ⟨64,fr.ret⟩
  atoms : Atom.All fnCode o.values o.store (Decrypt.doneAt fr)
  frame : RamWriteFrame fr.original o.store (fr.region :: footprint)

theorem machineResult [b : Bindings] {s : RamState} {ins : List ByteArray}
    (hb : MachineRamUnitStrideDecodable b s) (hm : SupportedIntegerMachineState b.processor s)
    (hc : ValidCall decrypt s ins) {fr : Activation} (hp : Decrypt.frameInfo.Pre fnCode fr s)
    {o : Output Value Ram Reg.count} (run : lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect fnCode)
      ⟨lifted.locationOf .l1014c0 s,[]⟩ o) {footprint : List MemoryRegion} (ret : Returned fr footprint o)
    {n : Nat} {rs : Vector MemoryRegion n} (covers : ∀ x, (∀ r ∈ rs, ¬r.Contains x) →
      ∀ r ∈ fr.region::footprint, ¬r.Contains x) :
    ∃ fuel t, UniqueExecution s fuel t ∧ SupportedIntegerMachineState b.processor t ∧
      MachineRamUnitStrideDecodable b t ∧ CalleeSavedRegistersUnchanged s t ∧ DirectionFlagUnset t ∧
      MemoryWriteFrame s t rs ∧ RetRel fnCode lifted o t := by
  have ready := callEntry hb hm hc
  have boundary := hp.returnBoundary
  have outside : ReturnOutside (returnBoundary s) fnCode := fun z hz => (hp.retOutside z hz) ∘ (·.trans boundary.1)
  have sim := Lifted.lifted.simulationFixed (Lifted.blocks hb.stringStride fnCode fun _ h => h) outside s
  obtain ⟨t, machineRun, hrel, fixed⟩ := sim.exec run.sem
    ⟨Rel.locationOf (P := lifted) (l := Lifted.Label.l1014c0) ready (show s.RIP = lifted.address .l1014c0 from hp.rip),rfl⟩
  have hat : Atom.All fnCode o.values o.store (Decrypt.frameInfo.doneAtoms fr) := ret.atoms
  obtain ⟨rsp,df,pres,mx,ftw,fcw⟩ := doneAtoms_retRel hrel hat (by rfl) (by decide)
  have rip : t.RIP = fr.ret := (Value.eq_bits (Option.some.inj (ret.tag.symm.trans hrel.rip))).symm
  have hpost : Decrypt.frameInfo.Post fr footprint t :=
    ⟨rip,rsp,pres,df,by rw [mx]; simp only [Value.get,BitVec.setWidth_eq],
     ftw,fcw,(congrArg (·.FS) fixed).trans hp.fs,hrel.store ▸ ret.frame⟩
  have atRet : AtBoundary (returnBoundary s) t := ⟨rip.trans boundary.1.symm,(Value.eq_bits rsp).trans boundary.2.symm⟩
  obtain ⟨u, adv, k, e⟩ := Semantics.exec_iff.mp machineRun
  have real : (machine (returnBoundary s)).Exec s t := Semantics.Reaches.exec (L := machine _) adv
    (.ret ⟨k,e.resolve_left fun h => h.2 atRet⟩)
  obtain ⟨k,hk⟩ := machine_exec_iff.mp real
  obtain ⟨fuel, hu⟩ := Returns.unique_of_boundary
    (nearReturn64Boundary_eq s ready.ready.dataReady ready.ready.cpu.ss hp.memReadable) hk
  have hframe := RamWriteFrame.memoryWriteFrame (hp.original ▸ hpost.frame) covers
  have inv : MachineInvariant s rs t := ⟨hrel.ready,hrel.sse,hframe,df⟩
  exact ⟨fuel,t,hu,inv.supported,⟨hrel.ready.smrr,hrel.ready.memoryType,hb.stringStride,hrel.ready.features.lzcnt⟩,
    sysVCalleeReturn_calleeSaved (hpost.sysVCalleeReturn hp (by decide)),df,hframe,hrel⟩

end ChaCha20Poly1305.Proofs.Decrypt
