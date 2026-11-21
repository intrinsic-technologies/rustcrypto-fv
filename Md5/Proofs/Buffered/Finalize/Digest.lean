import Md5.Proofs.Buffered.Finalize.Digest.PaddingInput
import Md5.Proofs.Buffered.Finalize.Digest.Padding.Proof
import Md5.Proofs.Buffered.Finalize.Digest.Branch
import Md5.Proofs.Buffered.Finalize.Digest.Long
import Md5.Proofs.Buffered.Finalize.Digest.Finish

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Digest

theorem digest_finalize [Bindings] {boundary : ReturnBoundary} {input : ByteArray} {s : RamState}
    (hp : Pre .digest boundary input s) : ∃ t, Post .digest boundary input s t := by
  have complete {v : RamState} (hv : ∃ fuel, Advances boundary fuel s v)
      (ha : AgreesExcept (Kind.digest.changes s) s v)
      (hr : ReadyToStep v) (hc : CodeIn Extracted.programImage v)
      (hs : Storage .digest v) (hip : v.RIP = 0x1001df)
      (hpos : (Operand.reg 12 : Operand 64).read v = BitVec.ofNat 64 (input.size % 64))
      (hblocks : (Operand.reg 15 : Operand 64).read v = BitVec.ofNat 64 (input.size / 64))
      (hprefix : Bytes v.external (stackPtr v + 24) 56
        (fun i ↦ if input.size % 64 < 56 then (firstBlock input)[i]! else 0))
      (hbuf : (⟨(stackPtr v + 8).toNat, 16⟩ : MemoryRegion).HasBytes v.external
        ⟨(paddedBuffer input).toBytes.toArray⟩) : ∃ t, Post .digest boundary input s t := by
    obtain ⟨t, ht⟩ := Finish.run hr hc hs hp.boundaryOutside hip hpos hblocks hprefix hbuf
    have hsp : stackPtr v = stackPtr s := ha.read (n := 64) (r := 4) (by
      simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
    have hchanges : Kind.digest.changes v = Kind.digest.changes s := by
      simp only [Kind.changes, Kind.localChanges, hsp]
    obtain ⟨n, hn⟩ := hv
    obtain ⟨k, hk⟩ := ht.advances
    refine ⟨t, ⟨⟨n + k, hn.trans hk⟩, ht.ready, ht.code, ht.rip, ?_, ?_⟩⟩
    · have hout := ht.output
      have haddr : (stackPtr s + 8).toNat = (stackPtr s).toNat + 8 :=
        hp.toStorage.stackAddress (offset := 8) (by decide +kernel)
      rw [hsp, haddr] at hout
      simpa only [Kind.resultRegion, Kind.resultOffset, messageDigest_paddedBuffer] using hout
    · have hat := ht.agrees
      rw [hchanges] at hat
      exact (ha.trans hat).mono (by simp)
  obtain ⟨n, u, hu, hup, hua⟩ := prepare_padding hp
  obtain ⟨v, hv⟩ := Padding.pad hp.stride hup
  obtain ⟨w, hw, hwr, hwc, hwip, hwa⟩ := padding_branch hv.ready hv.code
    hp.boundaryOutside hv.rip (Nat.mod_lt _ (by decide)) hv.remaining
  have hwsp : stackPtr w = stackPtr v := hwa.read (n := 64) (r := 4) (by simp)
  have hwmem : w.external = v.external := hwa.external (by simp [Component.Covers])
  have hw12 : (Operand.reg 12 : Operand 64).read w = BitVec.ofNat 64 (input.size % 64) :=
    (hwa.read (n := 64) (r := 12) (by simp)).trans hv.position
  have hw15 : (Operand.reg 15 : Operand 64).read w = BitVec.ofNat 64 (input.size / 64) :=
    (hwa.read (n := 64) (r := 15) (by simp)).trans hv.blocks
  have hws : Storage .digest w := hv.storage.of_agrees hwa hwsp
  have hwbuffer : (⟨(stackPtr w + 8).toNat, 16⟩ : MemoryRegion).HasBytes w.external
      ⟨(absorbedBuffer input).toBytes.toArray⟩ := by
    rw [hwsp, hwmem]
    exact hv.buffer
  have hwpadded : Bytes w.external (stackPtr w + 24) 64
      (fun i ↦ (firstBlock input)[i]!) := by
    rw [hwsp, hwmem]
    exact hv.padded
  have husp : stackPtr u = stackPtr s := hua.read (n := 64) (r := 4) (by
    simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
  have hchanges : Kind.digest.changes u = Kind.digest.changes s := by
    simp only [Kind.changes, Kind.localChanges, husp]
  have hva : AgreesExcept (Kind.digest.changes s) s v := by
    have hat := hv.agrees
    rw [hchanges] at hat
    exact (hua.trans hat).mono (by simp)
  have hwa' : AgreesExcept (Kind.digest.changes s) s w := by
    apply (hva.trans hwa).mono
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl
    · exact hc
    all_goals simp [Kind.changes]
  obtain ⟨m, hm⟩ := hv.advances
  have hrun : Advances boundary (n + m + 2) s w := (hu.trans hm).trans hw
  by_cases hshort : input.size % 64 < 56
  · refine complete ⟨_, hrun⟩ hwa' hwr hwc hws
      (by simpa only [ite_eq_left hshort] using hwip) hw12 hw15 ?_ ?_
    · intro i hi
      simpa only [ite_eq_left hshort] using hwpadded i (by omega)
    · simpa only [paddedBuffer, ite_eq_left hshort] using hwbuffer
  · have hlp : Long.Pre boundary input w := by
      refine ⟨hws, hwr, hwc, hp.boundaryOutside, ?_, by omega, ?_, hwbuffer, hw12, hw15⟩
      · simpa only [ite_eq_right hshort] using hwip
      · have hb := hasBytes_of_bytes (bytes := firstBlock input)
          (by simpa only [size_firstBlock] using hwpadded)
        simpa only [size_firstBlock] using hb
    obtain ⟨z, hz⟩ := Long.run hlp
    obtain ⟨k, hk⟩ := hz.advances
    have hwsp' : stackPtr w = stackPtr s := hwa'.read (n := 64) (r := 4) (by
      simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
    have hchanges' : Kind.digest.changes w = Kind.digest.changes s := by
      simp only [Kind.changes, Kind.localChanges, hwsp']
    have hza : AgreesExcept (Kind.digest.changes s) s z := by
      have hat := hz.agrees
      rw [hchanges'] at hat
      exact (hwa'.trans hat).mono (by simp)
    refine complete ⟨_, hrun.trans hk⟩ hza hz.ready hz.code hz.storage hz.rip hz.position hz.blocks ?_ ?_
    · simpa only [ite_eq_right hshort] using hz.zeroPrefix
    · simpa only [paddedBuffer, ite_eq_right hshort] using hz.buffer

end Md5.Proofs.Buffered.Finalize
