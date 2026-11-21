import ChaCha20Poly1305.Proofs.DecryptInPlace.Epilogue

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable [b : Bindings] {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

set_option maxRecDepth 2500 in
theorem shortEpilogue (hm : SupportedIntegerMachineState b.processor s)
    (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) (short : msg.size < 16)
    (start : AfterLength s u key msg.size) : AtEpilogue s u false false := by
  have ag := start.track.agrees
  refine ⟨readyOfTrack start.track hm,by simpa [short] using start.rip,
    start.rsp,?_,?_,?_,?_⟩
  · simp [start.status]
  · apply savedOfAgrees ag
    simp [prefixChanges]
  · exact ag.directionFlagClear (by simp [prefixChanges]) hc.directionFlagUnset
  · have floor := stackFloor hc
    have fr := trackedFrame (cs:=prefixChanges s) (n:=32) (by omega : 32 ≤ (stackPtr s).toNat) ag (by simp [prefixChanges,Component.isMem])
    exact widenToScratch hc (by decide) fr

theorem finish (hb : MachineRamUnitStrideDecodable b s)
    (hm : SupportedIntegerMachineState b.processor s)
    (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) {k : Nat} (advance : Advances (returnBoundary s) k s u)
    {norm acc : Bool} (resume : AtEpilogue s u norm acc) :
    ∃ fuel t, UniqueExecution s fuel t ∧ SupportedIntegerMachineState b.processor t ∧
      MachineRamUnitStrideDecodable b t ∧ CalleeSavedRegistersUnchanged s t ∧ DirectionFlagUnset t ∧
      t.external = u.external ∧ (t.regValue .rax).setWidth 32 = (if acc then 0 else 1) ∧
      (if acc then MemoryWriteFrame s t #v[outputRegion decryptInPlace s,Stack.region s decryptInPlace.minStackBytes]
       else MemoryWriteFrame s t #v[Stack.region s decryptInPlace.minStackBytes]) := by
  obtain ⟨_,t,ret,machine,saved,df,ready,mem,status⟩ := epilogue hc resume
  have entry := ChaCha20Poly1305.Proofs.Wrapper.entry_ready b hb hm hc.programLoaded
  obtain ⟨k,unique⟩ := (advance.returns ret).unique entry.ready.dataReady entry.ready.cpu.ss
    (ChaCha20Poly1305.Proofs.Wrapper.stack_return_readable hc.stackAvailable)
  refine ⟨k,t,unique,machine,⟨ready.ready.smrr,ready.ready.memoryType,hb.stringStride,ready.ready.features.lzcnt⟩,
    saved,df,mem,status,?_⟩
  have fr : RamWriteFrame s.external t.external (footprint s acc) := mem ▸ resume.frame
  cases acc
  · apply fr.memoryWriteFrame
    apply outside_of_within
    simpa [footprint] using scratchWithin hc
  · apply fr.memoryWriteFrame
    apply outside_of_within
    intro r hr
    simp only [footprint,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,by simp,scratchWithin hc⟩
    · exact ⟨_,by simp,fun _ h => h⟩

omit b in
theorem plaintext (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32) {t : RamState}
    (fr : RamWriteFrame s.external t.external (footprint s true))
    (data : let p := inPlacePacket s key nonce aad msg long small
            memLoad t.external p.buf (8*p.n.toNat) = p.dst) :
    readOutput decryptInPlace s t = .ok (inPlacePacket s key nonce aad msg long small).plain := by
  let p := inPlacePacket s key nonce aad msg long small
  have len : p.n.toNat = msg.size-16 := Nat.mod_eq_of_lt (by omega)
  have size : p.plain.size = p.n.toNat :=
    (ChaChaRound.encryptedSize p.key p.nonce 1 p.ct).trans p.length.symm
  have valid := hc.inputsInMemory.2.2.2.1
  have rd : Readable s.external (s.regValue .rcx) msg.size := by
    change ValidInput s (registerRegion s .rcx msg.size) msg at valid
    simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Readable.of_hasBytes valid.2 valid.1
  have out : Readable t.external p.buf p.plain.size :=
    (rd.of_frame fr).sub (Nat.le_refl _) (by change (s.regValue .rcx).toNat + p.plain.size ≤ (s.regValue .rcx).toNat + msg.size; omega)
  change memLoad t.external p.buf (8*p.n.toNat) = p.dst at data
  unfold Detached.Packet.dst Stream.encode at data
  rw [←size,BitVec.setWidth_eq] at data
  unfold readOutput
  rw [output hc,←len,←size]
  exact readRegion_of_bytes (Decrypt.Wrapper.bytesFromPacked out data)

end ChaCha20Poly1305.Proofs.DecryptInPlace
