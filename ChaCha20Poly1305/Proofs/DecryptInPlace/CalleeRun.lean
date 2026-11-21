import ChaCha20Poly1305.Proofs.DecryptInPlace.Regions
import ChaCha20Poly1305.Proofs.Decrypt.DetachCorrect
import ChaCha20Poly1305.Proofs.Decrypt.Lifted

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable [b : Bindings] {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

attribute [local irreducible] Detached.Packet.good memLoad
  Standards.RFC.ChaCha20Poly1305.chacha20Encrypt Standards.RFC.ChaCha20Poly1305.poly1305Mac
  Standards.RFC.ChaCha20Poly1305.poly1305KeyGen

private theorem afterCallFrame {m : Ram} (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32)
    (atCall : AtDetached s u (inPlacePacket s key nonce aad msg long small))
    (writes : let p := inPlacePacket s key nonce aad msg long small
              RamWriteFrame u.external m ((calleeFrame u).region :: (if p.good then [⟨p.buf.toNat,p.n.toNat⟩] else []))) :
    RamWriteFrame s.external m (footprint s (inPlacePacket s key nonce aad msg long small).good) := by
  let p := inPlacePacket s key nonce aad msg long small
  let f := calleeFrame u
  have floor := stackFloor hc
  have initFrame := widenToScratch hc (by decide : 80 ≤ 1072) (callFrame hc atCall)
  have len : p.n.toNat = msg.size-16 := Nat.mod_eq_of_lt (by omega)
  have out : (⟨p.buf.toNat,p.n.toNat⟩ : MemoryRegion) = outputRegion decryptInPlace s := by
    rw [output hc,len]; rfl
  have rsp : f.rsp.toNat = (stackPtr s).toNat-80 := by
    change (stackPtr u).toNat = _
    rw [atCall.rsp]; bv_omega
  have low := Activation.ofEntry_low_toNat (s:=u) (ret:=0x1016bb) (stackBytes:=864)
  change f.low.toNat = f.rsp.toNat-864 at low
  have within : (scratch s).start ≤ f.region.start ∧ f.region.start+f.region.size ≤ (scratch s).start+(scratch s).size := by
    change (stackPtr s).toNat-1072 ≤ f.low.toNat ∧ f.low.toNat+(f.rsp.toNat-f.low.toNat) ≤ (stackPtr s).toNat-1072+1072
    rw [low,rsp]; omega
  have large := Hash.widen (big:=footprint s p.good) initFrame (by
    intro q h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩)
  apply large.trans writes
  intro q hq
  rcases List.mem_cons.mp hq with rfl|mem
  · exact ⟨_,.head _,within⟩
  · change q ∈ (if p.good then [⟨p.buf.toNat,p.n.toNat⟩] else []) at mem
    cases good : p.good
    · rw [good] at mem
      exact False.elim (List.not_mem_nil mem)
    · rw [good] at mem
      have e : q = ⟨p.buf.toNat,p.n.toNat⟩ := List.mem_singleton.mp mem
      refine ⟨q,?_,Nat.le_refl _,Nat.le_refl _⟩
      rw [e,out]
      exact .tail _ (.head _)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 500000 in
theorem calleeRun (hb : MachineRamUnitStrideDecodable b s) (hm : SupportedIntegerMachineState b.processor s)
    (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32) (atCall : AtDetached s u (inPlacePacket s key nonce aad msg long small))
    (atoms : let k := Detached.detachedFn (inPlacePacket s key nonce aad msg long small)
             Atom.All Decrypt.Lifted.fnCode (Decrypt.Lifted.lifted.locationOf .l1001f0 u).arguments u.external
               (k.abi (calleeFrame u) ++ k.pre (calleeFrame u))) :
    let p := inPlacePacket s key nonce aad msg long small
    ∃ n v, Advances (returnBoundary s) n u v ∧ AtEpilogue s v true p.good ∧
      (p.good = true → memLoad v.external p.buf (8*p.n.toNat) = p.dst) := by
  let p := inPlacePacket s key nonce aad msg long small
  let f := calleeFrame u
  let loc := Decrypt.Lifted.lifted.locationOf .l1001f0 u
  obtain ⟨o,exec,tag,post,frame⟩ := Detached.detachedCorrect p f loc rfl atoms (RamWriteFrame.refl _ _)
  have outside : CFG.ReturnOutside (returnBoundary s) Decrypt.Lifted.fnCode := by
    intro x hx eq
    exact boundaryOutside hc (eq ▸ ⟨x.2,loaded_text hx⟩)
  have sim := Decrypt.Lifted.simulation hb.stringStride Decrypt.Lifted.fnCode (fun _ h => h) outside
  obtain ⟨v,run,rel⟩ := sim.exec exec.sem
    (Rel.locationOf (P:=Decrypt.Lifted.lifted) (l:=.l1001f0) (readyOfTrack atCall.track hm) atCall.rip)
  have rip : v.RIP = 0x1016bb := (Value.eq_bits (Option.some.inj (tag.symm.trans rel.rip))).symm
  have notEnd : ¬ AtBoundary (returnBoundary s) v := fun h =>
    ChaCha20Poly1305.Proofs.Wrapper.code_ne_boundary (boundaryOutside hc) 0x16bb (by decide) (rip.symm.trans h.1)
  obtain ⟨z,adv,n,last⟩ := Semantics.exec_iff.mp run
  obtain ⟨k,toZ⟩ := (CFG.machine_reaches_iff (boundary:=returnBoundary s)).mp adv
  have segment := (last.resolve_right (fun ret => notEnd ret.atBoundary)).1
  obtain ⟨abi,crypto⟩ := (Atom.all_append _ _).1 post
  have done : Atom.All Decrypt.Lifted.fnCode o.values o.store (Decrypt.Lifted.Decrypt.frameInfo.doneAtoms f) := abi
  obtain ⟨pop,dir,kept,_⟩ := doneAtoms_retRel rel done rfl (by decide)
  have keep := savedOfAgrees atCall.track.agrees (by simp [callChanges])
  have saved : CalleeSavedRegistersUnchanged s v := by
    intro r hr
    rw [←keep r hr]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact Value.eq_bits (kept 3 (by decide))
    · exact Value.eq_bits (kept 5 (by decide))
    · exact Value.eq_bits (kept 12 (by decide))
    · exact Value.eq_bits (kept 13 (by decide))
    · exact Value.eq_bits (kept 14 (by decide))
    · exact Value.eq_bits (kept 15 (by decide))
  have above : stackPtr v = stackPtr s-72 := by
    have sp : stackPtr v = stackPtr u + 8 := Value.eq_bits pop
    rw [sp,atCall.rsp]; bv_omega
  have values := rel.regs 0 (by decide) (by decide +kernel)
  have st := crypto.1
  change o.values[0].get 8 = (if p.good then 0 else 1) at st
  rw [values] at st
  have allFrame : RamWriteFrame s.external v.external (footprint s p.good) := by
    rw [←rel.store]
    exact afterCallFrame hc long small atCall frame
  refine ⟨_,v,toZ.trans segment,⟨⟨rel.ready,rel.sse,rel.code⟩,rip,above,st,saved,dir,allFrame⟩,?_⟩
  intro good
  have bytes := crypto.2
  change Atom.All _ _ _ (if p.good then [.mem p.buf (8*p.n.toNat) p.dst] else []) at bytes
  rw [good] at bytes
  exact rel.store ▸ bytes.1


end ChaCha20Poly1305.Proofs.DecryptInPlace
