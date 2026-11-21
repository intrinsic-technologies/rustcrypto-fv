import ChaCha20Poly1305.Proofs.DecryptInPlace.Regions

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable [b : Bindings] {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

set_option allowUnsafeReducibility true in
attribute [local reducible] Decrypt.Lifted.lifted

set_option maxRecDepth 4000 in
set_option maxHeartbeats 650000 in
theorem calleeABI (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32) (atCall : AtDetached s u (inPlacePacket s key nonce aad msg long small)) :
    Atom.All Decrypt.Lifted.fnCode (Decrypt.Lifted.lifted.locationOf .l1001f0 u).arguments u.external
      (Decrypt.Lifted.Fn1001f0.frameAt .l1001f0 (calleeFrame u)) := by
  have floor := stackFloor hc
  have sp := atCall.rsp
  have addr : (stackPtr u).toNat = (stackPtr s).toNat-80 := by rw [sp]; bv_omega
  have window := (stackWritable hc).of_frame (callFrame hc atCall)
  have retRead : Readable u.external (stackPtr u) 8 := window.readable.sub (by rw [sp]; bv_omega) (by bv_omega)
  have localWrite : Writable Decrypt.Lifted.fnCode u.external (stackPtr u-864) 864 :=
    window.sub (by rw [sp]; bv_omega) (by rw [sp]; bv_omega)
  have ar : (stackPtr s).toNat % 16 = 8 := hc.stackAvailable.2.2.2
  have got := Decrypt.Lifted.Fn1001f0.callSlots_loaded
    (show Decrypt.Lifted.rodataSection ∈ Extracted.programSections from .tail _ (.head _))
    (mem := u.external) (fun x hx => (atCall.track.code x hx).2)
  have get1 := got (0x2013a8,0x102dc0) (.head _)
  have get2 := got (0x2013e0,0x102d70) (.tail _ (.head _))
  have sep := imageApart hc (r:=Stack.region s decryptInPlace.minStackBytes)
    (by rw [written]; exact .tail _ (.head _))
    (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-1072); omega)
    (show Decrypt.Lifted.rodataSection ∈ Extracted.programSections from .tail _ (.head _))
    (lo:=0x2013a8) (hi:=0x2013e8) (by decide) (by decide +kernel) (by decide) (by decide)
  change (stackPtr s).toNat-1072+((stackPtr s).toNat+8-((stackPtr s).toNat-1072)) ≤ 0x2013a8 ∨
    0x2013e8 ≤ (stackPtr s).toNat-1072 at sep
  have room := Activation.ofEntry_low_toNat (s:=u) (stackBytes:=864) (ret:=0x1016bb)
  simp only [Decrypt.Lifted.Fn1001f0.frameAt,Decrypt.Lifted.Fn1001f0.frameAtG0,
    Decrypt.Lifted.Label.l1001f0,Atom.All,Atom.gpr,Atom.Holds,Lifted.locationOf]
  have reg (i : Fin Reg.count) : (Decrypt.Lifted.lifted.locationOf .l1001f0 u).arguments[i] =
      (Reg.ofIndex i).read u := Vector.getElem_ofFn _
  refine ⟨reg 4,(reg 22).trans (Reg.read_df_iff.2 ?_),reg 1,reg 2,reg 3,reg 5,reg 6,reg 7,
    reg 8,reg 9,reg 12,reg 13,reg 14,reg 15,reg 39,reg 50,reg 51,retRead,?_,
    by change 0x1016bb < 2^32; decide,localWrite,?_,?_,get1.1,get1.2,get2.1,get2.2,?_,trivial⟩
  · exact atCall.track.agrees.directionFlagClear (by simp [callChanges]) hc.directionFlagUnset
  · change memLoad u.external (stackPtr u) 64 = 0x1016bb
    simpa only [sp] using atCall.ret
  · change (calleeFrame u).low.toNat + 864 ≤ (stackPtr u).toNat
    change (calleeFrame u).low.toNat = (stackPtr u).toNat - 864 at room
    omega
  · change (stackPtr u).toNat % 16 = 8
    omega
  · change 0x201748 ≤ (stackPtr u).toNat ∨ (stackPtr u).toNat ≤ 0x2013a8
    omega

end ChaCha20Poly1305.Proofs.DecryptInPlace
