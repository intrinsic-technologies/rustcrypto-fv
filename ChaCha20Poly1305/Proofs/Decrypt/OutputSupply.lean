import ChaCha20Poly1305.Proofs.Decrypt.InputRanges
import ChaCha20Poly1305.Proofs.Decrypt.Deliver

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaCha20Poly1305.Spec.Program

set_option maxRecDepth 8000
set_option maxHeartbeats 500000

theorem bufferEq {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) : bufferRegion decrypt s=registerRegion s .r9 (msg.size-16) := by
  change registerRegion s .r9 (messageBytes decrypt s-16) = _
  rw [Short.message_length hc]

theorem outputSupply {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (nonempty : 0<msg.size) (needs : decrypt.needsOutput [key,nonce,aad,msg]=true)
    {m : Ram} (frame : RamWriteFrame s.external m (prefixWrites s msg.size)) (n : BitVec 64) (hn : n.toNat=msg.size-16) :
    ∃ cap, Delivery (s.regValue .rsp-136) (s.regValue .r9) (s.regValue .r8) n cap m := by
  let sp := s.regValue .rsp
  let dst := s.regValue .r9
  let src := s.regValue .r8
  let buf := bufferRegion decrypt s
  let st := Stack.region s decrypt.minStackBytes
  let heap := heapRegion decrypt s
  have floor : 1136≤sp.toNat := hc.stackAvailable.2.2.1
  have rs : writtenRegions decrypt s [key,nonce,aad,msg]=[buf,heap,allocatorStateRegion,st] := by
    unfold writtenRegions
    rw [ite_eq_left needs]; rfl
  have pair := hc.separation.1
  rw [rs] at pair
  have ds := (List.pairwise_cons.mp pair).1 st (by simp)
  have dh := (List.pairwise_cons.mp pair).1 heap (by simp)
  have stp : 0<st.size := by change 0<sp.toNat+8-(sp.toNat-1136); omega
  have hp : heap.size=msg.size := by rw [show heap=heapRegion decrypt s from rfl,Short.heap_region hc]; rfl
  have bs : buf=⟨dst.toNat,n.toNat⟩ := by dsimp only [buf]; rw [bufferEq hc,hn]; rfl
  obtain ⟨cap,arg,fit⟩ := hc.outputLengthArgumentCoversOutput needs _ rfl
  have fit' : n.toNat≤cap.toNat := by rw [output_region hc] at fit; exact hn ▸ fit
  have av := slotRead arg
  have ar : stackArgumentSlot s 3 ∈ readRegions decrypt s [key,nonce,aad,msg] := by unfold readRegions; rw [ite_eq_left needs]; simp [decrypt,argumentRegions]
  have away := readAway hc nonempty (r:=stackArgumentSlot s 3) (by change 0<8; decide) ar
  have bl : sp.toNat+32+8<2^32 := arg.1
  have addr : sp-136+168=BitVec.ofNat 64 (stackArgumentSlot s 3).start := by
    change sp-136+168=BitVec.ofNat 64 (sp.toNat+32)
    bv_omega
  have capM : memLoad m (sp-136+168) 64=cap := by
    apply (away.load frame floor (by exact Nat.le_of_lt arg.1) _ _).trans (addr ▸ av.2)
    · change sp.toNat+32≤(sp-136+168).toNat; bv_omega
    · change (sp-136+168).toNat+8≤sp.toNat+32+8; bv_omega
  refine ⟨cap,addr ▸ av.1.of_frame frame,capM,fit',?_,?_,?_,?_,?_⟩
  · intro pos
    have ok := hc.outputInMemory needs
    exact (Writable.of_avoids (code:=fnCode) (region:=buf) ok.1 ok.2
      (hc.separation.2.2 buf (rs ▸ .head _)) code_forbidden tables_forbidden
      (bs ▸ Nat.le_refl _) (bs ▸ Nat.le_refl _) pos).of_frame frame
  · intro pos
    have x := Short.written_apart_image hc (r:=buf) (rs ▸ .head _) (bs ▸ pos) (a:=0x100000) (len:=0x2def) (by decide)
      ⟨textSection,.head _,by decide,by decide⟩ (by decide)
    rw [bs] at x; exact x
  · intro pos
    have x := apart_ends ds (bs ▸ pos) stp
    rw [bs] at x
    change dst.toNat+n.toNat≤sp.toNat-1136 ∨ sp.toNat-1136+(sp.toNat+8-(sp.toNat-1136))≤dst.toNat at x
    change dst.toNat+n.toNat≤(sp-136).toNat-872 ∨ (sp-136).toNat+144≤dst.toNat
    bv_omega
  · intro pos
    have x := (apart_ends dh (bs ▸ pos) (hp ▸ nonempty)).symm
    rw [bs,show heap=heapRegion decrypt s from rfl,Short.heap_region hc] at x
    change src.toNat+msg.size≤dst.toNat ∨ dst.toNat+n.toNat≤src.toNat at x
    change src.toNat+n.toNat≤dst.toNat ∨ dst.toNat+n.toNat≤src.toNat
    omega
  · have x := away.heap
    change sp.toNat+32+8≤src.toNat ∨ src.toNat+msg.size≤sp.toNat+32 at x
    change src.toNat+n.toNat≤(sp-136).toNat+168 ∨ (sp-136).toNat+176≤src.toNat
    bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
