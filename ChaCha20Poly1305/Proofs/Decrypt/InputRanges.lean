import ChaCha20Poly1305.Proofs.Decrypt.PacketOf

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaCha20Poly1305.Spec.Program

def prefixWrites (s : RamState) (len : Nat) : List MemoryRegion :=
  [⟨(s.regValue .rsp).toNat-1136,1136⟩,⟨(s.regValue .r8).toNat,len⟩, allocatorStateRegion]

structure Away (s : RamState) (len b n : Nat) : Prop where
  stack : b+n≤(s.regValue .rsp).toNat-1136 ∨ (s.regValue .rsp).toNat+8≤b
  heap : b+n≤(s.regValue .r8).toNat ∨ (s.regValue .r8).toNat+len≤b
  allocator : b+n≤0x300000 ∨ 0x300010≤b

theorem readAway {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (nonempty : 0<msg.size) {r : MemoryRegion} (pos : 0<r.size)
    (rd : r ∈ readRegions decrypt s [key,nonce,aad,msg]) : Away s msg.size r.start r.size := by
  let st := Stack.region s decrypt.minStackBytes
  let ws := writtenRegions decrypt s [key,nonce,aad,msg]
  have hst : st ∈ ws := by simp [st,ws,writtenRegions]
  have ha : allocatorStateRegion ∈ ws := by simp [ws,writtenRegions,decrypt]
  have hh : heapRegion decrypt s ∈ ws := by simp [ws,writtenRegions,decrypt]
  have floor : 1136≤(s.regValue .rsp).toNat := hc.stackAvailable.2.2.1
  have stp : 0<st.size := by change 0<_+8-((s.regValue .rsp).toNat-1136); omega
  have heapSize : (heapRegion decrypt s).size=msg.size := by rw [Short.heap_region hc]; rfl
  have stSep := (apart_ends (hc.separation.2.1 _ hst _ rd) stp pos).symm
  have hSep := (apart_ends (hc.separation.2.1 _ hh _ rd) (heapSize ▸ nonempty) pos).symm
  have aSep := (apart_ends (hc.separation.2.1 _ ha _ rd) (by decide) pos).symm
  rw [Short.heap_region hc] at hSep
  refine ⟨?_,hSep,aSep⟩
  simp only [st,Stack.region,Stack.returnAddressBytes,decrypt] at stSep
  omega

theorem Away.load {s len b n fr m addr w} (h : Away s len b n)
    (frame : RamWriteFrame fr m (prefixWrites s len)) (floor : 1136≤(s.regValue .rsp).toNat) (low : b+n≤2^32)
    (l : b≤addr.toNat) (r : addr.toNat+w/8≤b+n) : memLoad m addr w=memLoad fr addr w := by
  obtain ⟨st,heap,alloc⟩ := h
  apply frame.memLoad_eq
  simp [Outside,prefixWrites,allocatorStateRegion]
  omega

theorem slotRead {s : RamState} {j : Nat} {v : BitVec 64} (h : StackArgument s j v) :
    Readable s.external (BitVec.ofNat 64 (stackArgumentSlot s j).start) 8 ∧
    memLoad s.external (BitVec.ofNat 64 (stackArgumentSlot s j).start) 64=v := by
  refine ⟨?_,memLoad_of_word64At h.2⟩
  apply Readable.of_word64At (n:=1) (vals:=fun _ => v)
  · intro i hi
    have e : i=0 := by omega
    subst i
    simpa only [stackArgumentSlot,Nat.mul_zero,Nat.add_zero] using h.2
  · have lo := h.1
    change (stackArgumentSlot s j).start+8<2^32 at lo
    omega

theorem relFrame {s : RamState} {ret : BitVec 64} (floor : 1136≤(s.regValue .rsp).toNat) :
    (Activation.ofEntry s 1136 ret).region=⟨(s.regValue .rsp).toNat-1136,1136⟩ := by
  simp [Activation.region,Activation.ofEntry]
  bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
