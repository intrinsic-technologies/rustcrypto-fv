import ChaCha20Poly1305.Proofs.Decrypt.Call

namespace ChaCha20Poly1305.Proofs.Decrypt.Short

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program

structure Env where
  n : BitVec 64
  cap : BitVec 64
  heap : BitVec 64
  src : BitVec 64
  sp : BitVec 64

def limit (e : Env) : BitVec 64 :=
  if (addSpec e.heap e.cap).2.CF then -1 else e.heap + e.cap

structure Geometry (e : Env) (bound : Nat := 16) : Prop where
  sz : 0 < e.n.toNat ∧ e.n.toNat < bound
  fits : e.n.toNat ≤ e.cap.toNat
  nonnull : e.heap ≠ 0
  low : e.heap.toNat + e.n.toNat ≤ 2^32
  srcLow : e.src.toNat + e.n.toNat ≤ 2^32
  sep : e.src.toNat + e.n.toNat ≤ e.heap.toNat ∨ e.heap.toNat + e.n.toNat ≤ e.src.toNat
  code : e.heap.toNat + e.n.toNat ≤ 0x100000 ∨ 0x102def ≤ e.heap.toNat
  rodata : e.heap.toNat + e.n.toNat ≤ 0x2013a8 ∨ 0x2013e8 ≤ e.heap.toNat
  state : e.heap.toNat + e.n.toNat ≤ 0x300000 ∨ 0x300010 ≤ e.heap.toNat
  stackHeap : e.heap.toNat + e.n.toNat ≤ e.sp.toNat - 1136 ∨ e.sp.toNat + 8 ≤ e.heap.toNat
  stackRO : e.sp.toNat + 8 ≤ 0x2013a8 ∨ 0x2013e8 ≤ e.sp.toNat - 1136
  stackCode : e.sp.toNat + 8 ≤ 0x100000 ∨ 0x102def ≤ e.sp.toNat - 1136
  stackState : e.sp.toNat + 8 ≤ 0x300000 ∨ 0x300010 ≤ e.sp.toNat - 1136
  stateSlots : e.sp.toNat + 32 ≤ 0x300000 ∨ 0x300010 ≤ e.sp.toNat + 16


theorem written_apart_image {s : RamState} {inputs : List ByteArray}
    (hc : ValidCall decrypt s inputs) {r : MemoryRegion} (hw : r ∈ writtenRegions decrypt s inputs)
    (hp : 0 < r.size) {a len : Nat} (hlen : 0 < len)
    (hs : ∃ sec ∈ Extracted.programSections,
      sec.address.toNat ≤ a ∧ a + len ≤ sec.address.toNat + sec.bytes.size)
    (hl : a+len ≤ 2^64) : r.start + r.size ≤ a ∨ a + len ≤ r.start := by
  apply apart_ends (q := ⟨a,len⟩) _ hp hlen
  intro x hr hx
  change a ≤ x ∧ x < a + len at hx
  obtain ⟨sec, hsec, h0, h1⟩ := hs
  have e : (BitVec.ofNat 64 x).toNat = x := Nat.mod_eq_of_lt (by have := hx.2; omega)
  have := hc.separation.2.2 r hw _ (show r.Contains (BitVec.ofNat 64 x).toNat by rwa [e])
  apply this
  left
  obtain ⟨b,hb⟩ := exists_mem_toCodeMap hsec (a := BitVec.ofNat 64 x)
    (by rw [e]; exact Nat.le_trans h0 hx.1) (by rw [e]; exact Nat.lt_of_lt_of_le hx.2 h1)
  exact ⟨b,fetch_image hb⟩

def envOf (s : RamState) (msg : ByteArray) (cap : BitVec 64) : Env :=
  ⟨BitVec.ofNat 64 msg.size, cap, s.regValue .r8, s.regValue .rcx, s.regValue .rsp⟩

theorem message_length {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall decrypt s [key, nonce, aad, msg]) :
    messageBytes decrypt s = msg.size := by
  have hslot : StackArgument s 1 (BitVec.ofNat 64 msg.size) := hc.lengthArgumentsMatchInputs.2.2.2.1
  have hsrc : (registerRegion s .rcx msg.size).Bounded := hc.inputsInMemory.2.2.2.1.1
  change (s.regValue .rcx).toNat + msg.size < 2^32 at hsrc
  change (match loadBytes s.external (BitVec.ofNat 64 (stackArgumentSlot s 1).start) 8 with
    | .ok value => value.toNat | .error _ => 0) = msg.size
  rw [hslot.2.2]
  exact Nat.mod_eq_of_lt (by omega)

theorem heap_region {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall decrypt s [key, nonce, aad, msg]) :
    heapRegion decrypt s = registerRegion s .r8 msg.size := by
  change registerRegion s .r8 (messageBytes decrypt s) = _
  rw [message_length hc]

theorem call_geometry_lt {bound : Nat} {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall decrypt s [key, nonce, aad, msg]) {cap : BitVec 64}
    (hcap : (heapRegion decrypt s).size ≤ cap.toNat) (hpos : 0 < msg.size) (hlen : msg.size < bound) :
    Geometry (envOf s msg cap) bound := by
  let hr := heapRegion decrypt s
  let st := Stack.region s decrypt.minStackBytes
  let src := registerRegion s .rcx msg.size
  let text := writtenRegions decrypt s [key, nonce, aad, msg]
  have hhr : hr ∈ text := by simp [text, writtenRegions, hr, decrypt]
  have hst : st ∈ text := by simp [text, writtenRegions, st]
  have hsrc : src ∈ readRegions decrypt s [key, nonce, aad, msg] := by
    simp [src, readRegions, decrypt, inputRegion]
  have hh : hr = registerRegion s .r8 msg.size := heap_region hc
  have hhpos : 0 < hr.size := hh ▸ hpos
  have hn := hc.heapNonzeroIfAllocating rfl hhpos
  have hhlo := (hc.heapInMemory rfl).1.1
  have hslo : src.Bounded := hc.inputsInMemory.2.2.2.1.1
  have hsplen : 1136 ≤ (s.regValue .rsp).toNat := hc.stackAvailable.2.2.1
  have hstpos : 0 < st.size := by change 0 < _ + 8 - ((s.regValue .rsp).toNat - 1136); omega
  have hsap := apart_ends (hc.separation.2.1 _ hhr _ hsrc) hhpos hpos
  have hpair : hr.Disjoint allocatorStateRegion ∧ hr.Disjoint st ∧ allocatorStateRegion.Disjoint st := by
    have hw := hc.separation.1
    unfold writtenRegions at hw
    split at hw
    · have hp := hw.tail
      exact ⟨(List.pairwise_cons.mp hp).1 _ (.head _), (List.pairwise_cons.mp hp).1 _ (.tail _ (.head _)),
        (List.pairwise_cons.mp hp.tail).1 _ (.head _)⟩
    · exact ⟨(List.pairwise_cons.mp hw).1 _ (.head _), (List.pairwise_cons.mp hw).1 _ (.tail _ (.head _)),
        (List.pairwise_cons.mp hw.tail).1 _ (.head _)⟩
  have hha := apart_ends hpair.1 hhpos (by decide)
  have hhs := apart_ends hpair.2.1 hhpos hstpos
  have hsa := apart_ends hpair.2.2 (by decide) hstpos
  have txt {r : MemoryRegion} (hw : r ∈ text) (hp : 0 < r.size) :=
    written_apart_image hc hw hp (a := 0x100000) (len := 0x2def) (by decide)
      ⟨Lifted.textSection,.head _,by decide,by decide⟩ (by decide)
  have ro {r : MemoryRegion} (hw : r ∈ text) (hp : 0 < r.size) :=
    written_apart_image hc hw hp (a := 0x2013a8) (len := 0x40) (by decide)
      ⟨Lifted.rodataSection,.tail _ (.head _),by decide,by decide⟩ (by decide)
  have h1 := txt hhr hhpos
  have h2 := txt hst hstpos
  have h3 := ro hhr hhpos
  have h4 := ro hst hstpos
  have h5 := (call_apart hc).2.2.2
  change hr.size ≤ _ at hcap
  change hr.Bounded at hhlo
  change hr.start ≠ 0 at hn
  rw [hh] at hcap hhlo hn h1 h3 hha hhs hsap
  have hnat : msg.size < 2^64 := by
    have low : (s.regValue .rcx).toNat + msg.size < 2^32 := hslo
    omega
  simp only [src, st, registerRegion, allocatorStateRegion, Stack.region, Stack.returnAddressBytes,
    MemoryRegion.Bounded, userAddressLimit, decrypt] at h1 h2 h3 h4 hha hhs hsa hsap hhlo hslo hcap hn
  constructor <;> simp only [envOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnat]
  · exact ⟨hpos, hlen⟩
  · exact hcap
  · intro he
    apply hn
    rw [he]; rfl
  · omega
  · omega
  · exact hsap.symm
  · exact h1
  · exact h3
  · exact hha
  · omega
  · omega
  · omega
  · omega
  · exact h5

theorem call_geometry {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall decrypt s [key, nonce, aad, msg]) {cap : BitVec 64}
    (hcap : (heapRegion decrypt s).size ≤ cap.toNat) (hpos : 0 < msg.size) (hlen : msg.size < 16) :
    Geometry (envOf s msg cap) := call_geometry_lt hc hcap hpos hlen

end ChaCha20Poly1305.Proofs.Decrypt.Short
