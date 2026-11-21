import ChaCha20Poly1305.Proofs.Decrypt.PrefixResult
import ChaCha20Poly1305.Proofs.Decrypt.Segment
import ChaCha20Poly1305.Proofs.Decrypt.Bytes

namespace ChaCha20Poly1305.Proofs.Decrypt.Prefix
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Spec.Program

set_option maxRecDepth 10000
set_option maxHeartbeats 450000

def initialKey (s : RamState) : Vector (BitVec 64) 4 := Vector.ofFn fun i =>
  memLoad s.external (s.regValue .rdi + BitVec.ofNat 64 (8*i.val)) 64

theorem sourceAway {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (hp : 0 < msg.size) :
    ((s.regValue .rcx).toNat + msg.size ≤ (s.regValue .rsp).toNat - 1136 ∨
      (s.regValue .rsp).toNat + 8 ≤ (s.regValue .rcx).toNat) ∧
    ((s.regValue .rcx).toNat + msg.size ≤ 3145728 ∨ 3145744 ≤ (s.regValue .rcx).toNat) := by
  let src := registerRegion s .rcx msg.size
  let stack := Stack.region s decrypt.minStackBytes
  let wr := writtenRegions decrypt s [key,nonce,aad,msg]
  have hs : src ∈ readRegions decrypt s [key,nonce,aad,msg] := by simp [src,readRegions,decrypt,inputRegion]
  have st : stack ∈ wr := by simp [wr,stack,writtenRegions]
  have al : allocatorStateRegion ∈ wr := by simp [wr,writtenRegions,decrypt]
  have hsplen : 1136 ≤ (s.regValue .rsp).toNat := hc.stackAvailable.2.2.1
  have hstpos : 0 < stack.size := by change 0 < _ + 8 - ((s.regValue .rsp).toNat - 1136); omega
  have ss := (apart_ends (hc.separation.2.1 _ st _ hs) hstpos hp).symm
  have sa := (apart_ends (hc.separation.2.1 _ al _ hs) (by decide) hp).symm
  simp only [src,registerRegion,stack,Stack.region, Stack.returnAddressBytes,decrypt,allocatorStateRegion] at ss sa
  exact ⟨by omega,sa⟩

theorem initial {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall decrypt s [key,nonce,aad,msg])
    (hp : 0 < msg.size) {ret : BitVec 64} (hret : (Stack.returnSlot s).Word64At s.external ret)
    (hrl : ret.toNat < userAddressLimit) (ho : ¬ InProgram ret)
    {cap : BitVec 64} (hcap : StackArgument s 2 cap) (_hcapLen : (heapRegion decrypt s).size ≤ cap.toNat) :
    let e := Short.envOf s msg cap
    let fr := Activation.ofEntry s decrypt.minStackBytes ret
    let c := {fr with rbp := 1,r12 := fr.r8+e.n,r13 := Short.limit e,rdx := 0}
    ∃ x : Inputs e, x.key = initialKey s ∧
      x.ciphertext = (Bytes.packed msg).setWidth (8*e.n.toNat) ∧
      (layout e x).Rel Lifted.fnCode (fr,c) (unitLoc .entry) (Lifted.lifted.locationOf .l1014c0 s) := by
  let e := Short.envOf s msg cap
  let fr := Activation.ofEntry s decrypt.minStackBytes ret
  let c := {fr with rbp := 1,r12 := fr.r8+e.n,r13 := Short.limit e,rdx := 0}
  let rsp := s.regValue .rsp
  have hf := callPre hc hret hrl ho
  have hlo : (s.regValue .rcx).toNat + msg.size < 2^32 := hc.inputsInMemory.2.2.2.1.1
  have hslot : StackArgument s 1 e.n := hc.lengthArgumentsMatchInputs.2.2.2.1
  have slotRead : Readable s.external (rsp + 16) 16 := by
    have hlow : rsp.toNat + 8 * (2 + 1) + 8 < 2^32 := hcap.1
    have h := Readable.of_word64At (mem := s.external) (start := rsp.toNat + 16)
      (n := 2) (vals := fun i => if i = 0 then e.n else cap) (by
        intro i hi
        rcases i with _ | i
        · simpa [stackArgumentSlot, rsp] using hslot.2
        · have ei : i = 0 := by omega
          subst i
          simpa [stackArgumentSlot, rsp, Nat.add_assoc] using hcap.2) (by omega)
    simpa [BitVec.ofNat_add] using h
  have sLen : memLoad s.external (rsp + 16) 64 = e.n := by
    simpa [stackArgumentSlot, rsp, BitVec.ofNat_add] using memLoad_of_word64At hslot.2
  have sCap : memLoad s.external (rsp + 24) 64 = cap := by
    simpa [stackArgumentSlot, rsp, BitVec.ofNat_add] using memLoad_of_word64At hcap.2
  have keyBytes : ValidInput s (registerRegion s .rdi 32) (key : ByteArray) := hc.inputsInMemory.1
  have keyRead : Readable s.external (s.regValue .rdi) 32 := by
    have h := Readable.of_hasBytes keyBytes.2 keyBytes.1
    rw [show (key : ByteArray).size = 32 from key.size_toArray] at h
    simpa [registerRegion] using h
  have hnat : e.n.toNat = msg.size := Nat.mod_eq_of_lt (by omega)
  have hsIn : ValidInput s (registerRegion s .rcx msg.size) msg := hc.inputsInMemory.2.2.2.1
  have srcRead : Readable s.external fr.rcx e.n.toNat := by
    rw [hnat]
    simpa [fr, Activation.ofEntry, registerRegion] using Readable.of_hasBytes hsIn.2 hsIn.1
  have heapWrite : Writable Lifted.fnCode s.external fr.r8 e.n.toNat := by
    rw [hnat]
    have he := Short.heap_region hc
    have hheap := (hc.heapInMemory rfl).1
    rw [he] at hheap
    apply Writable.of_avoids (region := registerRegion s .r8 msg.size) (forbidden := Forbidden)
      hheap.1 hheap.2 _ code_forbidden tables_forbidden (Nat.le_refl _) (Nat.le_refl _) hp
    rw [← he]
    apply hc.separation.2.2
    simp [writtenRegions, decrypt]
  obtain ⟨ks, ka, _, _⟩ := call_apart hc
  obtain ⟨st,al⟩ := sourceAway hc hp
  let x : Inputs e := ⟨initialKey s, (Bytes.packed msg).setWidth (8*e.n.toNat),
    by change _ + e.n.toNat ≤ _ ∨ _; rw [hnat]; exact st,
    by change _ + e.n.toNat ≤ _ ∨ _; rw [hnat]; exact al⟩
  refine ⟨x,rfl,rfl,rfl,⟨(),rfl,rfl,?_⟩,RamWriteFrame.refl _ _⟩
  rw [show (layout e x).atoms .entry (fr,c) () =
      Lifted.Decrypt.frameInfo.entryAtoms fr ++ (core e x).atoms .entry c fr () from rfl,
    Atom.all_append]
  refine ⟨hf.entryAtoms _ _,?_⟩
  change Atom.All _ _ _ ((Short.core e).atoms .entry c fr () ++ _)
  rw [Atom.all_append]
  refine ⟨⟨rfl,rfl,rfl,Activation.ofEntry_low_toNat,rfl,rfl,rfl,srcRead,heapWrite,allocator_writable hc,
    keyRead,slotRead,sLen,sCap,ks,ka,trivial⟩,?_⟩
  have keyAt (i : Fin 4) : (initialKey s)[i] = memLoad s.external (fr.rdi+BitVec.ofNat 64 (8*i.val)) 64 := Vector.getElem_ofFn _
  refine ⟨?_,(keyAt 1).symm,(keyAt 2).symm,(keyAt 3).symm,rfl,?_,trivial⟩
  · have he := (keyAt 0).symm
    change memLoad s.external (fr.rdi + 0#64) 64 = _ at he
    rw [BitVec.add_zero] at he
    exact he
  · change memLoad s.external (s.regValue .rcx) (8*e.n.toNat) = (Bytes.packed msg).setWidth (8*e.n.toNat)
    rw [hnat,BitVec.setWidth_eq]
    have he := Bytes.mem_packed (r := registerRegion s .rcx msg.size) hsIn.2
    change memLoad s.external (BitVec.ofNat 64 (s.regValue .rcx).toNat) _ = _ at he
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using he

end ChaCha20Poly1305.Proofs.Decrypt.Prefix
