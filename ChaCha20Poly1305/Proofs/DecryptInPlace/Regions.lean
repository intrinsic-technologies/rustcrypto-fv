import ChaCha20Poly1305.Proofs.DecryptInPlace.Interface
import ChaCha20Poly1305.Proofs.DecryptInPlace.CallRegions

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

theorem trackedFrame {cs : List Component} {n : Nat} (le : n ≤ (stackPtr s).toNat)
    (ag : AgreesExcept cs s u)
    (mem : ∀ c ∈ cs, c.isMem = false ∨ c = .mem (stackPtr s - BitVec.ofNat 64 n) n) :
    RamWriteFrame s.external u.external [⟨(stackPtr s).toNat-n,n⟩] := by
  refine ⟨?_,ag.grow⟩
  intro a outside
  apply ag.memory
  intro c hc cov
  rcases mem c hc with h | rfl
  · exact ChaCha20Poly1305.Proofs.Wrapper.nonmem_not_covers h a cov
  · obtain ⟨i,hi,rfl⟩ := cov
    have out := outside.2 _ (.head _)
    change _ ≤ (stackPtr s).toNat-n ∨ (stackPtr s).toNat-n+n ≤ _ at out
    bv_omega

theorem callFrame [Bindings] {p : Detached.Packet} (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (atCall : AtDetached s u p) :
    RamWriteFrame s.external u.external [⟨(stackPtr s).toNat-80,80⟩] := by
  apply trackedFrame (Nat.le_trans (by decide : 80 ≤ 1072) (stackFloor hc)) atCall.track.agrees
  simp [callChanges,Component.isMem]

theorem scratchWithin (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    ∀ x, (scratch s).Contains x → (Stack.region s decryptInPlace.minStackBytes).Contains x := by
  intro x h
  have floor := stackFloor hc
  change (stackPtr s).toNat - 1072 ≤ x ∧ x < (stackPtr s).toNat - 1072 + 1072 at h
  change (stackPtr s).toNat - 1072 ≤ x ∧ x < (stackPtr s).toNat - 1072 +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 1072))
  omega

theorem textSubset : ∀ x ∈ Decrypt.Lifted.fnCode, x ∈ Extracted.programImage := by
  intro x hx
  change x ∈ [Decrypt.Lifted.textSection, Decrypt.Lifted.rodataSection].flatMap ImageSection.toCodeMap
  change x ∈ [Decrypt.Lifted.textSection].flatMap ImageSection.toCodeMap at hx
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append] at *
  exact Or.inl hx

theorem readyOfTrack [b : Bindings] {cs : List Component}
    (track : ChaCha20Poly1305.Proofs.Wrapper.GTrack cs s u)
    (hm : SupportedIntegerMachineState b.processor s) : EntryReady Decrypt.Lifted.fnCode u :=
  ⟨track.ready,SupportedSSE.of_agreesExcept track.agrees hm.sse,track.code.mono textSubset⟩

theorem savedOfAgrees {cs : List Component} (ag : AgreesExcept cs s u)
    (untouched : ∀ n ∈ ([3,5,12,13,14,15] : List (BitVec 5)), Component.reg n ∉ cs) :
    CalleeSavedRegistersUnchanged s u := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ag.agree (.reg 3) (untouched 3 (by decide)) rfl
  · exact ag.agree (.reg 5) (untouched 5 (by decide)) rfl
  · exact ag.agree (.reg 12) (untouched 12 (by decide)) rfl
  · exact ag.agree (.reg 13) (untouched 13 (by decide)) rfl
  · exact ag.agree (.reg 14) (untouched 14 (by decide)) rfl
  · exact ag.agree (.reg 15) (untouched 15 (by decide)) rfl

theorem slotWriteValid {cs : List Component} {cap offset len : Nat}
    (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (capMem : Component.mem (stackPtr s-BitVec.ofNat 64 cap) cap ∈ cs)
    (within : len ≤ offset) (inside : offset ≤ cap) (bound : cap ≤ 1072) :
    ∀ x, (Component.mem (stackPtr s-BitVec.ofNat 64 offset) len).Covers x →
      (∃ d ∈ cs, d.Covers x) ∧ ¬ InProgram x :=
  fun _ cov => ⟨⟨_,capMem,slotFits within inside cov⟩,slotOutsideProgram hc within (Nat.le_trans inside bound) cov⟩

theorem returnSlotKept {accepted : Bool} (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (frame : RamWriteFrame s.external u.external (footprint s accepted)) :
    memLoad u.external (stackPtr s) 64 = (returnBoundary s).rip := by
  change memLoad _ _ _ = memLoad s.external (stackPtr s) 64
  have floor := stackFloor hc
  have top := stackTop hc
  apply memLoad_congr
  intro i hi
  change i < 8 at hi
  have addr : (stackPtr s + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat + i := by bv_omega
  simp only [memByte,PhysicalMemory.read]
  rw [frame.outside _ ⟨by omega,?_⟩]
  intro r hr
  rcases List.mem_cons.mp hr with rfl|hr
  · right
    change (stackPtr s).toNat-1072+1072 ≤ _
    omega
  · cases accepted
    · exact False.elim (List.not_mem_nil hr)
    · obtain rfl := List.mem_singleton.mp hr
      rw [output hc]
      change _+1 ≤ (s.regValue .rcx).toNat ∨ (s.regValue .rcx).toNat+(msg.size-16) ≤ _
      by_cases pos : 0 < msg.size
      · have := bufferStackApart hc pos
        omega
      · omega

theorem widenToScratch {d : Nat} (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (bound : d ≤ 1072)
    (fr : RamWriteFrame s.external u.external [⟨(stackPtr s).toNat-d,d⟩]) :
    RamWriteFrame s.external u.external [scratch s] := by
  have floor := stackFloor hc
  refine ⟨fun a outside => fr.outside _ ⟨outside.1,?_⟩,fr.present⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  have sep := outside.2 _ (.head _)
  change _ ≤ (stackPtr s).toNat-1072 ∨ (stackPtr s).toNat-1072+1072 ≤ _ at sep
  change _ ≤ (stackPtr s).toNat-d ∨ (stackPtr s).toNat-d+d ≤ _
  omega

theorem ciphertextParts (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32)
    (fr : RamWriteFrame s.external u.external [scratch s]) :
    let p := inPlacePacket s key nonce aad msg long small
    memLoad u.external p.buf (8*p.n.toNat) = p.src ∧
      memLoad u.external (p.buf+p.n) 64 = p.tag.extractLsb' 0 64 ∧
      memLoad u.external (p.buf+p.n+8) 64 = p.tag.extractLsb' 64 64 := by
  let buf := s.regValue .rcx
  have valid : ValidInput s (registerRegion s .rcx msg.size) msg := hc.inputsInMemory.2.2.2.1
  have low : buf.toNat+msg.size < 2^32 := valid.1
  have floor := stackFloor hc
  have away := bufferStackApart hc (by omega)
  have eq : memLoad u.external buf (8*msg.size) = memLoad s.external buf (8*msg.size) := by
    refine fr.memLoad_eq (a:=buf) (k:=8*msg.size) ⟨by omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change buf.toNat + 8*msg.size/8 ≤ (stackPtr s).toNat-1072 ∨ (stackPtr s).toNat-1072+1072 ≤ buf.toNat
    change buf.toNat + msg.size ≤ _ ∨ _ ≤ buf.toNat at away
    omega
  apply Decrypt.Wrapper.splitData msg long
  · exact Nat.mod_eq_of_lt (by omega)
  · change memLoad u.external buf (8*msg.size) = Bytes.packed msg
    rw [eq]
    simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Bytes.mem_packed valid.2

end ChaCha20Poly1305.Proofs.DecryptInPlace
