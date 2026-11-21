import K256.Proofs.Ecdh.CallSite
import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Ecdh.Wrapper.AffineMemory
import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.Child
import K256.Proofs.Ecdh.LIR.EcdhDiffieHellman
import K256.Proofs.Common.Tactic
import K256.Proofs.Sec1.Serialize.Assemble.Memory

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
open Sec1.Serialize.Assemble (wordsAtOffset fourWordsAt)

private abbrev code := Extracted.programImage

private def copyScalarWords (m : Ram) (sp : BitVec 64) (w : Vector (BitVec 64) 4) : Ram :=
  memStore (memStore (memStore (memStore m (sp + 40) w[3]) (sp + 32) w[2]) (sp + 24) w[1]) (sp + 16) w[0]

private def copyPeerWords (m source : Ram) (sp ptr : BitVec 64) : Ram :=
  memStore
    (memStore
      (memStore
        (memStore
          (memStore m (sp + 80) (memLoad source (ptr + 32) 8))
          (sp + 72) (memLoad source (ptr + 24) 64))
        (sp + 64) (memLoad source (ptr + 16) 64))
      (sp + 56) (memLoad source (ptr + 8) 64))
    (sp + 48) (memLoad source ptr 64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
private theorem copyBlock {s : RamState} {a : Arguments} {m : Ram} {w : Vector (BitVec 64) 4}
    (state : Caller s a m) (rp : a[14] = ⟨64, s.regValue .rdx⟩)
    (win : Writable code m (localSp s - 3936) 10088)
    (input : Readable m (s.regValue .rdx) 33)
    (apart : (localSp s - 3936).toNat + 10088 ≤ (s.regValue .rdx).toNat ∨
      (s.regValue .rdx).toNat + 33 ≤ (localSp s - 3936).toNat)
    (words : WordsAt m (localSp s + 192) 64 w)
    (push : StoreOk code (copyPeerWords (copyScalarWords m (localSp s) w) m (localSp s) (s.regValue .rdx))
      (returnSlot s) 8 0x10181e 5) :
    let sp := localSp s
    let n := copyPeerWords (copyScalarWords m sp w) m sp (s.regValue .rdx)
    ∃ b : Arguments, program.runBlock (dialect code) ⟨.l1017b1, a, m⟩ =
      .call ⟨.l120f30, b, memStore n (returnSlot s) (0x101823 : BitVec 64)⟩ (callFrame .l101823 0x101823) ∧
      ChildRegisters s b ∧ b[3] = ⟨64, s.regValue .rdi⟩ ∧
      b[6] = ⟨64, sp + 48⟩ ∧ b[7] = ⟨64, sp + 344⟩ := by
  let sp := localSp s
  let ptr := s.regValue .rdx
  change Writable code m (sp - 3936) 10088 at win
  change Readable m ptr 33 at input
  change (sp - 3936).toNat + 10088 ≤ ptr.toNat ∨ ptr.toNat + 33 ≤ (sp - 3936).toNat at apart
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) state.rsp
  have peer : a[14].get 64 = ptr := congrArg (Value.get 64) rp
  have w0 := wordsAtOffset (sp := sp) (offset := 192) words 0 (by decide)
  have w1 := wordsAtOffset (sp := sp) (offset := 192) words 1 (by decide)
  have w2 := wordsAtOffset (sp := sp) (offset := 192) words 2 (by decide)
  have w3 := wordsAtOffset (sp := sp) (offset := 192) words 3 (by decide)
  change memLoad m (sp + 192) 64 = w[0] at w0
  change memLoad m (sp + 200) 64 = w[1] at w1
  change memLoad m (sp + 208) 64 = w[2] at w2
  change memLoad m (sp + 216) 64 = w[3] at w3
  have push' : StoreOk code (copyPeerWords (copyScalarWords m sp w) m sp ptr)
      (sp - 8) 8 0x10181e 5 := by
    rw [show sp - 8 = returnSlot s from localSp_sub_eight s]
    exact push
  refine ⟨?_, ?run, ?regs, ?post⟩
  case run =>
    cfg_eval [rsp, peer]
    segment_words [w0, w1, w2, w3]
    iterate 18
      refine Eq.trans (ite_eq_left ?_) ?_
      · slot_guard using code_l1017b1
    rw [ite_eq_left (by simpa only [copyPeerWords, copyScalarWords] using push')]
    rw [show sp - 8 = returnSlot s from localSp_sub_eight s]
    rfl
  case regs =>
    constructor
    · rfl
    · exact state.df
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact state.widths ⟨_, hi⟩ (by decide +revert)
    · exact state.mxcsr
    · exact state.ftw
    · exact state.fcw
  case post => exact ⟨state.output, rfl, rfl⟩

private theorem copyFrame {m : Ram} {sp ptr : BitVec 64} {w : Vector (BitVec 64) 4}
    (access : Writable code m (sp - 3936) 10088) :
    RamWriteFrame m (copyPeerWords (copyScalarWords m sp w) m sp ptr) [⟨(sp + 16).toNat, 65⟩] := by
  unfold copyPeerWords copyScalarWords
  have stack : Writable code m (sp - 8) 288 :=
    access.of_offsets (addr_sub sp 8) (addr_sub sp 3936) (by decide)
  iterate 9
    apply RamWriteFrame.memStore
    case hin =>
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Sec1.Serialize.Assemble.inStackRegionOffsets stack rfl rfl (by decide) (by decide)
  exact RamWriteFrame.refl _ _

private theorem scalarCopyAt (m : Ram) (sp ptr : BitVec 64) (w : Vector (BitVec 64) 4) :
    WordsAt (copyPeerWords (copyScalarWords m sp w) m sp ptr) (sp + 16) 64 w := by
  apply fourWordsAt <;>
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [copyPeerWords, copyScalarWords, reduceAddOffset, memLoad_memStore_same,
        memLoad_memStore_of_rangeApart]

private theorem peerCopyBytes (m : Ram) (sp ptr : BitVec 64) (w : Vector (BitVec 64) 4) :
    ∀ i < 33, memByte (copyPeerWords (copyScalarWords m sp w) m sp ptr)
      (sp + 48 + BitVec.ofNat 64 i) = memByte m (ptr + BitVec.ofNat 64 i) := by
  let n := copyPeerWords (copyScalarWords m sp w) m sp ptr
  have eq0 : memLoad n (sp + 48) 64 = memLoad m ptr 64 := by
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have eq1 : memLoad n (sp + 56) 64 = memLoad m (ptr + 8) 64 := by
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [n, copyPeerWords, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have eq2 : memLoad n (sp + 64) 64 = memLoad m (ptr + 16) 64 := by
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [n, copyPeerWords, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have eq3 : memLoad n (sp + 72) 64 = memLoad m (ptr + 24) 64 := by
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [n, copyPeerWords, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have eq4 : memLoad n (sp + 80) 8 = memLoad m (ptr + 32) 8 := by
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [n, copyPeerWords, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  intro i hi
  have chunk {off width : Nat} (eq : memLoad n (sp + 48 + BitVec.ofNat 64 off) width =
      memLoad m (ptr + BitVec.ofNat 64 off) width) (start : off ≤ i) (end_ : i < off + width / 8) :
      memByte n (sp + 48 + BitVec.ofNat 64 i) = memByte m (ptr + BitVec.ofNat 64 i) := by
    have h := memByte_of_memLoad_eq eq (i - off) (by omega)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le start] using h
  by_cases h0 : i < 8
  · exact memByte_of_memLoad_eq eq0 i h0
  by_cases h1 : i < 16
  · exact chunk (off := 8) (width := 64) (by
      rw [show sp + 48 + BitVec.ofNat 64 8 = sp + 56 by bv_omega]
      exact eq1) (by omega) (by omega)
  by_cases h2 : i < 24
  · exact chunk (off := 16) (width := 64) (by
      rw [show sp + 48 + BitVec.ofNat 64 16 = sp + 64 by bv_omega]
      exact eq2) (by omega) (by omega)
  by_cases h3 : i < 32
  · exact chunk (off := 24) (width := 64) (by
      rw [show sp + 48 + BitVec.ofNat 64 24 = sp + 72 by bv_omega]
      exact eq3) (by omega) (by omega)
  exact chunk (off := 32) (width := 8) (by
    rw [show sp + 48 + BitVec.ofNat 64 32 = sp + 80 by bv_omega]
    exact eq4) (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem copyToCall {s : RamState} {secret key : ByteArray} {d : Nat} {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (peerPtr : a[14] = ⟨64, s.regValue .rdx⟩) (scalar : ScalarAt s m 0xc0 d) :
    ∃ b n, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1017b1, a, m⟩, []⟩ ⟨⟨.l120f30, b, n⟩, [callFrame .l101823 0x101823]⟩ ∧
      ChildRegisters s b ∧ b[3] = ⟨64, s.regValue .rdi⟩ ∧
      b[6] = ⟨64, localSp s + 48⟩ ∧ b[7] = ⟨64, localSp s + 344⟩ ∧
      Scalar.Memory s n ∧ ScalarAt s n 0x10 d ∧
      (∀ i < 33, memByte n (localSp s + 48 + BitVec.ofNat 64 i) = key.data[i]?.getD 0) ∧
      memLoad n (returnSlot s) 64 = 0x101823 := by
  let sp := localSp s
  let ptr := s.regValue .rdx
  let stack := Stack.region s ecdhDiffieHellman.minStackBytes
  let src := registerRegion s .rdx 33
  let w := Generate.Generator.Multiply.scalarWords d
  have valid : ValidInput s src key := call.inputsInMemory.2.1
  have srcBound : ptr.toNat + 33 < 2^32 := valid.2.1
  have keySize : key.size = 33 := valid.2.2.1
  have separate : stack.Disjoint src :=
    (call.separation.2 stack (by simp [stack, writtenRegions, ecdhDiffieHellman])).2 src
      (by simp [src, inputRegions, ecdhDiffieHellman, inputRegion])
  obtain ⟨depth, low, spNat⟩ := Scalar.stack_geometry call
  have stackStart : (sp - 3936).toNat = (stackPtr s).toNat - 10088 := by
    rw [show sp - 3936 = stackPtr s - 10088 by change stackPtr s - 6152 - 3936 = _; bv_omega]
    exact Common.stackOffset call.stackAvailable (by decide)
  have separation := apart_of_disjoint separate
    (show 0 < stack.size by change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10088); omega)
    (show 0 < src.size by change 0 < 33; decide)
  have outside : Outside [stack] ptr 33 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact separation.symm
  change (stackPtr s).toNat - 10088 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10088)) ≤
    ptr.toNat ∨ ptr.toNat + 33 ≤ (stackPtr s).toNat - 10088 at separation
  have apart : (sp - 3936).toNat + 10088 ≤ ptr.toNat ∨ ptr.toNat + 33 ≤ (sp - 3936).toNat := by
    rw [stackStart]
    omega
  have input : Readable m ptr 33 := by
    have h := (Readable.of_hasBytes valid.2.2 valid.2.1).of_frame state.frame
    simpa only [keySize, src, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  have sourceByte (i : Nat) (hi : i < 33) : memByte m (ptr + BitVec.ofNat 64 i) = key.data[i]?.getD 0 := by
    have h := valid.2.2.2 ⟨i, by omega⟩
    change s.external[BitVec.ofNat 64 (ptr.toNat + i)]? = some key[i] at h
    rw [ofNat_toNat_add] at h
    have original := memByte_of_memLoad_eq (state.frame.memLoad_eq (k := 264) outside) i hi
    rw [original]
    simp only [memByte, PhysicalMemory.read, h, Option.getD_some]
    rw [Array.getElem?_eq_getElem (show i < key.data.size by change i < key.size; omega)]
    rfl
  let n := copyPeerWords (copyScalarWords m sp w) m sp ptr
  have win := state.toMemory.window call
  have copied := copyFrame (ptr := ptr) (w := w) win
  have slotNat (off : Nat) (ok : off ≤ 6152) :
      (sp + BitVec.ofNat 64 off).toNat = (stackPtr s).toNat - (6152 - off) :=
    (congrArg BitVec.toNat (localOffset s off ok)).trans
      (Common.stackOffset call.stackAvailable (show 6152 - off ≤ 10088 by omega))
  have memory : Scalar.Memory s n := state.toMemory.advance call copied (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (sp + 16).toNat ∧ (sp + 16).toNat + 65 ≤ _
    rw [show (sp + 16).toNat = (stackPtr s).toNat - 6136 from slotNat 16 (by decide)]
    omega)
  obtain ⟨push, pushed, frame, ret, live⟩ := callSite call memory 6160 (by decide) (by decide)
    0x1017b1 bytes_l1017b1 109 5 (fun x hx => Common.fnCode_subset_programImage x (code_l1017b1 x hx))
    (by decide +kernel) 0x101823
  change StoreOk code n (returnSlot s) 8 0x10181e 5 at push
  obtain ⟨b, run, regs, output, rsi, rdi⟩ := copyBlock state peerPtr win input apart scalar push
  refine ⟨b, _, .single (by simp only [Program.sem, Program.step, run, Transfer.next]; rfl),
    regs, output, rsi, rdi, pushed, ?_, ?_, ret⟩
  · exact WordsAt.of_frame (scalarCopyAt m sp ptr w) frame (by decide)
      (by rw [localOffset s 16 (by decide)];
          exact live 6136 32 (by decide) (by decide))
  · intro i hi
    have peerOutside : Outside [⟨(returnSlot s).toNat, 8⟩] (sp + 48) 33 := by
      rw [show sp + 48 = s.regValue .rsp - 6104 from localOffset s 48 (by decide)]
      exact live 6104 33 (by decide) (by decide)
    have hi' : i < 264 / 8 := hi
    exact (memByte_of_memLoad_eq (frame.memLoad_eq (k := 264) peerOutside) i hi').trans
      ((peerCopyBytes m sp ptr w i hi).trans (sourceByte i hi))

end K256.Proofs.Ecdh.Wrapper
