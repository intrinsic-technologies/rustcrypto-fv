import Md5.Proofs.Buffered.Invariant
import Md5.Proofs.RFC1321.Padding
import X86Proofs.Program.ReadWrite.Bytes

namespace Md5.Proofs.Buffered.Finalize

open X86 X86.Machine X86Proofs Md5.Spec

abbrev zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

theorem size_zeroBytes (n : Nat) : (zeroBytes n).size = n := by
  simp [ByteArray.size]

def firstBlock (message : ByteArray) : ByteArray :=
  tailBytes message ++ ⟨#[128]⟩ ++ zeroBytes (63 - message.size % 64)

def lastBlock (message : ByteArray) : ByteArray :=
  (if message.size % 64 < 56 then (firstBlock message).extract 0 56 else zeroBytes 56) ++
    RFC1321.lengthBytes message.size

theorem size_firstBlock (message : ByteArray) : (firstBlock message).size = 64 := by
  unfold firstBlock
  rw [ByteArray.size_append, ByteArray.size_append, size_tailBytes]
  rw [size_zeroBytes]
  change message.size % 64 + 1 + (63 - message.size % 64) = 64
  omega

theorem size_lastBlock (message : ByteArray) : (lastBlock message).size = 64 := by
  unfold lastBlock
  rw [ByteArray.size_append, RFC1321.size_lengthBytes]
  split
  · rw [ByteArray.size_extract, size_firstBlock]
    decide
  · rfl

theorem getElem_firstBlock_tail (message : ByteArray) (i : Nat)
    (hi : i < message.size % 64) :
    (firstBlock message)[i]'(by rw [size_firstBlock]; omega) =
      (tailBytes message)[i]'(by rw [size_tailBytes]; exact hi) := by
  unfold firstBlock
  rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append, size_tailBytes]
      change i < message.size % 64 + 1
      omega),
    ByteArray.getElem_append_left (by rw [size_tailBytes]; exact hi)]

theorem getElem_firstBlock_padding (message : ByteArray) :
    (firstBlock message)[message.size % 64]'(by rw [size_firstBlock]; omega) = 128 := by
  unfold firstBlock
  rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append, size_tailBytes]
      change message.size % 64 < message.size % 64 + 1
      omega),
    ByteArray.getElem_append_right (by rw [size_tailBytes]; exact Nat.le_refl _)]
  simp only [size_tailBytes, Nat.sub_self]
  rfl

theorem getElem_firstBlock_zero (message : ByteArray) (i : Nat)
    (hp : message.size % 64 < i) (hi : i < 64) :
    (firstBlock message)[i]'(by rw [size_firstBlock]; exact hi) = 0 := by
  unfold firstBlock
  rw [ByteArray.getElem_append_right (by
      rw [ByteArray.size_append, size_tailBytes]
      change message.size % 64 + 1 ≤ i
      omega)]
  simp only [zeroBytes, ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

theorem getElem_lastBlock_prefix (message : ByteArray) (i : Nat) (hi : i < 56) :
    (lastBlock message)[i]'(by rw [size_lastBlock]; omega) =
      if message.size % 64 < 56 then (firstBlock message)[i]!
      else 0 := by
  unfold lastBlock
  split
  · rw [ByteArray.getElem_append_left (by rw [ByteArray.size_extract, size_firstBlock]; omega),
      ByteArray.getElem_extract]
    simp only [Nat.zero_add, getElem!_pos (firstBlock message) i (by rw [size_firstBlock]; omega)]
  · rw [ByteArray.getElem_append_left (by exact hi)]
    change (Array.replicate 56 (0 : UInt8))[i] = 0
    exact Array.getElem_replicate (by simpa using hi)

theorem getElem_lastBlock_length (message : ByteArray) (i : Nat) (hi : i < 8) :
    (lastBlock message)[56 + i]'(by rw [size_lastBlock]; omega) =
      (RFC1321.lengthBytes message.size)[i]'(by rw [RFC1321.size_lengthBytes]; exact hi) := by
  have hprefix : (if message.size % 64 < 56 then (firstBlock message).extract 0 56
      else zeroBytes 56).size = 56 := by
    split
    · rw [ByteArray.size_extract, size_firstBlock]
      decide
    · rfl
  unfold lastBlock
  rw [ByteArray.getElem_append_right (by rw [hprefix]; omega)]
  simp only [hprefix, Nat.add_sub_cancel_left]

theorem getElem_lengthBytes_storedByte (n i : Nat) (hi : i < 8) :
    (RFC1321.lengthBytes n)[i]'(by rw [RFC1321.size_lengthBytes]; exact hi) =
      storedByte (BitVec.ofNat 64 (n * 8)) i := by
  rw [RFC1321.getElem_lengthBytes n i hi]
  simp only [storedByte, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem paddedTail_eq (message : ByteArray) :
    RFC1321.paddedTail message =
      tailBytes message ++ RFC1321.paddingBytes message.size ++ RFC1321.lengthBytes message.size := rfl

theorem getElem_paddedTail_tail (message : ByteArray) (i : Nat)
    (hi : i < message.size % 64) :
    (RFC1321.paddedTail message)[i]'(by rw [RFC1321.size_paddedTail]; split <;> omega) =
      (tailBytes message)[i]'(by rw [size_tailBytes]; exact hi) := by
  simp only [paddedTail_eq]
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, size_tailBytes]; omega),
    ByteArray.getElem_append_left (by rw [size_tailBytes]; exact hi)]

theorem getElem_paddedTail_padding (message : ByteArray) :
    (RFC1321.paddedTail message)[message.size % 64]'
      (by rw [RFC1321.size_paddedTail]; split <;> omega) = 128 := by
  simp only [paddedTail_eq]
  rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append, size_tailBytes, RFC1321.size_paddingBytes]
      omega), ByteArray.getElem_append_right (by rw [size_tailBytes]; exact Nat.le_refl _)]
  simp only [size_tailBytes, Nat.sub_self, RFC1321.getElem_paddingBytes_zero]

theorem getElem_paddedTail_zero (message : ByteArray) (i : Nat)
    (hlo : message.size % 64 < i)
    (hhi : i < message.size % 64 + 1 + RFC1321.paddingZeroBytes message.size) :
    (RFC1321.paddedTail message)[i]'
      (by simp only [RFC1321.paddedTail, ByteArray.size_append, ByteArray.size_extract,
        RFC1321.size_paddingBytes, RFC1321.size_lengthBytes]; omega) = 0 := by
  simp only [paddedTail_eq]
  rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append, size_tailBytes, RFC1321.size_paddingBytes]
      omega),
    ByteArray.getElem_append_right (by rw [size_tailBytes]; omega)]
  have he : i - (tailBytes message).size = (i - message.size % 64 - 1) + 1 := by
    rw [size_tailBytes]; omega
  simp only [he]
  exact RFC1321.getElem_paddingBytes_succ _ _ (by omega)

theorem getElem_paddedTail_length (message : ByteArray) (i : Nat) (hi : i < 8) :
    (RFC1321.paddedTail message)[message.size % 64 + 1 +
      RFC1321.paddingZeroBytes message.size + i]'
      (by simp only [RFC1321.paddedTail, ByteArray.size_append, ByteArray.size_extract,
        RFC1321.size_paddingBytes, RFC1321.size_lengthBytes]; omega) =
      (RFC1321.lengthBytes message.size)[i]'(by rw [RFC1321.size_lengthBytes]; exact hi) := by
  simp only [paddedTail_eq]
  rw [ByteArray.getElem_append_right (by
      rw [ByteArray.size_append, size_tailBytes, RFC1321.size_paddingBytes]
      omega)]
  simp only [ByteArray.size_append, size_tailBytes, RFC1321.size_paddingBytes]
  congr 1
  omega


theorem paddedTail_long (message : ByteArray) (h : 56 ≤ message.size % 64) :
    RFC1321.paddedTail message = firstBlock message ++ lastBlock message := by
  have hz : RFC1321.paddingZeroBytes message.size = 63 - message.size % 64 + 56 := by
    rw [RFC1321.paddingZeroBytes_eq, ite_eq_right (by omega)]
    omega
  simp only [paddedTail_eq, firstBlock, lastBlock, ite_eq_right (by omega :
    ¬ message.size % 64 < 56), RFC1321.paddingBytes, hz]
  apply ByteArray.ext
  simp only [ByteArray.data_append, zeroBytes, ← Array.replicate_append_replicate, Array.append_assoc]

theorem paddedTail_short (message : ByteArray) (h : message.size % 64 < 56) :
    RFC1321.paddedTail message = lastBlock message := by
  have hz : message.size % 64 + 1 + RFC1321.paddingZeroBytes message.size = 56 := by
    rw [RFC1321.paddingZeroBytes_eq, ite_eq_left h]
    omega
  apply ByteArray.ext
  apply Array.ext
  · change (RFC1321.paddedTail message).size = (lastBlock message).size
    rw [RFC1321.size_paddedTail, size_lastBlock, ite_eq_left h]
  · intro i hi hj
    change (RFC1321.paddedTail message)[i] = (lastBlock message)[i]
    have hi64 : i < 64 := by change i < (lastBlock message).size at hj; rwa [size_lastBlock] at hj
    by_cases hip : i < 56
    · rw [getElem_lastBlock_prefix _ _ hip, ite_eq_left h,
        getElem!_pos _ _ (by rw [size_firstBlock]; exact hi64)]
      by_cases hit : i < message.size % 64
      · rw [getElem_paddedTail_tail _ _ hit, getElem_firstBlock_tail _ _ hit]
      · by_cases hie : i = message.size % 64
        · subst i
          rw [getElem_paddedTail_padding, getElem_firstBlock_padding]
        · rw [getElem_paddedTail_zero _ _ (by omega) (by omega),
            getElem_firstBlock_zero _ _ (by omega) hi64]
    · have hh : i = 56 + (i - 56) := by omega
      have hidx : i - 56 < 8 := by omega
      have hleft := getElem_paddedTail_length message (i - 56) hidx
      simp only [hz, ← hh] at hleft
      have hright := getElem_lastBlock_length message (i - 56) hidx
      simp only [← hh] at hright
      exact hleft.trans hright.symm

theorem messageDigest_short (message : ByteArray) (h : message.size % 64 < 56) :
    Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message) =
      (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (lastBlock message))).toBytes := by
  rw [RFC1321.messageDigest_bitsOfBytes_completeBlocks, paddedTail_short message h]
  rfl

theorem messageDigest_long (message : ByteArray) (h : 56 ≤ message.size % 64) :
    Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message) =
      (Standards.RFC.MD5.processBlocks
        (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
          (Standards.RFC.MD5.wordsOfBytes (firstBlock message)))
        (Standards.RFC.MD5.wordsOfBytes (lastBlock message))).toBytes := by
  rw [RFC1321.messageDigest_bitsOfBytes_completeBlocks, paddedTail_long message h,
    RFC1321.processBlocks_wordsOfBytes_append _ _ _ (by rw [size_firstBlock])]
  rfl


def paddedBuffer (message : ByteArray) : Standards.RFC.MD5.Buffer :=
  if message.size % 64 < 56 then absorbedBuffer message else
    Standards.RFC.MD5.processBlocks (absorbedBuffer message) (Standards.RFC.MD5.wordsOfBytes (firstBlock message))

theorem messageDigest_paddedBuffer (message : ByteArray) :
    Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message) =
      (Standards.RFC.MD5.processBlocks (paddedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (lastBlock message))).toBytes := by
  unfold paddedBuffer
  split
  · exact messageDigest_short message ‹_›
  · exact messageDigest_long message (by omega)


theorem firstBlock_bytes {m : Ram} {base : BitVec 64} (message : ByteArray)
    (hTail : Bytes m base (message.size % 64) (fun i ↦ (tailBytes message)[i]!))
    (hPadding : m[base + BitVec.ofNat 64 (message.size % 64)]? = some 128)
    (hZero : ∀ i, message.size % 64 < i → i < 64 →
      m[base + BitVec.ofNat 64 i]? = some 0) :
    Bytes m base 64 (fun i ↦ (firstBlock message)[i]!) := by
  intro i hi
  dsimp only
  rw [getElem!_pos (firstBlock message) i (by rw [size_firstBlock]; exact hi)]
  by_cases ht : i < message.size % 64
  · rw [getElem_firstBlock_tail _ _ ht]
    simpa only [getElem!_pos (tailBytes message) i (by rw [size_tailBytes]; exact ht)] using hTail i ht
  · by_cases he : i = message.size % 64
    · subst i
      rw [getElem_firstBlock_padding]
      exact hPadding
    · rw [getElem_firstBlock_zero _ _ (by omega) hi]
      exact hZero i (by omega) hi

theorem lastBlock_bytes {m : Ram} {base : BitVec 64} (message : ByteArray)
    (hPrefix : Bytes m base 56 (fun i ↦
      if message.size % 64 < 56 then (firstBlock message)[i]! else 0))
    (hLength : Bytes m (base + 56) 8 (storedByte (BitVec.ofNat 64 (message.size * 8)))) :
    Bytes m base 64 (fun i ↦ (lastBlock message)[i]!) := by
  intro i hi
  dsimp only
  rw [getElem!_pos (lastBlock message) i (by rw [size_lastBlock]; exact hi)]
  by_cases hp : i < 56
  · rw [getElem_lastBlock_prefix _ _ hp]
    exact hPrefix i hp
  · have hidx : i - 56 < 8 := by omega
    have hl := getElem_lastBlock_length message (i - 56) hidx
    simp only [show 56 + (i - 56) = i by omega,
      getElem_lengthBytes_storedByte _ _ hidx] at hl
    rw [hl]
    have he : base + BitVec.ofNat 64 i = base + 56 + BitVec.ofNat 64 (i - 56) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        show (56 : BitVec 64).toNat = 56 by rfl]
      omega
    rw [he]
    exact hLength (i - 56) hidx

theorem hasBytes_of_bytes {m : Ram} {base : BitVec 64} {bytes : ByteArray}
    (h : Bytes m base bytes.size (fun i ↦ bytes[i]!)) :
    (⟨base.toNat, bytes.size⟩ : Prelude.MemoryRegion).HasBytes m bytes := by
  refine ⟨rfl, ?_⟩
  intro i
  have hb := h i.val i.isLt
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    getElem!_pos bytes i.val i.isLt] using hb

end Md5.Proofs.Buffered.Finalize
