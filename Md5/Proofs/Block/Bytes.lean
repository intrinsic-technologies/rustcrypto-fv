import Md5.Proofs.Machine
import Md5.Proofs.RFC1321.Processing
import X86Proofs.Program.ReadWrite.Bytes

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem bytes_of_hasBytes {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes m bytes) :
    Bytes m (BitVec.ofNat 64 region.start) bytes.size (fun i ↦ bytes[i]!) := by
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [getElem!_pos bytes i hi] using h.2 ⟨i, hi⟩

theorem getElem_bytesOfWord (word : BitVec 32) (i : Nat) (hi : i < 4) :
    (Standards.RFC.MD5.bytesOfWord word)[i] = storedByte word i := by
  simp [Standards.RFC.MD5.bytesOfWord, storedByte, BitVec.toNat_ushiftRight]

theorem getElem_bufferBytes (buffer : Standards.RFC.MD5.Buffer) (word byte : Nat)
    (hw : word < 4) (hb : byte < 4) :
    buffer.toBytes[4 * word + byte] =
      storedByte (#v[buffer.A, buffer.B, buffer.C, buffer.D][word]) byte := by
  rw [Standards.RFC.MD5.Buffer.toBytes, Vector.getElem_flatten (by omega)]
  simp only [Vector.getElem_map,
    show (4 * word + byte) / 4 = word by omega,
    show (4 * word + byte) % 4 = byte by omega, getElem_bytesOfWord]

theorem buffer_word_bytes {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : Call.Compress.ValidBuffer s buffer) (word : Nat) (hw : word < 4) :
    Bytes s.external (s.regValue .rdi + BitVec.ofNat 64 (4 * word)) 4
      (storedByte (#v[buffer.A, buffer.B, buffer.C, buffer.D][word])) := by
  intro i hi
  have hb := h.2.2 ⟨4 * word + i, by
    simpa only [ByteArray.size, Vector.size_toArray] using
      (show 4 * word + i < 16 by omega)⟩
  change s.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat + (4 * word + i))]? =
    some buffer.toBytes[4 * word + i] at hb
  rw [getElem_bufferBytes buffer word i hw hi] at hb
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] using hb

theorem memLoad_buffer_A {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : Call.Compress.ValidBuffer s buffer) : memLoad s.external (s.regValue .rdi) 32 = buffer.A := by
  have hv := Bytes.memLoad (n := 32) (v := buffer.A)
    (buffer_word_bytes h 0 (by decide)) (by decide) (by decide)
  simpa using hv

theorem memLoad_buffer_B {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : Call.Compress.ValidBuffer s buffer) :
    memLoad s.external (s.regValue .rdi + 4) 32 = buffer.B := by
  simpa using (buffer_word_bytes h 1 (by decide)).memLoad (by decide) (by decide)

theorem memLoad_buffer_C {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : Call.Compress.ValidBuffer s buffer) :
    memLoad s.external (s.regValue .rdi + 8) 32 = buffer.C := by
  simpa using (buffer_word_bytes h 2 (by decide)).memLoad (by decide) (by decide)

theorem memLoad_buffer_D {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : Call.Compress.ValidBuffer s buffer) :
    memLoad s.external (s.regValue .rdi + 12) 32 = buffer.D := by
  simpa using (buffer_word_bytes h 3 (by decide)).memLoad (by decide) (by decide)

theorem buffer_bytes_of_words {m : Ram} {base : BitVec 64} {buffer : Standards.RFC.MD5.Buffer}
    (h : ∀ word, (hw : word < 4) →
      Bytes m (base + BitVec.ofNat 64 (4 * word)) 4
        (storedByte (#v[buffer.A, buffer.B, buffer.C, buffer.D][word]))) :
    Bytes m base 16 (fun i ↦ buffer.toBytes[i]!) := by
  intro i hi
  have hb := h (i / 4) (by omega) (i % 4) (by omega)
  rw [← getElem_bufferBytes buffer (i / 4) (i % 4) (by omega) (by omega)] at hb
  have he : 4 * (i / 4) + i % 4 = i := by omega
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, he, getElem!_pos buffer.toBytes i hi] using hb

theorem readOutput_of_bufferBytes {initial final : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (hA : Bytes final.external (initial.regValue .rdi) 4 (storedByte buffer.A))
    (hB : Bytes final.external (initial.regValue .rdi + 4) 4 (storedByte buffer.B))
    (hC : Bytes final.external (initial.regValue .rdi + 8) 4 (storedByte buffer.C))
    (hD : Bytes final.external (initial.regValue .rdi + 12) 4 (storedByte buffer.D)) :
    Compress.readOutput initial final = .ok buffer.toBytes := by
  have hb : Bytes final.external (initial.regValue .rdi) 16
      (fun i ↦ buffer.toBytes[i]!) := by
    apply buffer_bytes_of_words
    intro word hw
    have hc : word = 0 ∨ word = 1 ∨ word = 2 ∨ word = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · simpa using hA
    · simpa using hB
    · simpa using hC
    · simpa using hD
  apply readVector_of_hasBytes
  refine ⟨by simp [ByteArray.size, MemoryRegion.HasLength, Compress.outputRegion, registerRegion], ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have hbi := hb i.val hi
  change final.external[BitVec.ofNat 64 ((initial.regValue .rdi).toNat + i.val)]? =
    some buffer.toBytes[i.val]
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, getElem!_pos buffer.toBytes i.val hi] using hbi

theorem getElem_wordsOfBytes_eq (bytes : ByteArray) (word : Nat)
    (hw : word < (Standards.RFC.MD5.wordsOfBytes bytes).size) :
    (Standards.RFC.MD5.wordsOfBytes bytes)[word] =
      (((BitVec.ofNat 32 bytes[4 * word + 3]!.toNat <<< 8 |||
          BitVec.ofNat 32 bytes[4 * word + 2]!.toNat) <<< 8 |||
        BitVec.ofNat 32 bytes[4 * word + 1]!.toNat) <<< 8 |||
        BitVec.ofNat 32 bytes[4 * word]!.toNat) := by
  have hend : 4 * word + 4 ≤ bytes.size := by
    rw [Md5.Proofs.RFC1321.size_wordsOfBytes] at hw
    omega
  rw [Md5.Proofs.RFC1321.getElem_wordsOfBytes]
  have he : (bytes.extract (4 * word) (4 * word + 4)).data =
      #[bytes[4 * word]!, bytes[4 * word + 1]!, bytes[4 * word + 2]!,
        bytes[4 * word + 3]!] := by
    apply Array.ext
    · change (bytes.extract (4 * word) (4 * word + 4)).size = 4
      rw [ByteArray.size_extract]
      omega
    · intro i hi hi'
      have hi4 : i < 4 := hi'
      have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp (disch := omega) [ByteArray.data_extract, Array.getElem_extract,
          getElem!_pos, ByteArray.getElem_eq_getElem_data]
  rw [he]
  simp [BitVec.zero_shiftLeft, BitVec.zero_or]

theorem memLoad_wordsOfBytes {m : Ram} {base : BitVec 64} {bytes : ByteArray}
    (h : Bytes m base bytes.size (fun i ↦ bytes[i]!)) (word : Nat)
    (hw : word < (Standards.RFC.MD5.wordsOfBytes bytes).size) :
    memLoad m (base + BitVec.ofNat 64 (4 * word)) 32 =
      (Standards.RFC.MD5.wordsOfBytes bytes)[word] := by
  have hend : 4 * word + 4 ≤ bytes.size := by
    rw [Md5.Proofs.RFC1321.size_wordsOfBytes] at hw
    omega
  have hb (i : Nat) (hi : i < 4) :
      memByte m (base + BitVec.ofNat 64 (4 * word) + BitVec.ofNat 64 i) =
        bytes[4 * word + i]! := by
    change (m[base + BitVec.ofNat 64 (4 * word) + BitVec.ofNat 64 i]?).getD 0 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega)]
    rfl
  rw [getElem_wordsOfBytes_eq]
  simp only [memLoad, show List.range (32 / 8) = [0, 1, 2, 3] from rfl,
    List.foldl_cons, List.foldl_nil, hb 0 (by decide), hb 1 (by decide),
    hb 2 (by decide), hb 3 (by decide), Nat.reduceMul, Nat.add_zero,
    BitVec.shiftLeft_zero, BitVec.shiftLeft_or_distrib,
    ← BitVec.shiftLeft_add, Nat.reduceAdd]
  have hor (a b c d : BitVec 32) : 0 ||| a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
    simp only [BitVec.or_comm]
    ac_rfl
  exact hor _ _ _ _

theorem memLoad_validInput {s : RamState} {input : ByteArray}
    (h : Call.Compress.ValidInput s input) (word : Nat)
    (hw : word < (Standards.RFC.MD5.wordsOfBytes input).size) :
    memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (4 * word)) 32 =
      (Standards.RFC.MD5.wordsOfBytes input)[word] := by
  have hb := bytes_of_hasBytes h.2.2
  change Bytes s.external (BitVec.ofNat 64 (s.regValue .rsi).toNat) input.size
    (fun i ↦ input[i]!) at hb
  have hl := memLoad_wordsOfBytes hb word hw
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hl

theorem getElem_of_ofFnM_eq_ok {α ε : Type} {n : Nat}
    {f : Fin n → Except ε α} {values : Vector α n} (h : Vector.ofFnM f = .ok values) :
    ∀ i : Fin n, f i = .ok values[i] := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    rw [Vector.ofFnM_succ] at h
    cases hPrefix : Vector.ofFnM (fun i : Fin n ↦ f i.castSucc) with
    | error err => rw [hPrefix] at h; cases h
    | ok prior =>
      cases hLast : f (Fin.last n) with
      | error err => rw [hPrefix, hLast] at h; cases h
      | ok last =>
        have hv : prior.push last = values := by
          rw [hPrefix, hLast] at h
          exact Except.ok.inj h
        subst values
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hLast
        · intro j
          simpa using ih hPrefix j

theorem hasBytes_of_readVector {s : RamState} {region : MemoryRegion}
    {bytes : Vector UInt8 n} (hLength : region.HasLength n)
    (h : (Vector.ofFnM fun i : Fin n ↦
      match s.external[BitVec.ofNat 64 (region.start + i.val)]? with
      | some byte => Except.ok byte
      | none => Except.error (Machine.Fault.unmappedMemory
          (BitVec.ofNat 64 (region.start + i.val)))) = .ok bytes) :
    region.HasBytes s.external ⟨bytes.toArray⟩ := by
  refine ⟨by simpa only [ByteArray.size, Vector.size_toArray] using hLength, ?_⟩
  intro i
  have hi : i.val < n := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have hb := getElem_of_ofFnM_eq_ok h ⟨i.val, hi⟩
  cases hm : s.external[BitVec.ofNat 64 (region.start + i.val)]? with
  | none => simp [hm] at hb
  | some byte =>
    simp only [hm, Except.ok.injEq, Fin.getElem_fin] at hb
    simp only [hb, ByteArray.getElem_eq_getElem_data, Vector.getElem_toArray]

theorem readOutput_eq_ok_iff {initial final : RamState} {bytes : Vector UInt8 16} :
    Compress.readOutput initial final = .ok bytes ↔
      (Compress.outputRegion initial).HasBytes final.external ⟨bytes.toArray⟩ := by
  constructor
  · exact hasBytes_of_readVector rfl
  · exact readVector_of_hasBytes

end Md5.Proofs.Block
