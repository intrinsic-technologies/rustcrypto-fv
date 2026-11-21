import Sha3.Spec.Keccak
import Sha3.Proofs.Sponge
import Sha3.Proofs.Keccak
import Standards.NIST.SHA3

namespace Sha3.Proofs.Absorption

open Standards.NIST.SHA3 Sha3.Proofs.Keccak

def bitBlock {b : Nat} (p : Array Bool) (r : Nat) (_hr : r ≤ b)
    (i : Fin (p.size / r)) : Vector Bool b :=
  Vector.ofFn fun j ↦ if hj : j.val < r then
    p[i.val * r + j.val]'(by
      have hblock : (i.val + 1) * r ≤ p.size :=
        Nat.le_trans (Nat.mul_le_mul_right r i.isLt) (Nat.div_mul_le_self p.size r)
      simp only [Nat.add_mul, Nat.one_mul] at hblock
      omega)
    else false

theorem bitBlock_eq_append {b : Nat} (p : Array Bool) (r : Nat) (hr : r ≤ b)
    (i : Fin (p.size / r)) :
    bitBlock p r hr i =
      ((Vector.ofFn fun j : Fin r ↦ p[i.val * r + j.val]'(by
        have hblock : (i.val + 1) * r ≤ p.size :=
          Nat.le_trans (Nat.mul_le_mul_right r i.isLt) (Nat.div_mul_le_self p.size r)
        simp only [Nat.add_mul, Nat.one_mul] at hblock
        omega)) ++ Vector.replicate (b - r) false).cast (by omega) := by
  apply Vector.ext
  intro j hj
  simp only [bitBlock, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_append,
    Vector.getElem_replicate]

theorem absorb_eq_foldl {b : Nat} (f : Vector Bool b → Vector Bool b)
    (pad : Standards.NIST.SHA3.PaddingRule) (r : Nat) (hr : 0 < r ∧ r < b) (n : Array Bool) :
    Standards.NIST.SHA3.absorb f pad r hr n =
      (Array.ofFn fun i : Fin ((n ++ pad.pad r n.size).size / r) ↦
        bitBlock (n ++ pad.pad r n.size) r (by omega) i).foldl
          (fun s block ↦ f (s.zipWith (· ^^ ·) block)) (Vector.replicate b false) := by
  unfold Standards.NIST.SHA3.absorb
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, Vector.toArray_ofFn]
  rw [← Array.foldl_map
    (f := fun block : Vector Bool r ↦
      (block ++ Vector.replicate (b - r) false).cast (by omega))
    (g := fun s block : Vector Bool b ↦ f (s.zipWith (· ^^ ·) block))]
  congr 1
  · rw [Array.map_ofFn]
    congr 1
    funext i
    exact (bitBlock_eq_append (n ++ pad.pad r n.size) r (by omega) i).symm
  · simp only [Array.size_map, Array.size_ofFn]

def laneBits (a : Lanes) : Vector Bool 1600 := (stateOfLanes a).toString

theorem getElem_laneBits (a : Lanes) (i : Nat) (hi : i < 1600) :
    (laneBits a)[i] = (a ⟨i / 64, by omega⟩).getLsbD (i % 64) := by
  simp only [laneBits, StateArray.toString, w, b, Vector.getElem_ofFn,
    StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW, stateOfLanes]
  congr 2
  apply Fin.ext
  change i / 64 % 5 + 5 * (i / 64 / 5) = i / 64
  omega

theorem laneBits_zero : laneBits (fun _ ↦ 0#64) = Vector.replicate 1600 false := by
  apply Vector.ext
  intro i hi
  rw [getElem_laneBits]
  simp

theorem laneBits_xor (a b : Lanes) :
    laneBits (fun i ↦ a i ^^^ b i) = (laneBits a).zipWith (· ^^ ·) (laneBits b) := by
  apply Vector.ext
  intro i hi
  simp only [getElem_laneBits, Vector.getElem_zipWith, BitVec.getLsbD_xor]

def blockLanes (bytes : ByteArray) (offset rate : Nat) : Lanes := fun lane ↦
  packLane fun z ↦
    let j := 8 * lane.val + z.val / 8
    if h : j < rate ∧ offset + j < bytes.size then
      (bytes.data[offset + j]'h.2).toBitVec.getLsbD (z.val % 8)
    else false

theorem getElem_laneBits_blockLanes (bytes : ByteArray) (offset rate i : Nat)
    (hi : i < 1600) :
    (laneBits (blockLanes bytes offset rate))[i] =
      if h : i / 8 < rate ∧ offset + i / 8 < bytes.size then
        (bytes.data[offset + i / 8]'h.2).toBitVec.getLsbD (i % 8)
      else false := by
  rw [getElem_laneBits]
  simp only [blockLanes, getLsbD_packLane _ ⟨i % 64, by omega⟩]
  have hdiv : 8 * (i / 64) + i % 64 / 8 = i / 8 := by omega
  have hmod : i % 64 % 8 = i % 8 := by omega
  simp only [hdiv, hmod]

theorem blockLanes_extract_byte (bytes : ByteArray) (offset rate : Nat)
    (lane : Fin 25) (j : Fin 8) :
    UInt8.ofBitVec ((blockLanes bytes offset rate lane).extractLsb' (8 * j.val) 8) =
      if h : 8 * lane.val + j.val < rate ∧ offset + (8 * lane.val + j.val) < bytes.size then
        bytes.data[offset + (8 * lane.val + j.val)]'h.2
      else 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [BitVec.getLsbD_extractLsb', hz, decide_true, Bool.true_and, blockLanes, getLsbD_packLane _ ⟨8 * j.val + z, by omega⟩]
  have hdiv : (8 * j.val + z) / 8 = j.val := by omega
  have hmod : (8 * j.val + z) % 8 = z := by omega
  simp only [hdiv, hmod]
  split <;> simp_all

theorem size_bytesToBits_div (bytes : ByteArray) (rate : Nat) :
    (bytesToBits bytes).size / (8 * rate) = bytes.size / rate := by
  rw [size_bytesToBits, Nat.mul_div_mul_left _ _ (by decide)]

theorem laneBits_blockLanes (bytes : ByteArray) (rate : Nat) (hr : rate ≤ 200)
    (i : Fin (bytes.size / rate)) :
    laneBits (blockLanes bytes (i.val * rate) rate) =
      bitBlock (bytesToBits bytes) (8 * rate) (by omega)
        (i.cast (size_bytesToBits_div bytes rate).symm) := by
  have hblock : (i.val + 1) * rate ≤ bytes.size :=
    Nat.le_trans (Nat.mul_le_mul_right rate i.isLt) (Nat.div_mul_le_self bytes.size rate)
  simp only [Nat.add_mul, Nat.one_mul] at hblock
  apply Vector.ext
  intro j hj
  simp only [getElem_laneBits_blockLanes, bitBlock, Vector.getElem_ofFn, Fin.val_cast]
  by_cases hjr : j < 8 * rate
  · have hjbyte : j / 8 < rate := by omega
    have hread : i.val * rate + j / 8 < bytes.size := by omega
    simp only [hjr, hjbyte, hread, and_self, ↓reduceDIte]
    rw [getElem_bytesToBits _ _ (by rw [Nat.mul_left_comm i.val 8 rate]; omega)]
    have hmul : i.val * (8 * rate) = 8 * (i.val * rate) := Nat.mul_left_comm _ _ _
    have hdiv : (i.val * (8 * rate) + j) / 8 = i.val * rate + j / 8 := by
      rw [hmul]
      omega
    have hmod : (i.val * (8 * rate) + j) % 8 = j % 8 := by
      rw [hmul]
      omega
    simp only [hdiv, hmod]
  · have hjbyte : ¬j / 8 < rate := by omega
    simp [hjr, hjbyte]

def absorbBlocks (permute : Lanes → Lanes) (rate : Nat) (bytes : ByteArray) : Lanes :=
  (Array.ofFn fun i : Fin (bytes.size / rate) ↦ blockLanes bytes (i.val * rate) rate).foldl
    (fun a block ↦ permute (fun i ↦ a i ^^^ block i)) (fun _ ↦ 0#64)

theorem laneBits_absorbBlocks (permute : Lanes → Lanes)
    (f : Vector Bool 1600 → Vector Bool 1600)
    (hperm : ∀ a, laneBits (permute a) = f (laneBits a))
    (bytes : ByteArray) (rate : Nat) (hr : rate ≤ 200) :
    laneBits (absorbBlocks permute rate bytes) =
      (Array.ofFn fun i : Fin ((bytesToBits bytes).size / (8 * rate)) ↦
        bitBlock (bytesToBits bytes) (8 * rate) (by omega) i).foldl
          (fun s block ↦ f (s.zipWith (· ^^ ·) block)) (Vector.replicate 1600 false) := by
  have hstep : ∀ a block : Lanes,
      f ((laneBits a).zipWith (· ^^ ·) (laneBits block)) =
        laneBits (permute (fun i ↦ a i ^^^ block i)) := by
    intro a block
    rw [hperm, laneBits_xor]
  rw [absorbBlocks, ← Array.foldl_map_hom (g := laneBits) (f := fun a block : Lanes ↦
    permute (fun i ↦ a i ^^^ block i))
    (f' := fun s block : Vector Bool 1600 ↦ f (s.zipWith (· ^^ ·) block)) hstep, laneBits_zero, Array.map_ofFn]
  congr 1
  · apply Array.ext
    · simp [size_bytesToBits_div]
    · intro i hi hj
      simp only [Array.getElem_ofFn]
      exact laneBits_blockLanes bytes rate hr ⟨i, by simpa using hi⟩
  · simp [size_bytesToBits_div]

def paddedBytes (rate : Nat) (input : ByteArray) (suffix : UInt8 := 0x06) : ByteArray :=
  input ++ ⟨Array.ofFn fun i : Fin (rate - input.size % rate) ↦
    ((if i.val = 0 then suffix else 0) : UInt8) ^^^
      ((if i.val + 1 = rate - input.size % rate then 0x80 else 0) : UInt8)⟩

def absorbSha3 (permute : Lanes → Lanes) (rate : Nat) (input : ByteArray)
    (suffix : UInt8 := 0x06) : Lanes :=
  absorbBlocks permute rate (paddedBytes rate input suffix)

theorem laneBits_absorbSha3 (permute : Lanes → Lanes)
    (f : Vector Bool 1600 → Vector Bool 1600)
    (hperm : ∀ a, laneBits (permute a) = f (laneBits a))
    (rate : Nat) (hr : 0 < rate ∧ rate < 200) (input : ByteArray)
    (suffix : UInt8 := 0x06) (bits : Array Bool := #[false, true])
    (hpad : (bytesToBits input ++ bits) ++
      pad101.pad (8 * rate) (bytesToBits input ++ bits).size =
        bytesToBits (paddedBytes rate input suffix) := by
          apply Padding.sha3_paddedMessage_eq_bytesToBits; omega) :
    laneBits (absorbSha3 permute rate input suffix) =
      Standards.NIST.SHA3.absorb f pad101 (8 * rate) (by omega)
        (bytesToBits input ++ bits) := by
  rw [absorbSha3, laneBits_absorbBlocks permute f hperm _ rate (by omega), absorb_eq_foldl]
  rw [hpad]

def digestLanes (a : Lanes) (n : Nat) (hn : n ≤ 200) : Digest n :=
  Vector.ofFn fun i ↦ UInt8.ofBitVec
    ((a ⟨i.val / 8, by omega⟩).extractLsb' (8 * (i.val % 8)) 8)

theorem digestLanes_eq_ofBits_trunc (a : Lanes) (n : Nat) (hn : n ≤ 200) :
    digestLanes a n hn = Digest.ofBits (trunc (laneBits a) (8 * n) (by omega)) := by
  apply Vector.ext
  intro i hi
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [digestLanes, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec,
    BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [getLsbD_digest_ofBits _ i j hi hj]
  simp only [trunc, Vector.getElem_ofFn]
  rw [getElem_laneBits]
  have hdiv : (8 * i + j) / 64 = i / 8 := by omega
  have hmod : (8 * i + j) % 64 = 8 * (i % 8) + j := by omega
  simp only [hdiv, hmod]

theorem digestLanes_absorbSha3 (permute : Lanes → Lanes)
    (f : Vector Bool 1600 → Vector Bool 1600)
    (hperm : ∀ a, laneBits (permute a) = f (laneBits a))
    (rate : Nat) (hr : 0 < rate ∧ rate < 200) (input : ByteArray)
    (n : Nat) (hn : n ≤ rate)
    (suffix : UInt8 := 0x06) (bits : Array Bool := #[false, true])
    (hpad : (bytesToBits input ++ bits) ++
      pad101.pad (8 * rate) (bytesToBits input ++ bits).size =
        bytesToBits (paddedBytes rate input suffix) := by
          apply Padding.sha3_paddedMessage_eq_bytesToBits; omega) :
    digestLanes (absorbSha3 permute rate input suffix) n (by omega) =
      Digest.ofBits (sponge f pad101 (8 * rate) (by omega)
        (bytesToBits input ++ bits) (8 * n)) := by
  rw [digestLanes_eq_ofBits_trunc,
    laneBits_absorbSha3 permute f hperm rate hr input suffix bits hpad,
    sponge_eq_trunc_absorb f pad101 (8 * rate) (by omega) _ (8 * n) (by omega)]

theorem digestLanes_sha3_224 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 144 input) 28 (by decide) =
      Digest.ofBits (SHA3_224 (bytesToBits input)) :=
  digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
    144 (by decide) input 28 (by decide)

theorem digestLanes_sha3_256 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 136 input) 32 (by decide) =
      Digest.ofBits (SHA3_256 (bytesToBits input)) :=
  digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
    136 (by decide) input 32 (by decide)

theorem digestLanes_sha3_384 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 104 input) 48 (by decide) =
      Digest.ofBits (SHA3_384 (bytesToBits input)) :=
  digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
    104 (by decide) input 48 (by decide)

theorem digestLanes_sha3_512 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 72 input) 64 (by decide) =
      Digest.ofBits (SHA3_512 (bytesToBits input)) :=
  digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
    72 (by decide) input 64 (by decide)

theorem size_paddedBytes (rate : Nat) (input : ByteArray) (hr : 0 < rate) (suffix : UInt8 := 0x06) :
    (paddedBytes rate input suffix).size = (input.size / rate + 1) * rate := by
  rw [paddedBytes, ByteArray.size_append]
  simp only [ByteArray.size, Array.size_ofFn]
  change input.size + (rate - input.size % rate) = (input.size / rate + 1) * rate
  have hmod := Nat.mod_lt input.size hr
  have hdiv := Nat.div_add_mod input.size rate
  rw [Nat.mul_comm rate] at hdiv
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem size_paddedBytes_div (rate : Nat) (input : ByteArray) (hr : 0 < rate) (suffix : UInt8 := 0x06) :
    (paddedBytes rate input suffix).size / rate = input.size / rate + 1 := by
  rw [size_paddedBytes rate input hr suffix, Nat.mul_div_cancel _ hr]

theorem blockLanes_append_of_le (a b : ByteArray) (offset rate : Nat)
    (h : offset + rate ≤ a.size) :
    blockLanes (a ++ b) offset rate = blockLanes a offset rate := by
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [blockLanes, getLsbD_packLane _ ⟨z, hz⟩]
  by_cases hj : 8 * lane.val + z / 8 < rate
  · have ha : offset + (8 * lane.val + z / 8) < a.size := by omega
    have hab : offset + (8 * lane.val + z / 8) < (a ++ b).size := by
      rw [ByteArray.size_append]
      omega
    simp only [hj, ha, hab, and_self, ↓reduceDIte]
    simp only [ByteArray.data_append, Array.getElem_append_left ha]
  · simp [hj]

theorem absorbSha3_eq_completeBlocks (permute : Lanes → Lanes) (rate : Nat)
    (input : ByteArray) (hr : 0 < rate) (suffix : UInt8 := 0x06) :
    absorbSha3 permute rate input suffix =
      permute (fun i ↦ absorbBlocks permute rate input i ^^^
        blockLanes (paddedBytes rate input suffix) ((input.size / rate) * rate) rate i) := by
  have hblocks :
      (Array.ofFn fun i : Fin ((paddedBytes rate input suffix).size / rate) ↦
        blockLanes (paddedBytes rate input suffix) (i.val * rate) rate) =
      (Array.ofFn fun i : Fin (input.size / rate) ↦
        blockLanes input (i.val * rate) rate).push
          (blockLanes (paddedBytes rate input suffix) ((input.size / rate) * rate) rate) := by
    apply Array.ext
    · simp [size_paddedBytes_div rate input hr suffix]
    · intro i hi hj
      simp only [Array.size_ofFn] at hi
      rw [size_paddedBytes_div rate input hr suffix] at hi
      simp only [Array.getElem_ofFn, Array.getElem_push, Array.size_ofFn]
      by_cases hilt : i < input.size / rate
      · simp only [hilt, ↓reduceDIte]
        apply blockLanes_append_of_le
        have hblock : (i + 1) * rate ≤ input.size :=
          Nat.le_trans (Nat.mul_le_mul_right rate hilt)
            (Nat.div_mul_le_self input.size rate)
        simpa only [Nat.add_mul, Nat.one_mul] using hblock
      · have hiq : i = input.size / rate := by omega
        simp [hiq]
  simp only [absorbSha3, absorbBlocks]
  rw [hblocks, Array.foldl_push]

theorem getElem_paddedBytes_final (rate : Nat) (input : ByteArray) (hr : 0 < rate)
    (j : Nat) (hj : j < rate) (suffix : UInt8 := 0x06) :
    (paddedBytes rate input suffix).data[input.size / rate * rate + j]'(by
      change input.size / rate * rate + j < (paddedBytes rate input suffix).size
      rw [size_paddedBytes rate input hr suffix]
      simp only [Nat.add_mul, Nat.one_mul]
      omega) =
      ((if h : j < input.size % rate then
        input.data[input.size / rate * rate + j]'(by
          have hdiv := Nat.div_add_mod input.size rate
          rw [Nat.mul_comm rate] at hdiv
          change input.size / rate * rate + j < input.size
          omega)
      else 0) ^^^ ((if j = input.size % rate then suffix else 0) : UInt8)) ^^^
        ((if j + 1 = rate then 0x80 else 0) : UInt8) := by
  have hmod := Nat.mod_lt input.size hr
  have hdiv := Nat.div_add_mod input.size rate
  rw [Nat.mul_comm rate] at hdiv
  by_cases hrem : j < input.size % rate
  · have hread : input.size / rate * rate + j < input.data.size := by
      change input.size / rate * rate + j < input.size
      omega
    have hne : ¬j = input.size % rate := by omega
    have hlast : ¬j + 1 = rate := by omega
    simp only [paddedBytes, ByteArray.data_append, Array.getElem_append_left hread,
      hrem, ↓reduceDIte, hne, hlast, ↓reduceIte, UInt8.xor_zero]
  · have hread : input.data.size ≤ input.size / rate * rate + j := by
      change input.size ≤ input.size / rate * rate + j
      omega
    have hsub : input.size / rate * rate + j - input.data.size = j - input.size % rate := by
      change input.size / rate * rate + j - input.size = j - input.size % rate
      omega
    simp only [paddedBytes, ByteArray.data_append, Array.getElem_append_right hread,
      Array.getElem_ofFn, hsub, hrem, ↓reduceDIte, UInt8.zero_xor]
    have hfirst : j - input.size % rate = 0 ↔ j = input.size % rate := by omega
    have hlast : j - input.size % rate + 1 = rate - input.size % rate ↔ j + 1 = rate := by
      omega
    simp only [hfirst, hlast]

theorem getLsbD_blockLanes_final (rate : Nat) (input : ByteArray) (hr : 0 < rate)
    (lane : Fin 25) (z : Fin 64) (suffix : UInt8 := 0x06) :
    let j := 8 * lane.val + z.val / 8
    (blockLanes (paddedBytes rate input suffix) (input.size / rate * rate) rate lane).getLsbD z.val =
      if hj : j < rate then
        (((if h : j < input.size % rate then
          input.data[input.size / rate * rate + j]'(by
            have hdiv := Nat.div_add_mod input.size rate
            rw [Nat.mul_comm rate] at hdiv
            change input.size / rate * rate + j < input.size
            omega)
        else 0) ^^^ ((if j = input.size % rate then suffix else 0) : UInt8)) ^^^
          ((if j + 1 = rate then 0x80 else 0) : UInt8)).toBitVec.getLsbD (z.val % 8)
      else false := by
  dsimp only
  simp only [blockLanes, getLsbD_packLane]
  by_cases hj : 8 * lane.val + z.val / 8 < rate
  · have hread : input.size / rate * rate + (8 * lane.val + z.val / 8) <
        (paddedBytes rate input suffix).size := by
      rw [size_paddedBytes rate input hr suffix]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    simp only [hj, hread, and_self, ↓reduceDIte]
    rw [getElem_paddedBytes_final rate input hr _ hj suffix]
  · simp [hj]


theorem digestLanes_keccak224 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 144 input 0x01) 28 (by decide) =
      Digest.ofBits (Sha3.Spec.Keccak.keccak224 (bytesToBits input)) := by
  change _ = Digest.ofBits (sponge (keccakF 6) pad101 (8 * 144) (by decide) (bytesToBits input) (8 * 28))
  have h := digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
      144 (by decide) input 28 (by decide) 0x01 #[] (by
        simpa only [Array.append_empty, paddedBytes] using
          Padding.keccak_paddedMessage_eq_bytesToBits 144 input (by decide))
  simp only [Array.append_empty] at h
  exact h

theorem digestLanes_keccak256 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 136 input 0x01) 32 (by decide) =
      Digest.ofBits (Sha3.Spec.Keccak.keccak256 (bytesToBits input)) := by
  change _ = Digest.ofBits (sponge (keccakF 6) pad101 (8 * 136) (by decide) (bytesToBits input) (8 * 32))
  have h := digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
      136 (by decide) input 32 (by decide) 0x01 #[] (by
        simpa only [Array.append_empty, paddedBytes] using
          Padding.keccak_paddedMessage_eq_bytesToBits 136 input (by decide))
  simp only [Array.append_empty] at h
  exact h

theorem digestLanes_keccak384 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 104 input 0x01) 48 (by decide) =
      Digest.ofBits (Sha3.Spec.Keccak.keccak384 (bytesToBits input)) := by
  change _ = Digest.ofBits (sponge (keccakF 6) pad101 (8 * 104) (by decide) (bytesToBits input) (8 * 48))
  have h := digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
      104 (by decide) input 48 (by decide) 0x01 #[] (by
        simpa only [Array.append_empty, paddedBytes] using
          Padding.keccak_paddedMessage_eq_bytesToBits 104 input (by decide))
  simp only [Array.append_empty] at h
  exact h

theorem digestLanes_keccak512 (input : ByteArray) :
    digestLanes (absorbSha3 keccakLanes 72 input 0x01) 64 (by decide) =
      Digest.ofBits (Sha3.Spec.Keccak.keccak512 (bytesToBits input)) := by
  change _ = Digest.ofBits (sponge (keccakF 6) pad101 (8 * 72) (by decide) (bytesToBits input) (8 * 64))
  have h := digestLanes_absorbSha3 keccakLanes (keccakF 6) stateOfLanes_keccakLanes
      72 (by decide) input 64 (by decide) 0x01 #[] (by
        simpa only [Array.append_empty, paddedBytes] using
          Padding.keccak_paddedMessage_eq_bytesToBits 72 input (by decide))
  simp only [Array.append_empty] at h
  exact h

end Sha3.Proofs.Absorption
