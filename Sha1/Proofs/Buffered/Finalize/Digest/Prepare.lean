import Sha1.Proofs.Buffered.Finalize.Digest.Copy
import Sha1.Proofs.Buffered.Finalize.Digest.Normalize

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

theorem read_of_agrees {cs : List Component} {s t : RamState} {a : BitVec 64} {n : Nat}
    (h : AgreesExcept cs s t)
    (hd : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  change memLoad t.external a n = memLoad s.external a n
  apply memLoad_congr
  intro i hi
  change (t.external[a + BitVec.ofNat 64 i]?).getD 0 = (s.external[a + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte (hd i hi)]

theorem bytes_eq_of_read_eq {m m' : Ram} {a b : BitVec 64} {n : Nat}
    (ha : ∀ i < n / 8, (m[a + BitVec.ofNat 64 i]?).isSome)
    (hb : ∀ i < n / 8, (m'[b + BitVec.ofNat 64 i]?).isSome)
    (heq : memLoad m a n = memLoad m' b n) :
    ∀ i < n / 8, m[a + BitVec.ofNat 64 i]? = m'[b + BitVec.ofNat 64 i]? := by
  intro i hi
  rw [Bytes.of_memLoad ha i hi, Bytes.of_memLoad hb i hi, heq]

theorem covers_apart {base x : BitVec 64} {a len b count i : Nat}
    (hx : x = base + BitVec.ofNat 64 b + BitVec.ofNat 64 i) (hi : i < count)
    (ha : a + len ≤ 2^64) (hb : b + count ≤ 2^64) (hab : a + len ≤ b ∨ b + count ≤ a) :
    ¬ Component.Covers (.mem (base + BitVec.ofNat 64 a) len) x := by
  rintro ⟨j, hj, he⟩
  exact RangeApart.offsets base ha hb hab j hj i hi (he.symm.trans hx)

theorem covers_apart_zero {base x : BitVec 64} {len b count i : Nat}
    (hx : x = base + BitVec.ofNat 64 b + BitVec.ofNat 64 i) (hi : i < count)
    (ha : len ≤ 2^64) (hb : b + count ≤ 2^64) (hab : len ≤ b) :
    ¬ Component.Covers (.mem base len) x := by
  have h := covers_apart (a := 0) (len := len) hx hi (by omega) hb (.inl (by omega))
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

theorem offset_split (a : BitVec 64) (i k : Nat) (hk : k ≤ i) :
    a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i - k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hk]

structure Prepared [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x100112
  storage : Storage .digestCopy t
  df : DirectionFlagClear t.RFLAGS
  rsp : stackPtr t = stackPtr s
  tail : (⟨(stackPtr t + 24).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
    t.external (tailBytes message)
  state : (⟨(stackPtr t).toNat, 20⟩ : MemoryRegion).HasBytes t.external
    (absorbedStateBytes message)
  position : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  blocks : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  agrees : AgreesExcept (Kind.digestCopy.changes s) s t

theorem prepare [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .digestCopy boundary message s)
    (hstate : (Operand.reg 14 : Operand 64).read s = stackPtr s + 256) :
    ∃ t, Prepared boundary message s t := by
  obtain ⟨c, hc⟩ := copy_context hp
  have hcsp := hc.rsp
  have hc14 : (Operand.reg 14 : Operand 64).read c = stackPtr c + 256 := by
    rw [hc.agrees.read (n := 64) (r := 14) (by simp [copyChanges]), hstate, hcsp]
  obtain ⟨fuel, u, t, hrun, hr, hcode, hA, hB⟩ :=
    Normalize.run hc.ready hc.code hp.boundaryOutside ⟨hc.storage, hc.rip, hc14⟩
  have husp := Normalize.effectA_rsp hA
  have htsp := Normalize.effectB_rsp hB
  have hus : Storage .digestCopy u := hc.storage.of_agrees hA.agrees husp
  have hts : Storage .digestCopy t := hus.of_agrees hB.agrees htsp
  have hag : AgreesExcept (Kind.digestCopy.changes s) s t := by
    have h1 := hc.agreesDigest hp.toStorage
    have h2 := Normalize.effects_agrees hc.storage hA hB
    rw [Kind.changes_eq_of_rsp _ hcsp (by decide)] at h2
    exact (h1.trans h2).mono (by simp)
  have hwA := hA.writes
  have hwB := hB.writes
  simp only [Normalize.effectA, Normalize.effectB, Write.AllHold] at hwA hwB
  have h15 : (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read u :=
    hB.agrees.read (by simp [Normalize.effectB, Effect.components])
  have h12 : (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read u :=
    hB.agrees.read (by simp [Normalize.effectB, Effect.components])
  have hposition : (Operand.reg 15 : Operand 64).read t =
      BitVec.ofNat 64 (message.size % 64) := by
    have hpos := hc.absorbed.position
    change (Operand.mem (stackPtr c + 24 + 63) : Operand 8).read c = _ at hpos
    rw [BitVec.add_assoc] at hpos
    have hpos' : (Operand.mem (stackPtr c + 87) : Operand 8).read c =
        BitVec.ofNat 8 (message.size % 64) := by simpa using hpos
    rw [h15, hwA.1, hpos']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hblocks : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) := by
    have hb := hc.absorbed.blocks
    change (Operand.mem (stackPtr c + 24 + 64) : Operand 64).read c = _ at hb
    rw [BitVec.add_assoc] at hb
    rw [h12, hwA.2.1]
    exact hb
  have hrsp : stackPtr t = stackPtr c := htsp.trans husp
  rw [husp] at hwB
  have hAc : ∀ (x : BitVec 64) (comp : Component), comp ∈ (Normalize.effectA c).components →
      (∃ i, i < 64 ∧ (x = stackPtr c + BitVec.ofNat 64 24 + BitVec.ofNat 64 i ∨
        x = stackPtr c + BitVec.ofNat 64 256 + BitVec.ofNat 64 (i % 8) ∧ i < 8 ∨
        x = stackPtr c + BitVec.ofNat 64 264 + BitVec.ofNat 64 (i % 8) ∧ i < 8)) →
      ¬ comp.Covers x := by
    intro x comp hcomp hx hcov
    simp only [Normalize.effectA, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hcomp
    rcases hcomp with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov
    obtain ⟨i, hi, hx | ⟨hx, hi8⟩ | ⟨hx, hi8⟩⟩ := hx
    · exact covers_apart (a := 16) (len := 4) (b := 24) (count := 64) hx hi
        (by omega) (by omega) (by omega) hcov
    · exact covers_apart (a := 16) (len := 4) (b := 256) (count := 8) hx (Nat.mod_lt _ (by omega))
        (by omega) (by omega) (by omega) hcov
    · exact covers_apart (a := 16) (len := 4) (b := 264) (count := 8) hx (Nat.mod_lt _ (by omega))
        (by omega) (by omega) (by omega) hcov
  have hBc : ∀ (x : BitVec 64) (comp : Component), comp ∈ (Normalize.effectB u).components →
      (∃ i, i < 64 ∧ (x = stackPtr c + BitVec.ofNat 64 24 + BitVec.ofNat 64 i ∨
        x = stackPtr c + BitVec.ofNat 64 16 + BitVec.ofNat 64 (i % 4) ∧ i < 4)) →
      ¬ comp.Covers x := by
    intro x comp hcomp hx hcov
    simp only [Normalize.effectB, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hcomp
    rcases hcomp with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov
    all_goals rw [husp] at hcov
    all_goals obtain ⟨i, hi, hx | ⟨hx, hi4⟩⟩ := hx
    · exact covers_apart (a := 8) (len := 8) (b := 24) (count := 64) hx hi
        (by omega) (by omega) (by omega) hcov
    · exact covers_apart (a := 8) (len := 8) (b := 16) (count := 4) hx (Nat.mod_lt _ (by omega))
        (by omega) (by omega) (by omega) hcov
    · exact covers_apart_zero (len := 8) (b := 24) (count := 64) hx hi
        (by omega) (by omega) (by omega) hcov
    · exact covers_apart_zero (len := 8) (b := 16) (count := 4) hx (Nat.mod_lt _ (by omega))
        (by omega) (by omega) (by omega) hcov
  have E0 : (Operand.mem (stackPtr c + BitVec.ofNat 64 256) : Operand 64).read u =
      (Operand.mem (stackPtr c + BitVec.ofNat 64 256) : Operand 64).read c :=
    read_of_agrees hA.agrees fun i hi comp hcomp ↦ hAc _ comp hcomp
      ⟨i, by omega, .inr (.inl ⟨by rw [Nat.mod_eq_of_lt hi], hi⟩)⟩
  have E8 : (Operand.mem (stackPtr c + BitVec.ofNat 64 264) : Operand 64).read u =
      (Operand.mem (stackPtr c + BitVec.ofNat 64 264) : Operand 64).read c :=
    read_of_agrees hA.agrees fun i hi comp hcomp ↦ hAc _ comp hcomp
      ⟨i, by omega, .inr (.inr ⟨by rw [Nat.mod_eq_of_lt hi], hi⟩)⟩
  have E16 : (Operand.mem (stackPtr c + BitVec.ofNat 64 16) : Operand 32).read t =
      (Operand.mem (stackPtr c + BitVec.ofNat 64 16) : Operand 32).read u :=
    read_of_agrees hB.agrees fun i hi comp hcomp ↦ hBc _ comp hcomp
      ⟨i, by omega, .inr ⟨by rw [Nat.mod_eq_of_lt hi], hi⟩⟩
  have W0 : memLoad t.external (stackPtr c + BitVec.ofNat 64 0) 64 =
      memLoad c.external (stackPtr c + BitVec.ofNat 64 256) 64 := by
    have := hwB.2.2.2
    simp only [BitVec.add_zero]
    exact this.trans E0
  have W8 : memLoad t.external (stackPtr c + BitVec.ofNat 64 8) 64 =
      memLoad c.external (stackPtr c + BitVec.ofNat 64 264) 64 := hwB.2.2.1.trans E8
  have W16 : memLoad t.external (stackPtr c + BitVec.ofNat 64 16) 32 =
      memLoad c.external (stackPtr c + BitVec.ofNat 64 272) 32 := E16.trans hwA.2.2.2
  have hct : ∀ off len, off + len ≤ 280 → ∀ i < len,
      (t.external[stackPtr c + BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).isSome := by
    intro off len hl i hi
    have := (hts.stackWritable off len hl).mem i hi
    rwa [hrsp] at this
  have hcc : ∀ off len, off + len ≤ 280 → ∀ i < len,
      (c.external[stackPtr c + BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).isSome :=
    fun off len hl i hi ↦ (hc.storage.stackWritable off len hl).mem i hi
  have hstate : (⟨(stackPtr t).toNat, 20⟩ : MemoryRegion).HasBytes t.external
      (absorbedStateBytes message) := by
    have hsrc := hc.source.state
    have he : stackPtr c + 184 + 72 = stackPtr c + BitVec.ofNat 64 256 := by
      rw [BitVec.add_assoc]; rfl
    rw [he, ← absorbedStateBytes_size message] at hsrc
    rw [hrsp, ← absorbedStateBytes_size message]
    apply hasBytes_of_copy _ hsrc
    intro i hi
    rw [absorbedStateBytes_size] at hi
    have hs (a j : Nat) : stackPtr c + BitVec.ofNat 64 a + BitVec.ofNat 64 j =
        stackPtr c + BitVec.ofNat 64 (a + j) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hs]
    by_cases hi8 : i < 8
    · have key := bytes_eq_of_read_eq (n := 64) (hct 0 8 (by omega)) (hcc 256 8 (by omega)) W0 i hi8
      simp only [hs, Nat.zero_add] at key
      exact key
    by_cases hi16 : i < 16
    · have key := bytes_eq_of_read_eq (n := 64) (hct 8 8 (by omega)) (hcc 264 8 (by omega)) W8
        (i - 8) (by omega)
      simp only [hs] at key
      rwa [show 8 + (i - 8) = i by omega, show 264 + (i - 8) = 256 + i by omega] at key
    · have key := bytes_eq_of_read_eq (n := 32) (hct 16 4 (by omega)) (hcc 272 4 (by omega)) W16
        (i - 16) (by omega)
      simp only [hs] at key
      rwa [show 16 + (i - 16) = i by omega, show 272 + (i - 16) = 256 + i by omega] at key
  have htail : (⟨(stackPtr t + 24).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
      t.external (tailBytes message) := by
    rw [hrsp]
    apply hasBytes_of_copy _ hc.absorbed.tail
    intro i hi
    have hn : (tailBytes message).size < 64 := tailBytes_lt message
    refine (hB.agrees.byte fun comp hcomp ↦ hBc _ comp hcomp ⟨i, by omega, .inl rfl⟩).trans ?_
    exact hA.agrees.byte fun comp hcomp ↦ hAc _ comp hcomp ⟨i, by omega, .inl rfl⟩
  have hdf : DirectionFlagClear t.RFLAGS :=
    (hag.directionFlagClear (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
      hp.df).df
  obtain ⟨n, hn⟩ := hc.advances
  exact ⟨t, ⟨⟨n + fuel, hn.trans hrun⟩, hr, hcode, hB.rip, hts, hdf, hrsp.trans hcsp, htail,
    hstate, hposition, hblocks, hag⟩⟩

end Sha1.Proofs.Buffered.Finalize.Digest
