import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Mark
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Copy
import Hkdf.Proofs.Common.Streaming
import Hkdf.Proofs.Common.StreamPadding.Mathematics
import Hkdf.Proofs.Common.Memory.LoadBytes

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def padded (digest : ByteArray) : ByteArray :=
  digest ++ ⟨#[128]⟩ ++ ⟨Array.replicate 23 0⟩ ++
    Hkdf.Proofs.NIST.Encoding.natToOctets 8 768

theorem padded_size {digest : ByteArray} (size : digest.size = 32) :
    (padded digest).size = 64 := by
  simp only [padded, ByteArray.size_append, size,
    Hkdf.Proofs.Common.Encoding.natToOctets_size]
  rfl

private theorem hasBytes_append {memory : Ram} {address : BitVec 64} {a b : ByteArray}
    (front : (⟨address.toNat,a.size⟩ : MemoryRegion).HasBytes memory a)
    (back : (⟨(address+BitVec.ofNat 64 a.size).toNat,b.size⟩ : MemoryRegion).HasBytes memory b) :
    (⟨address.toNat,(a++b).size⟩ : MemoryRegion).HasBytes memory (a++b) := by
  refine ⟨rfl,fun i => ?_⟩
  by_cases hi : i.val < a.size
  · have byte := front.2 ⟨i.val,hi⟩
    simpa only [ByteArray.getElem_append_left hi] using byte
  · have hj : i.val-a.size < b.size := by
      have h : i.val < a.size+b.size := by simpa only [ByteArray.size_append] using i.isLt
      omega
    have byte := back.2 ⟨i.val-a.size,hj⟩
    change memory[BitVec.ofNat 64 ((address+BitVec.ofNat 64 a.size).toNat+(i.val-a.size))]? = _ at byte
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc,
      ← BitVec.ofNat_add,Nat.add_sub_of_le (by omega : a.size ≤ i.val)] at byte
    simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
      ByteArray.getElem_append_right (by omega : a.size ≤ i.val)] using byte

private theorem word_byte {s : RamState} {base : BitVec 64} {word : BitVec 64}
    (allocated : ∀ i < 8, (s.external[base + BitVec.ofNat 64 i]?).isSome)
    (read : memLoad s.external base 64 = word) {i : Nat} (hi : i < 8) :
    s.external[base + BitVec.ofNat 64 i]? = some (storedByte word i) := by
  have bytes := Bytes.of_memLoad (n := 64) allocated
  rw [read] at bytes
  exact bytes i hi

theorem mark_bytes {s a : RamState} {digest : ByteArray}
    (effect : (Mark.effect s).Holds s a)
    (count : loadBytes s.external (rspOf s + 208) 8 = .ok 1)
    (source : (⟨(rspOf s + 72).toNat,32⟩ : MemoryRegion).HasBytes s.external digest)
    (readable : MemReadable a (rspOf s + 72) 64) :
    (⟨(rspOf s + 72).toNat,64⟩ : MemoryRegion).HasBytes a.external (padded digest) := by
  have size : digest.size = 32 := source.1
  have add32 : rspOf s + 72#64 + 32#64 = rspOf s + 104#64 := by bv_omega
  have add33 : rspOf s + 72#64 + 33#64 = rspOf s + 105#64 := by bv_omega
  have add56 : rspOf s + 72#64 + 56#64 = rspOf s + 128#64 := by bv_omega
  have writes := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at writes
  have front : (⟨(rspOf s + 72).toNat,digest.size⟩ : MemoryRegion).HasBytes a.external digest := by
    refine ⟨rfl,fun i => ?_⟩
    apply Eq.trans (effect.agrees.byte ?_) (source.2 i)
    intro c hc covered
    simp only [Mark.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component, Operand.component, Nat.reduceDiv] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,he⟩ := covered
    all_goals have hi : i.val < 32 := by have := i.isLt; omega
    all_goals simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofNat_eq_ofNat] at he
    all_goals first
    | exact (RangeApart.offsets (rspOf s) (a := 72) (len := 32) (b := 104)
        (count := 1) (by decide) (by decide) (.inl (by decide))) i.val hi j hj he
    | exact (RangeApart.offsets (rspOf s) (a := 72) (len := 32) (b := 120)
        (count := 8) (by decide) (by decide) (.inl (by decide))) i.val hi j hj he
    | exact (RangeApart.offsets (rspOf s) (a := 72) (len := 32) (b := 113)
        (count := 8) (by decide) (by decide) (.inl (by decide))) i.val hi j hj he
    | exact (RangeApart.offsets (rspOf s) (a := 72) (len := 32) (b := 105)
        (count := 8) (by decide) (by decide) (.inl (by decide))) i.val hi j hj he
    | exact (RangeApart.offsets (rspOf s) (a := 72) (len := 32) (b := 128)
        (count := 8) (by decide) (by decide) (.inl (by decide))) i.val hi j hj he
  have marker : (⟨(rspOf s + 104).toNat,1⟩ : MemoryRegion).HasBytes a.external ⟨#[128]⟩ := by
    refine ⟨rfl,fun i => ?_⟩
    have iz : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    have marked : memLoad a.external (rspOf s + 104) 8 = 128 := writes.2.1
    have byte := Bytes.of_memLoad (m := a.external) (n := 8) (a := rspOf s + 104) (fun j hj => by
      simpa only [BitVec.ofNat_add,
        BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, add32] using
          readable.mem (32+j) (by omega))
    rw [marked] at byte
    have markedByte := byte 0 (by decide)
    change a.external[rspOf s + 104 + 0]? = some 128 at markedByte
    simp only [iz, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    change a.external[rspOf s + 104#64]? = some 128
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using markedByte
  have zeros : (⟨(rspOf s + 105).toNat,23⟩ : MemoryRegion).HasBytes a.external
      ⟨Array.replicate 23 0⟩ := by
    refine ⟨rfl,fun i => ?_⟩
    have hi : i.val < 23 := i.isLt
    have word (offset : Nat) (member : offset ∈ ([105,113,120] : List Nat)) :
        memLoad a.external (rspOf s + BitVec.ofNat 64 offset) 64 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact writes.2.2.2.2.1
      · exact writes.2.2.2.1
      · exact writes.2.2.1
    let offset := if i.val < 8 then 105 else if i.val < 16 then 113 else 120
    have member : offset ∈ ([105,113,120] : List Nat) := by
      by_cases first : i.val < 8
      · simp [offset, first]
      · by_cases second : i.val < 16 <;> simp [offset, first, second]
    have bounds : 105 ≤ offset ∧ offset ≤ 120 ∧ offset ≤ 105+i.val ∧ 105+i.val < offset+8 := by
      by_cases first : i.val < 8
      · simp only [offset, first, ite_true]
        omega
      · by_cases second : i.val < 16 <;>
          simp only [offset, first, second, ite_true, ite_false] <;> omega
    have byte := word_byte (s := a) (base := rspOf s + BitVec.ofNat 64 offset)
      (fun j hj => by
        have alloc := readable.mem (offset-72+j) (by omega)
        have addr : rspOf s + 72 + BitVec.ofNat 64 (offset-72+j) =
            rspOf s + BitVec.ofNat 64 offset + BitVec.ofNat 64 j := by
          change rspOf s + BitVec.ofNat 64 72 + BitVec.ofNat 64 (offset-72+j) = _
          simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          omega
        simpa only [addr] using alloc)
      (word offset member) (i := 105+i.val-offset) (by omega)
    have addr : rspOf s + BitVec.ofNat 64 offset + BitVec.ofNat 64 (105+i.val-offset) =
        rspOf s + 105 + BitVec.ofNat 64 i.val := by
      change _ = rspOf s + BitVec.ofNat 64 105 + BitVec.ofNat 64 i.val
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [addr] at byte
    have zero : storedByte (0#64) (105+i.val-offset) = 0 := by simp [storedByte]
    change a.external[_]? = some (storedByte (0#64) (105+i.val-offset)) at byte
    rw [zero] at byte
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_eq_getElem_data, Array.getElem_replicate] using byte
  have length : (⟨(rspOf s + 128).toNat,8⟩ : MemoryRegion).HasBytes a.external
      (Hkdf.Proofs.NIST.Encoding.natToOctets 8 768) := by
    have countWord := Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64 count
    have value : Mark.lengthWord s = bswap64 (BitVec.ofNat 64 768) := by
      rw [Mark.lengthWord, countWord]
      rfl
    have written : memLoad a.external (rspOf s + 128) 64 = bswap64 (BitVec.ofNat 64 768) :=
      writes.2.2.2.2.2.trans value
    refine ⟨Hkdf.Proofs.Common.Encoding.natToOctets_size _ _,fun i => ?_⟩
    have hi : i.val < 8 := by simpa only [Hkdf.Proofs.Common.Encoding.natToOctets_size] using i.isLt
    have byte := word_byte (s := a) (base := rspOf s+128)
      (fun j hj => by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
          add56] using readable.mem (56+j) (by omega)) written hi
    rw [Hkdf.Proofs.Common.StreamPadding.bswap64_ofNat_storedByte 768 hi] at byte
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
  have singletonSize : (⟨#[128]⟩ : ByteArray).size = 1 := rfl
  have zerosSize : (⟨Array.replicate 23 0⟩ : ByteArray).size = 23 := by
    simp [ByteArray.size]
  have first := hasBytes_append (b := (⟨#[128]⟩ : ByteArray)) front
    (by simpa only [size, singletonSize, BitVec.ofNat_eq_ofNat,
      ← BitVec.add_assoc, add32] using marker)
  have second := hasBytes_append
    (b := (⟨Array.replicate 23 0⟩ : ByteArray)) first
    (by simpa only [ByteArray.size_append, size, singletonSize, zerosSize, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, add33] using zeros)
  simpa only [padded, ByteArray.size_append, size, singletonSize, zerosSize, Nat.reduceAdd,
    Hkdf.Proofs.Common.Encoding.natToOctets_size, BitVec.ofNat_eq_ofNat,
    ← BitVec.add_assoc, BitVec.reduceAdd] using hasBytes_append second
      (b := Hkdf.Proofs.NIST.Encoding.natToOctets 8 768)
      (by simpa only [ByteArray.size_append, size, singletonSize, zerosSize, Nat.reduceAdd,
        Hkdf.Proofs.Common.Encoding.natToOctets_size, BitVec.ofNat_eq_ofNat,
        ← BitVec.add_assoc, add56] using length)

theorem copy_words {a t : RamState}
    (effect : (Copy.effect a).Holds a t)
    (highword : a.regValue .rax = memLoad a.external (rspOf a + 128) 64) :
    ∀ j < 8, memLoad t.external (rspOf a + BitVec.ofNat 64 (8+8*j)) 64 =
      memLoad a.external (rspOf a + BitVec.ofNat 64 (72+8*j)) 64 := by
  intro j hj
  by_cases last : j = 7
  · subst j
    exact effect.writes.2.2.2.1.trans highword
  · have member : 8+8*j ∈ ([56,48,40,32,24,16,8] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have word := Write.allHold_iff.mp effect.writes
      (⟨(.mem (rspOf a + BitVec.ofNat 64 (8+8*j)) : Operand 64),
        memLoad a.external (rspOf a + BitVec.ofNat 64 ((8+8*j)+64)) 64⟩)
      (List.mem_append_right _ (List.mem_map_of_mem member))
    change memLoad t.external _ 64 = _ at word
    simpa only [show (8+8*j)+64 = 72+8*j by omega] using word

theorem copy_bytes {a t : RamState} {block : ByteArray}
    (effect : (Copy.effect a).Holds a t)
    (source : (⟨(rspOf a + 72).toNat,64⟩ : MemoryRegion).HasBytes a.external block)
    (readable : MemReadable t (rspOf a + 8) 64)
    (highword : a.regValue .rax = memLoad a.external (rspOf a + 128) 64) :
    (⟨(rspOf a + 8).toNat,64⟩ : MemoryRegion).HasBytes t.external block := by
  refine ⟨source.1,?_⟩
  intro i
  have hi : i.val < 64 := by have := i.isLt; have size : block.size = 64 := source.1; omega
  have word := copy_words effect highword (i.val/8) (by omega)
  have equal := memByte_of_memLoad_eq word (i.val%8) (by omega)
  have address (offset : Nat) :
      rspOf a + BitVec.ofNat 64 (offset+8*(i.val/8)) + BitVec.ofNat 64 (i.val%8) =
        rspOf a + BitVec.ofNat 64 offset + BitVec.ofNat 64 i.val := by
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address, address] at equal
  have stored := source.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at stored ⊢
  have present := readable.mem i.val hi
  obtain ⟨byte,hbyte⟩ := Option.isSome_iff_exists.mp present
  change (t.external[_]?).getD 0 = (a.external[_]?).getD 0 at equal
  simp only [BitVec.ofNat_eq_ofNat] at stored hbyte equal ⊢
  rw [stored,hbyte] at equal
  simp only [Option.getD_some] at equal
  rw [hbyte,equal]

theorem payload {s a t : RamState} {digest : ByteArray}
    (mark : (Mark.effect s).Holds s a) (copy : (Copy.effect a).Holds a t)
    (count : loadBytes s.external (rspOf s + 208) 8 = .ok 1)
    (source : (⟨(rspOf s + 72).toNat,32⟩ : MemoryRegion).HasBytes s.external digest)
    (middleReadable : MemReadable a (rspOf s + 72) 64)
    (readable : MemReadable t (rspOf s + 8) 64) :
    (⟨(rspOf s + 8).toNat,64⟩ : MemoryRegion).HasBytes t.external (padded digest) := by
  have rsp : rspOf a = rspOf s := mark.agrees.read (n := 64) (r := 4)
    (by simp [Mark.effect, Effect.components, Write.component, Operand.component])
  have words := mark.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  have highword : a.regValue .rax = memLoad a.external (rspOf a + 128) 64 := by
    rw [rsp]
    exact words.1.trans words.2.2.2.2.2.symm
  simpa only [rsp] using copy_bytes copy
    (by simpa only [rsp] using mark_bytes mark count source middleReadable)
    (by simpa only [rsp] using readable) highword

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad
