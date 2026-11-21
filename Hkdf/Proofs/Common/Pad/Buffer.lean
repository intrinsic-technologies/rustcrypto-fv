import Hkdf.Proofs.Common.Pad.Layout

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

 def Stored (s : RamState) (pointer : BitVec 64) (bytes : Vector UInt8 64)
    (mask : UInt8) (count : Nat) : Prop :=
  ∀ i : Fin 64, s.external[pointer + BitVec.ofNat 64 i.val]? =
    some (if i.val < count then bytes[i] ^^^ mask else bytes[i])

theorem read_byte {s : RamState} {address : BitVec 64} {byte : UInt8}
    (stored : s.external[address]? = some byte) :
    (Operand.mem address : Operand 8).read s = byte.toBitVec := by
  simp [Operand.read, memLoad, memByte, PhysicalMemory.read, stored]

theorem byte_of_read {s : RamState} {address : BitVec 64} {byte : UInt8}
    (present : (s.external[address]?).isSome)
    (read : (Operand.mem address : Operand 8).read s = byte.toBitVec) :
    s.external[address]? = some byte := by
  cases found : s.external[address]? with
  | none => simp [found] at present
  | some value =>
    have eq := (read_byte found).symm.trans read
    have same : value = byte := UInt8.toBitVec_inj.mp eq
    exact congrArg some same

theorem Stored.xor {s t : RamState} {pointer : BitVec 64} {bytes : Vector UInt8 64}
    {mask : UInt8} {count : Nat} (stored : Stored s pointer bytes mask count)
    (within : count < 64)
    (agrees : AgreesExcept [.mem (pointer + BitVec.ofNat 64 count) 1, .flags, .rip] s t)
    (write : (Operand.mem (pointer + BitVec.ofNat 64 count) : Operand 8).read t =
      (Operand.mem (pointer + BitVec.ofNat 64 count) : Operand 8).read s ^^^ mask.toBitVec) :
    Stored t pointer bytes mask (count + 1) := by
  intro i
  by_cases current : i.val = count
  · subst count
    have original : s.external[pointer + BitVec.ofNat 64 i.val]? = some bytes[i] := by
      simpa only [Nat.lt_irrefl, ↓reduceIte] using stored i
    have changed : t.external[pointer + BitVec.ofNat 64 i.val]? = some (bytes[i] ^^^ mask) := by
      apply byte_of_read
      · exact agrees.grow _ (by rw [original]; rfl)
      · rw [write, read_byte original]
        rfl
    simpa only [Nat.lt_succ_self, ↓reduceIte] using changed
  · have unchanged : t.external[pointer + BitVec.ofNat 64 i.val]? =
        s.external[pointer + BitVec.ofNat 64 i.val]? := by
      apply agrees.byte
      intro component member cover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · obtain ⟨j, hj, equal⟩ := cover
        have zero : j = 0 := by omega
        subst j
        simp only [BitVec.add_zero] at equal
        have same : BitVec.ofNat 64 i.val = BitVec.ofNat 64 count := by bv_omega
        have number := congrArg BitVec.toNat same
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show i.val < 2^64 by omega),
          Nat.mod_eq_of_lt (show count < 2^64 by omega)] at number
        omega
      · exact cover
      · exact cover
    rw [unchanged, stored i]
    by_cases before : i.val < count
    · simp only [before, show i.val < count + 1 by omega, ↓reduceIte]
    · simp only [before, show ¬i.val < count + 1 by omega, ↓reduceIte]

theorem Stored.of_agrees {s t : RamState} {pointer : BitVec 64} {bytes : Vector UInt8 64}
    {mask : UInt8} {count : Nat} {components : List Component}
    (stored : Stored s pointer bytes mask count) (agrees : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬c.Covers a) : Stored t pointer bytes mask count := by
  intro i
  rw [agrees.byte (fun c hc ↦ noMem c hc _)]
  exact stored i

theorem Stored.initial {s : RamState} {pointer : BitVec 64} {bytes : ByteArray}
    (stored : (⟨pointer.toNat, 64⟩ : MemoryRegion).HasBytes s.external bytes)
    (mask : UInt8) :
    Stored s pointer (⟨bytes.data, stored.1⟩ : Vector UInt8 64) mask 0 := by
  intro i
  have bound : i.val < bytes.size := by have := stored.1; change bytes.size = 64 at this; omega
  have h := stored.2 ⟨i.val, bound⟩
  change s.external[pointer + BitVec.ofNat 64 i.val]? =
    some (if i.val < 0 then bytes[i.val] ^^^ mask else bytes[i.val])
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Nat.not_lt_zero, ↓reduceIte,
    ByteArray.getElem_eq_getElem_data] using h

theorem Stored.hasBytes {s : RamState} {pointer : BitVec 64} {bytes : ByteArray}
    (size : bytes.size = 64) (mask : UInt8)
    (stored : Stored s pointer (⟨bytes.data, size⟩ : Vector UInt8 64) mask 64) :
    (⟨pointer.toNat, 64⟩ : MemoryRegion).HasBytes s.external (HMAC.xorPad bytes mask) := by
  refine ⟨by rw [HMAC.xorPad_size, size]; rfl, ?_⟩
  intro i
  have bound : i.val < 64 := by simpa only [HMAC.xorPad_size, size] using i.isLt
  have h := stored ⟨i.val, bound⟩
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, bound, ↓reduceIte,
    Fin.getElem_fin, Vector.getElem_mk, HMAC.xorPad, ByteArray.getElem_eq_getElem_data,
    Array.getElem_map] using h

end Hkdf.Proofs.Common.Pad
