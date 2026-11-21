import Base16ct.Spec.Program
import X86Proofs.Program.ReadWrite.Bytes

namespace Base16ct.Proofs

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem byte_lookup_of_operand_read {s : RamState} {a : BitVec 64} {b : UInt8}
    (hread : (Operand.mem a : Operand 8).read s = b.toBitVec)
    (hallocated : (s.external[a]?).isSome) : s.external[a]? = some b := by
  change memLoad s.external a 8 = b.toBitVec at hread
  rw [memLoad_8, UInt8.toBitVec_inj] at hread
  change (s.external[a]?).getD 0 = b at hread
  cases hlookup : s.external[a]? with
  | none => simp [hlookup] at hallocated
  | some value =>
    simp only [hlookup, Option.getD_some] at hread
    exact congrArg some hread

theorem readOutput_congr_prefix {initial s t : RamState} {count : Nat}
    (hbytes : ∀ j, j < count →
      t.external[initial.regValue .rcx + BitVec.ofNat 64 j]? =
        s.external[initial.regValue .rcx + BitVec.ofNat 64 j]?) :
    readOutput initial t count = readOutput initial s count := by
  unfold readOutput
  simp only [outputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  congr 1
  have hb : ∀ j ∈ List.range count,
      t.external[initial.regValue .rcx + BitVec.ofNat 64 j]? =
      s.external[initial.regValue .rcx + BitVec.ofNat 64 j]? :=
    fun j hj ↦ hbytes j (List.mem_range.mp hj)
  generalize List.range count = js at hb ⊢
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.mapM_cons, List.mapM_cons, hb j (by simp),
      ih (fun k hk ↦ hb k (by simp [hk]))]

theorem readOutput_succ {initial t : RamState} {count : Nat} {bytes : List UInt8}
    {byte : UInt8} (hprefix : readOutput initial t count = .ok bytes.toByteArray)
    (hbyte : t.external[initial.regValue .rcx + BitVec.ofNat 64 count]? = some byte) :
    readOutput initial t (count + 1) = .ok (bytes ++ [byte]).toByteArray := by
  unfold readOutput at hprefix ⊢
  simp only [outputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] at hprefix ⊢
  rw [List.range_succ, List.mapM_append]
  simp only [List.mapM_cons, List.mapM_nil, hbyte]
  generalize he : List.mapM (fun j ↦
    match t.external[initial.regValue .rcx + BitVec.ofNat 64 j]? with
    | some byte => Except.ok byte
    | none => Except.error (Fault.unmappedMemory
        (initial.regValue .rcx + BitVec.ofNat 64 j))) (List.range count) = result at hprefix ⊢
  cases result with
  | error e => cases hprefix
  | ok values =>
    have hv : values = bytes := by
      have hdata := congrArg ByteArray.data (Except.ok.inj hprefix)
      simpa only [List.data_toByteArray, List.toList_toArray] using congrArg Array.toList hdata
    subst values
    change Except.ok (ByteArray.mk _) = Except.ok _
    congr 1
    apply ByteArray.ext
    exact List.data_toByteArray.symm

theorem readLengthOutput_of_operand_read {initial final : RamState} {value : BitVec 64}
    (hreadable : MemReadable final (initial.regValue .rdx) 8)
    (hread : (Operand.mem (initial.regValue .rdx) : Operand 64).read final = value) :
    readLengthOutput initial final = .ok value := by
  have hbytes := Bytes.of_memLoad (n := 64) hreadable.mem
  change memLoad final.external (initial.regValue .rdx) 64 = value at hread
  rw [hread] at hbytes
  simpa only [readLengthOutput, lengthOutputRegion, registerRegion,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using hbytes.loadBytes64

end Base16ct.Proofs
