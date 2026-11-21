import P256.Proofs.Generate.Wrapper.Tail.ScalarCopy
import P256.Proofs.Program.CopyBytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem point_tag {input : ByteArray} {d : Nat}
    (draw : Ecdh.drawNonzeroScalar input = some d) :
    (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G)).data[0]? = some 4 := by
  obtain ⟨positive,bound⟩ := (draw_some_iff_trace.mp draw).value
  have nonzero := PublicPoint.publicPoint_ne_infinity d positive bound
  cases point : Points.mul d Operations.domain.G with
  | infinity => exact (nonzero point).elim
  | affine x y =>
    simp [Sec1Serialize.encodedPoint,Points.encode,Points.encodeWith,
      Standards.SECG.ECC.Points.encodePoint,ByteArray.data_append,Array.getElem?_append]

theorem payload_append {memory : Ram} {address : BitVec 64} {first second : ByteArray}
    (left : (MemoryRegion.mk address.toNat first.size).HasBytes memory first)
    (right : (MemoryRegion.mk (address+BitVec.ofNat 64 first.size).toNat second.size).HasBytes memory second) :
    (MemoryRegion.mk address.toNat (first.size+second.size)).HasBytes memory (first++second) := by
  refine ⟨ByteArray.size_append,?_⟩
  intro i
  by_cases hi : i.val < first.size
  · have byte := left.2 ⟨i.val,hi⟩
    simpa only [ByteArray.getElem_append_left hi] using byte
  · have bound : i.val-first.size < second.size := by
      have h : i.val < first.size+second.size := by
        simpa only [ByteArray.size_append] using i.isLt
      omega
    have byte := right.2 ⟨i.val-first.size,bound⟩
    change memory[BitVec.ofNat 64 ((address+BitVec.ofNat 64 first.size).toNat+(i.val-first.size))]? = _ at byte
    change memory[BitVec.ofNat 64 (address.toNat+i.val)]? = _
    simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at byte ⊢
    rw [BitVec.add_assoc,← BitVec.ofNat_add,Nat.add_sub_of_le (by omega)] at byte
    rw [byte]
    congr 1
    rw [ByteArray.getElem_append_right (by omega)]

theorem generated_payload {initial t : RamState} {input : ByteArray} {d : Nat}
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (scalar : Bytes t.external (initial.regValue .rcx+8) 32
      (fun i => UInt8.ofNat (d / 256^(31-i) % 256)))
    (point : (MemoryRegion.mk (initial.regValue .rcx+40).toNat 65).HasBytes
      t.external (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G))) :
    (MemoryRegion.mk (initial.regValue .rcx+8).toNat 97).HasBytes t.external
      (Spec.Generate.generatedSigningKey #[input]) := by
  have size := SecretKeyFromBytes.Encoding.natToOctets_size 32 d
  have first : (MemoryRegion.mk (initial.regValue .rcx+8).toNat
      (Standards.SECG.ECC.Encoding.natToOctets 32 d).size).HasBytes t.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 d) := by
    refine ⟨rfl,?_⟩
    intro i
    have hi : i.val < 32 := by simpa only [size] using i.isLt
    have byte := scalar i.val hi
    change t.external[BitVec.ofNat 64 ((initial.regValue .rcx+8).toNat+i.val)]? = _
    simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    rw [byte]
    congr 1
    exact (SecretKeyFromBytes.Encoding.natToOctets_getElem 32 d i.val hi).symm
  have second : (MemoryRegion.mk
      (initial.regValue .rcx+8+BitVec.ofNat 64 (Standards.SECG.ECC.Encoding.natToOctets 32 d).size).toNat
      (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G)).size).HasBytes
      t.external (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G)) := by
    rw [size,point.1]
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using point
  have result := payload_append first second
  rw [size,point.1,← generated_key_eq draw] at result
  exact result

end P256.Proofs.Generate.Wrapper
