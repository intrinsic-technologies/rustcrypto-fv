import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Contract
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

namespace P256.Proofs.SignatureFromDer.Parser.ReadSlice

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions.CrossPageStore

theorem call_covers_slice {base x : BitVec 64} {off len total : Nat}
    (hb : off + len ≤ total)
    (h : (Component.mem (base + BitVec.ofNat 64 off) len).Covers x) :
    (Component.mem base total).Covers x := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨off + i, by omega, by rw [BitVec.add_assoc, BitVec.ofNat_add]⟩

theorem call_apart_slice {a b : BitVec 64} {len count : Nat}
    (h : RangeApart a len b count) (off size : Nat) (hb : off + size ≤ len) :
    RangeApart (a + BitVec.ofNat 64 off) size b count := by
  intro i hi j hj he
  apply h (off + i) (by omega) j hj
  simpa only [BitVec.add_assoc, BitVec.ofNat_add] using he

theorem call_apart_code {a : BitVec 64} {len : Nat}
    (h : ∀ i < len, ¬ InProgram (a + BitVec.ofNat 64 i))
    (off count : Nat) (hb : off + count ≤ Extracted.textBytes.size) :
    RangeApart a len (Extracted.textAddress + BitVec.ofNat 64 off) count := by
  intro i hi j hj he
  apply h i hi
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (off + j) (by simpa only [textBytes_size] using (show off + j < Extracted.textBytes.size by omega))

abbrev callBodyComponents (reader result : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 7, .reg 8, .reg 9, .flags, .rip,
    .mem (reader + 28) 4, .mem (reader + 32) 1, .mem result 24]

theorem call_frame {cs : List Component} {s t : RamState} {reader result : BitVec 64}
    (h : AgreesExcept cs s t)
    (hreg : ∀ c ∈ cs, c.isMem = false → c ∈ callBodyComponents reader result)
    (hmem : ∀ a n, .mem a n ∈ cs →
      (a = reader + 28 ∧ n ≤ 4) ∨ (a = reader + 32 ∧ n ≤ 1) ∨
      (∃ off : Nat, off + n ≤ 24 ∧ a = result + BitVec.ofNat 64 off)) :
    AgreesExcept (callBodyComponents reader result) s t := by
  apply h.widen hreg
  intro x c hc hx
  cases c with
  | mem a n =>
    rcases hmem a n hc with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨off, hb, rfl⟩
    · obtain ⟨i, hi, he⟩ := hx
      exact ⟨.mem (reader + 28) 4, by simp [callBodyComponents], i, by omega, he⟩
    · obtain ⟨i, hi, he⟩ := hx
      exact ⟨.mem (reader + 32) 1, by simp [callBodyComponents], i, by omega, he⟩
    · exact ⟨.mem result 24, by simp [callBodyComponents], call_covers_slice hb hx⟩
  | _ => exact hx.elim

theorem call_success_read {s t : RamState} {addr : BitVec 64} {width : Nat}
    {cs : List Component} (h : AgreesExcept cs s t)
    (hm : ∀ a n, .mem a n ∈ cs →
      RangeApart a n addr (width / 8)) :
    (Operand.mem addr : Operand width).read t = (Operand.mem addr : Operand width).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h _
  intro i hi c hc hcov
  cases c with
  | mem a n =>
    obtain ⟨j, hj, he⟩ := hcov
    exact hm a n hc j hj i hi he.symm
  | _ => exact hcov.elim


end P256.Proofs.SignatureFromDer.Parser.ReadSlice
