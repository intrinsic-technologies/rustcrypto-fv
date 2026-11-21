import P256.Proofs.Field.Schoolbook.UpperProducts
import P256.Proofs.Field.Schoolbook.Correspondence

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Field.Montgomery.Schoolbook

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem upperProducts_stack {s t : RamState}
    (h : (upperProductsEffect s).Holds s t) {c : BitVec 64}
    (hc : c ∈ ([0,24,40,56,80] : List (BitVec 64))) :
    (Operand.mem (rspOf s+c) : Operand 64).read t =
      (Operand.mem (rspOf s+c) : Operand 64).read s := by
  have apart (d : BitVec 64) (hd : d ∈ ([16,48,32,8] : List (BitVec 64))) :
      OffsetsApart d 8 c 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
  apply memLoad_congr
  intro i hi
  have hb : t.external[rspOf s+c+BitVec.ofNat 64 i]? =
      s.external[rspOf s+c+BitVec.ofNat 64 i]? := by
    apply h.agrees.byte
    intro d hd ha
    simp only [upperProductsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨j, hj, he⟩ := ha
      first
      | exact (apart 16 (by simp)).ne (rspOf s) hj hi (by decide) he.symm
      | exact (apart 48 (by simp)).ne (rspOf s) hj hi (by decide) he.symm
      | exact (apart 32 (by simp)).ne (rspOf s) hj hi (by decide) he.symm
      | exact (apart 8 (by simp)).ne (rspOf s) hj hi (by decide) he.symm
  simp only [memByte, PhysicalMemory.read, hb]

private theorem productWords_value {lo hi a b : BitVec 64}
    (hl : lo = a*b) (hh : hi = mulHigh64 a b) :
    lo.toNat + wordBase*hi.toNat = b.toNat*a.toNat := by
  subst lo hi
  exact (Montgomery.product64_value a b).trans (Nat.mul_comm _ _)

private theorem mulWords_value {x y a b : BitVec 64} (hx : x = a) (hy : y = b) :
    x.toNat*y.toNat = b.toNat*a.toNat := by
  rw [hx, hy, Nat.mul_comm]

attribute [local irreducible] memLoad mulHigh64 Operand.read

set_option maxHeartbeats 800000 in
theorem upperProducts_inputs {s t : RamState} (h : (upperProductsEffect s).Holds s t) :
    let a2 := ((Operand.mem ((Operand.reg 6 : Operand 64).read s+16) : Operand 64).read s).toNat
    let a3 := ((Operand.reg 1 : Operand 64).read s).toNat
    let b0 := ((Operand.mem (rspOf s+64) : Operand 64).read s).toNat
    let b1 := ((Operand.mem (rspOf s+72) : Operand 64).read s).toNat
    let b2 := ((Operand.reg 14 : Operand 64).read s).toNat
    let b3 := ((Operand.reg 3 : Operand 64).read s).toNat
    upperInputRow t = upperInputRow s ∧
      upperInputQ t = #v[a2*b0, a2*b1,
        a2*((Operand.mem (rspOf s+40) : Operand 64).read s).toNat,
        a2*((Operand.mem (rspOf s+56) : Operand 64).read s).toNat] ∧
      upperInputP t = #v[a3*b0, a3*b1, a3*b2, a3*b3] := by
  dsimp only
  have hsp : rspOf t = rspOf s := h.agrees.read (r := 4) (n := 64)
    (by simp [upperProductsEffect, Effect.components])
  have h8 : (Operand.reg 8 : Operand 64).read t = (Operand.reg 8 : Operand 64).read s :=
    h.agrees.read (by simp [upperProductsEffect, Effect.components])
  have h11 : (Operand.reg 11 : Operand 64).read t = (Operand.reg 11 : Operand 64).read s :=
    h.agrees.read (by simp [upperProductsEffect, Effect.components])
  have h12 : (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
    h.agrees.read (by simp [upperProductsEffect, Effect.components])
  have hm0 := upperProducts_stack h (c := 0) (by simp)
  have hm24 := upperProducts_stack h (c := 24) (by simp)
  have hm40 := upperProducts_stack h (c := 40) (by simp)
  have hm56 := upperProducts_stack h (c := 56) (by simp)
  have hm80 := upperProducts_stack h (c := 80) (by simp)
  have hw := h.writes
  dsimp only [upperProductsEffect, Write.AllHold] at hw
  rcases hw with ⟨hr15, hm16, hr13, hm48, hm32, hr5, hr14, hr9, hm8, hr3, hr1, _, _, hr6, hr10⟩
  constructor
  · simp only [upperInputRow, hsp, hm0, hm24, hm80, h8, h11, h12]
  have readSlot (c : BitVec 64) :
      (Operand.mem (rspOf t+c) : Operand 64).read t =
        (Operand.mem (rspOf s+c) : Operand 64).read t :=
    congrArg (fun sp => (Operand.mem (sp+c) : Operand 64).read t) hsp
  constructor
  · ext i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact productWords_value hr10 hr6
    · exact productWords_value hr1 hr3
    · exact mulWords_value ((readSlot 40).trans hm40) hr14
    · exact mulWords_value ((readSlot 56).trans hm56) hr14
  · ext i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact productWords_value ((readSlot 8).trans hm8) hr9
    · exact productWords_value ((readSlot 32).trans hm32) hr5
    · exact productWords_value ((readSlot 48).trans hm48) hr13
    · exact productWords_value ((readSlot 16).trans hm16) hr15

end P256.Proofs.Field.Schoolbook
