import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.FirstCarry
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.MiddleFirst
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.MiddleSecond
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.TopCarry
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Arithmetic

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem firstProducts_local : Effect.Local firstProductsEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [firstProductsEffect, h.read_reg, h.read_mem]
  · intro s
    simp [firstProductsEffect, Write.Full, Operand.Full]

private theorem seq_full {E F : RamState → Effect}
    (hE : ∀ s, ∀ w ∈ (E s).writes, w.Full)
    (hF : ∀ s, ∀ w ∈ (F s).writes, w.Full) :
    ∀ s, ∀ w ∈ (Effect.seq E F s).writes, w.Full := by
  intro s w hw
  simp only [Effect.seq, List.mem_append, List.mem_map, List.mem_filter] at hw
  rcases hw with ⟨v, ⟨hv, _⟩, rfl⟩ | hw
  · exact hE s v hv
  · exact hF _ w hw

private theorem firstCarry_local : Effect.Local firstCarryEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [firstCarryEffect, h.read_reg, h.read_mem]
  · intro s
    simp [firstCarryEffect, Write.Full, Operand.Full]

private theorem middleFirst_local : Effect.Local middleFirstEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [middleFirstEffect, h.read_reg, h.read_mem]
  · intro s
    simp [middleFirstEffect, Write.Full, Operand.Full]

private theorem middleSecond_local : Effect.Local middleSecondEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [middleSecondEffect, h.read_reg, h.read_mem]
  · intro s
    simp [middleSecondEffect, Write.Full, Operand.Full]

private theorem topCarry_local : Effect.Local topCarryEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [topCarryEffect, h.read_reg, h.read_mem]
  · intro s
    simp [topCarryEffect, Write.Full, Operand.Full]

def arithmeticEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq firstProductsEffect firstCarryEffect)
    middleFirstEffect) middleSecondEffect) topCarryEffect

theorem arithmetic_full : ∀ s, ∀ w ∈ (arithmeticEffect s).writes, w.Full :=
  seq_full (seq_full (seq_full (seq_full firstProducts_local.full firstCarry_local.full)
    middleFirst_local.full) middleSecond_local.full) topCarry_local.full

theorem arithmetic_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x115565) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (arithmeticEffect t).Holds t u := by
  obtain ⟨t1, n1, he1, hf1, h1⟩ := firstProducts_run ctx hf hip
  obtain ⟨t2, n2, he2, hf2, h2, _⟩ := firstCarry_run ctx hf1 h1.rip
  obtain ⟨t3, n3, he3, hf3, h3⟩ := middleFirst_run ctx hf2 h2.rip
  obtain ⟨t4, n4, he4, hf4, h4⟩ := middleSecond_run ctx hf3 h3.rip
  obtain ⟨t5, n5, he5, hf5, h5⟩ := topCarry_run ctx hf4 h4.rip
  have f2 := seq_full firstProducts_local.full firstCarry_local.full
  have f3 := seq_full f2 middleFirst_local.full
  have f4 := seq_full f3 middleSecond_local.full
  have hh2 := h1.seq firstCarry_local (by simp [firstProductsEffect, Write.Full, Operand.Full]) h2
  have hh3 := hh2.seq middleFirst_local (f2 t) h3
  have hh4 := hh3.seq middleSecond_local (f3 t) h4
  have hh5 := hh4.seq topCarry_local (f4 t) h5
  exact ⟨t5, _, (((he1.trans he2).trans he3).trans he4).trans he5, hf5, hh5⟩
end P256.Proofs.Sec1.SquareRoot.SquareFour
