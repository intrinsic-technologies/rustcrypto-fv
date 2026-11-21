import P256.Proofs.Sec1.Decompress.Output.Copy
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def components (s : RamState) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s) 32]

theorem frame {s t : RamState} (h : (copyEffect s).Holds s t) :
    AgreesExcept (components s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [components]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s) 32, by simp [components], ?_⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩


theorem copy_bytes {s t : RamState} (effect : (copyEffect s).Holds s t)
    (input : MemReadable s (stackPtr s + 120) 32) (output : MemReadable t (stackPtr s) 32) :
    ∀ i < 32, t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[(stackPtr s + 120) + BitVec.ofNat 64 i]? := by
  have limbs (j : Nat) (hj : j < 4) :
      memLoad t.external (stackPtr s + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external ((stackPtr s + 120) + BitVec.ofNat 64 (8*j)) 64 := by
    have values := effect.writes
    simp only [copyEffect, Write.AllHold] at values
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h0 : memLoad t.external (stackPtr s + 0) 64 = memLoad s.external (stackPtr s + 120) 64 := values.2.2.1
      simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
    · have h1 : memLoad t.external (stackPtr s + 8) 64 = memLoad s.external (stackPtr s + 128) 64 := values.2.2.2.1
      simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h1
    · have h2 : memLoad t.external (stackPtr s + 16) 64 = memLoad s.external (stackPtr s + 136) 64 := values.2.2.2.2.1
      simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h2
    · have h3 : memLoad t.external (stackPtr s + 24) 64 = memLoad s.external (stackPtr s + 144) 64 := values.2.2.2.2.2
      simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h3
  intro i hi
  have bytes {v : RamState} {address : BitVec 64} (readable : MemReadable v address 32) :
      Bytes v.external (address + BitVec.ofNat 64 (8*(i/8))) 8
        (storedByte (memLoad v.external (address + BitVec.ofNat 64 (8*(i/8))) 64)) := by
    apply Bytes.of_memLoad (n := 64)
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact readable.mem _ (by omega)
  have ht := bytes output (i%8) (by omega)
  have hs := bytes input (i%8) (by omega)
  rw [limbs _ (by omega)] at ht
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8 = i by omega] using ht.trans hs.symm


end P256.Proofs.Sec1.Decompress.Output
