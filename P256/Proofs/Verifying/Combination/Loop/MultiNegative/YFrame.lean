import P256.Proofs.Verifying.Combination.Loop.MultiNegative.YCopy
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative.YCopy

open X86 X86.Machine X86Proofs
open P256.Proofs.Program.ScalarFrame

theorem frame {s t : RamState} {ip : BitVec 64} {source destination : RamState → BitVec 64}
    (h : (effect ip source destination s).Holds s t) :
    AgreesExcept (Copy32.components (destination s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [Copy32.components]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (destination s) 32, by simp [Copy32.components], ?_⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem copy_bytes {s t : RamState} {entry : BitVec 64}
    {source destination : RamState → BitVec 64}
    (effect : (effect entry source destination s).Holds s t)
    (input : MemReadable s (source s) 32) (output : MemReadable t (destination s) 32) :
    ∀ i < 32, t.external[destination s + BitVec.ofNat 64 i]? =
      s.external[source s + BitVec.ofNat 64 i]? := by
  have limbs (j : Nat) (hj : j < 4) :
      memLoad t.external (destination s + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (source s + BitVec.ofNat 64 (8*j)) 64 := by
    have values := effect.writes
    simp only [YCopy.effect, Write.AllHold] at values
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h0 : memLoad t.external (destination s) 64 = memLoad s.external (source s) 64 := values.2.2.1
      simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
    · exact values.2.2.2.1
    · exact values.2.2.2.2.1
    · exact values.2.2.2.2.2
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

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative.YCopy
