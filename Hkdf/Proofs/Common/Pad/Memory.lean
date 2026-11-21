import Hkdf.Proofs.Common.Pad.Code
import Hkdf.Proofs.Common.Pad.Permissions
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions.CrossPageStore

def buffer (v : Variant) (s : RamState) : BitVec 64 :=
  stackPtr s + BitVec.ofNat 64 (layout v).bufferOffset

def footprint (v : Variant) (s : RamState) : List Component :=
  [.reg 0, .flags, .rip, .mem (buffer v s) 64]

structure Memory (v : Variant) (s : RamState) : Prop where
  writable : Writable s (buffer v s) 64
  avoids : ∀ i < 64, ¬ InProgram (buffer v s + BitVec.ofNat 64 i)

theorem buffer_of_agrees {v : Variant} {s t : RamState}
    (agrees : AgreesExcept (footprint v s) s t) : buffer v t = buffer v s := by
  have rsp : stackPtr t = stackPtr s := agrees.read (n := 64) (r := 4) (by simp [footprint])
  simp only [buffer, rsp]

theorem Memory.after {v : Variant} {s t : RamState} (memory : Memory v s)
    (agrees : AgreesExcept (footprint v s) s t) : Memory v t := by
  have eq := buffer_of_agrees agrees
  constructor
  · rw [eq]
    exact ⟨⟨memory.writable.low, fun i hi => agrees.grow _ (memory.writable.mem i hi)⟩,
      memory.writable.tables⟩
  · rw [eq]
    exact memory.avoids

theorem Memory.loaded_after {v : Variant} {s t : RamState} (memory : Memory v s)
    (loaded : ProgramLoaded s) (agrees : AgreesExcept (footprint v s) s t) :
    ProgramLoaded t := by
  intro a b hb
  rw [agrees.byte]
  · exact loaded a b hb
  · intro c hc covered
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact covered.elim
    · exact covered.elim
    · exact covered.elim
    · obtain ⟨i, hi, rfl⟩ := covered
      exact memory.avoids i hi ⟨b, hb⟩

theorem footprint_trans {v : Variant} {s t u : RamState}
    (left : AgreesExcept (footprint v s) s t)
    (right : AgreesExcept (footprint v t) t u) :
    AgreesExcept (footprint v s) s u := by
  have eq : footprint v t = footprint v s := by
    simp only [footprint, buffer_of_agrees left]
  rw [eq] at right
  exact (left.trans right).mono (by simp)

theorem Memory.byte_writable {v : Variant} {s : RamState} (memory : Memory v s)
    (i : Nat) (hi : i < 64) : MemWritable s (buffer v s + BitVec.ofNat 64 i) 1 := by
  have w := memory.writable.add i (len := 1) (by omega)
  exact w.toMemWritable

theorem Memory.byte_code {v : Variant} {s : RamState} (memory : Memory v s)
    (i offset len : Nat) (hi : i < 64) (bound : offset + len ≤ (layout v).positions[4] + 10) :
    RangeApart (buffer v s + BitVec.ofNat 64 i) 1
      (v.entry + BitVec.ofNat 64 offset) len := by
  intro j hj k hk eq
  have hj0 : j = 0 := by omega
  subst j
  simp only [BitVec.add_zero] at eq
  apply memory.avoids i hi
  have entry : v.entry = Hkdf.Spec.Program.Extracted.textAddress +
      BitVec.ofNat 64 (layout v).offset := by
    simp [Variant.entry, Variant.pc, (layout_valid v).initial]
  rw [eq, entry, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  simpa [Nat.add_assoc] using inProgram_of_textOffset ((layout v).offset + offset + k)
    (by have h := (layout_valid v).bound; omega)

theorem byte_agrees {v : Variant} {s t : RamState} {i : Nat} (hi : i < 64)
    (agrees : AgreesExcept [.mem (buffer v s + BitVec.ofNat 64 i) 1, .flags, .rip] s t) :
    AgreesExcept (footprint v s) s t := by
  refine ⟨?_, ?_, agrees.rest, agrees.grow⟩
  · intro c hc hm
    exact agrees.agree c (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · contradiction
      · exact hc (by simp [footprint])
      · exact hc (by simp [footprint])) hm
  · intro a ha
    apply agrees.memory a
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j, hj, rfl⟩ := covered
      apply ha (.mem (buffer v s) 64) (by simp [footprint])
      exact ⟨i + j, by omega, by simp only [BitVec.ofNat_add, BitVec.add_assoc]⟩
    · exact covered.elim
    · exact covered.elim

end Hkdf.Proofs.Common.Pad
