import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Memory

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame.Copy32

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Pre (ip : BitVec 64) (source destination : RamState → BitVec 64)
    (s : RamState) : Prop where
  rip : s.RIP = ip
  readable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), MemReadable s (source s + i) 8
  writable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (destination s + i) 8
  apart : RangeApart (destination s) 32 (source s) 32
  codeApart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (destination s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def effect (ip : BitVec 64) (source destination : RamState → BitVec 64)
    (s : RamState) : Effect :=
  { rip := ip
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.mem (destination s) : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 8) : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 16) : Operand 64), (.mem (source s + 16) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 24) : Operand 64), (.mem (source s + 24) : Operand 64).read s⟩] }

def components (destination : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .rip, .mem destination 32]

theorem frame {s t : RamState} {ip : BitVec 64} {source destination : RamState → BitVec 64}
    (h : (effect ip source destination s).Holds s t) :
    AgreesExcept (components (destination s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [components]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (destination s) 32, by simp [components], ?_⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

end P256.Proofs.Program.ScalarFrame.Copy32
