import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program.ScalarFrame
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def effect (ip : BitVec 64) (source destination : RamState → BitVec 64)
    (s : RamState) : Effect :=
  { rip := ip
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.mem (source s + 24) : Operand 64).read s⟩,
      ⟨(.mem (destination s) : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 8) : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 16) : Operand 64), (.mem (source s + 16) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 24) : Operand 64), (.mem (source s + 24) : Operand 64).read s⟩] }

def components (destination : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .rip, .mem destination 32]

theorem frame {s t : RamState} {ip : BitVec 64} {source destination : RamState → BitVec 64}
    (h : (effect ip source destination s).Holds s t) :
    AgreesExcept (components (destination s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [components]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (destination s) 32, by simp [components], ?_⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem copy_nat256 {s t : RamState} {entry : BitVec 64}
    {source destination : RamState → BitVec 64} {value : Nat}
    (h : (effect entry source destination s).Holds s t)
    (output : MemReadable t (destination s) 32)
    (scalar : Nat256At s (source s) value) : Nat256At t (destination s) value := by
  apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs scalar.1 output.mem
  intro j hj
  have values := h.writes
  simp only [effect, Write.AllHold] at values
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · have h0 : memLoad t.external (destination s) 64 = memLoad s.external (source s) 64 :=
      values.2.2.2.1
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      h0.trans (by simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using scalar.memLoad_limb 0 (by decide))
  · exact values.2.2.2.2.1.trans (scalar.memLoad_limb 1 (by decide))
  · exact values.2.2.2.2.2.1.trans (scalar.memLoad_limb 2 (by decide))
  · exact values.2.2.2.2.2.2.trans (scalar.memLoad_limb 3 (by decide))

end P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result
