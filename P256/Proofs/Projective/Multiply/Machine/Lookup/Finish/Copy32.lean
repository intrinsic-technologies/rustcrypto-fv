import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Field.Representation
import P256.Proofs.Projective.Multiply.Machine.Lookup.Memory
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stackPtr_read (s : RamState) : stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

abbrev CopyPre := Program.ScalarFrame.Copy32.Pre

def copyEffect (ip : BitVec 64) (src dst : Nat) (finalA : Nat) (copyB : Bool) (s : RamState) : Effect :=
  { rip := ip
    writes := [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (src+finalA)) : Operand 64).read s⟩] ++
      (if copyB then [⟨(.reg 1 : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (src+8)) : Operand 64).read s⟩] else []) ++
      [⟨(.mem (stackPtr s + BitVec.ofNat 64 dst) : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 src) : Operand 64).read s⟩,
       ⟨(.mem (stackPtr s + BitVec.ofNat 64 (dst+8)) : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (src+8)) : Operand 64).read s⟩,
       ⟨(.mem (stackPtr s + BitVec.ofNat 64 (dst+16)) : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (src+16)) : Operand 64).read s⟩,
       ⟨(.mem (stackPtr s + BitVec.ofNat 64 (dst+24)) : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (src+24)) : Operand 64).read s⟩] }

theorem copy_frame {s t : RamState} {ip : BitVec 64} {src dst finalA : Nat} {copyB : Bool}
    (effect : (copyEffect ip src dst finalA copyB s).Holds s t) :
    AgreesExcept [.reg 0, .reg 1, .mem (stackPtr s + BitVec.ofNat 64 dst) 32, .rip] s t := by
  apply effect.agrees.widen
  · intro c hc hm
    cases copyB <;>
      simp only [copyEffect, Bool.false_eq_true, ite_false, ite_true, List.append_nil,
        List.cons_append, List.nil_append, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp
  · intro a c hc ha
    cases copyB <;>
      simp only [copyEffect, Bool.false_eq_true, ite_false, ite_true, List.append_nil,
        List.cons_append, List.nil_append, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s + BitVec.ofNat 64 dst) 32, by simp, ?_⟩
      first
      | (refine ⟨i, by omega, ?_⟩; rfl)
      | (refine ⟨8+i, by omega, ?_⟩; solve | simp only [BitVec.ofNat_add, BitVec.add_assoc])
      | (refine ⟨16+i, by omega, ?_⟩; solve | simp only [BitVec.ofNat_add, BitVec.add_assoc])
      | (refine ⟨24+i, by omega, ?_⟩; solve | simp only [BitVec.ofNat_add, BitVec.add_assoc])

theorem copy_payload {s t : RamState} {ip : BitVec 64} {src dst finalA x : Nat} {copyB : Bool}
    (effect : (copyEffect ip src dst finalA copyB s).Holds s t)
    (input : MontgomeryAt s (stackPtr s + BitVec.ofNat 64 src) x)
    (output : MemReadable t (stackPtr s + BitVec.ofNat 64 dst) 32) :
    MontgomeryAt t (stackPtr s + BitVec.ofNat 64 dst) x := by
  apply Field.montgomeryAt_of_memLoad_limbs input.1 output.mem
  intro j hj
  apply Eq.trans _ (input.memLoad_limb j hj)
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  have writes := Write.allHold_iff.mp effect.writes
  have limb (k : Nat) (hk : k ∈ [0,8,16,24]) :
      memLoad t.external (stackPtr s + BitVec.ofNat 64 (dst+k)) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 (src+k)) 64 := by
    apply writes ⟨(Operand.mem (stackPtr s + BitVec.ofNat 64 (dst+k)) : Operand 64),
      memLoad s.external (stackPtr s + BitVec.ofNat 64 (src+k)) 64⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    all_goals cases copyB <;> simp [copyEffect, Operand.read]
  rcases cases with rfl | rfl | rfl | rfl
  · simpa only [Nat.add_zero, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using limb 0 (by simp)
  · simpa only [Nat.reduceMul, BitVec.ofNat_add, BitVec.add_assoc] using limb 8 (by simp)
  · simpa only [Nat.reduceMul, BitVec.ofNat_add, BitVec.add_assoc] using limb 16 (by simp)
  · simpa only [Nat.reduceMul, BitVec.ofNat_add, BitVec.add_assoc] using limb 24 (by simp)

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
