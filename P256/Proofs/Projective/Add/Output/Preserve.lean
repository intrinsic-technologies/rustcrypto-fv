import P256.Proofs.Projective.Add.Output.Copy

set_option autoImplicit false


namespace P256.Proofs.Projective.Add.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

omit [Bindings] in
theorem montgomery_external {address : BitVec 64} {value : Nat}
    (memory : u.external = t.external) (input : MontgomeryAt t address value) :
    MontgomeryAt u address value := by
  simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, memory] using input

theorem copy_stack_stack {dst off value : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (agrees : AgreesExcept (Copy32.components (stackPtr s - BitVec.ofNat 64 dst)) t u)
    (hd : dst ≤ 632) (ho : off ≤ 632) (ld : 32 ≤ dst + 8) (lo : 32 ≤ off + 8)
    (apart : off + 32 ≤ dst ∨ dst + 32 ≤ off)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 off) value) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 off) value :=
  Copy.preserves agrees
    (stack_sub_apart pre.stack (by omega) (by omega) ld lo apart) input

theorem copy_stack_output {dst off value : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (agrees : AgreesExcept (Copy32.components (stackPtr s - BitVec.ofNat 64 dst)) t u)
    (hd : dst ≤ 632) (ld : 32 ≤ dst + 8) (ho : off + 32 ≤ 96)
    (input : MontgomeryAt t (s.regValue .rdi + BitVec.ofNat 64 off) value) :
    MontgomeryAt u (s.regValue .rdi + BitVec.ofNat 64 off) value := by
  apply Copy.preserves agrees _ input
  intro i hi j hj he
  exact stack_apart pre ho (by omega) ld j hj i hi he.symm

theorem copy_output_stack {dst off value : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (agrees : AgreesExcept (Copy32.components (s.regValue .rdi + BitVec.ofNat 64 dst)) t u)
    (hd : dst + 32 ≤ 96) (ho : off ≤ 632) (lo : 32 ≤ off + 8)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 off) value) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 off) value :=
  Copy.preserves agrees (stack_apart pre hd (by omega) lo) input

theorem copy_output_output {dst off value : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (agrees : AgreesExcept (Copy32.components (s.regValue .rdi + BitVec.ofNat 64 dst)) t u)
    (hd : dst + 32 ≤ 96) (ho : off + 32 ≤ 96)
    (apart : dst + 32 ≤ off ∨ off + 32 ≤ dst)
    (input : MontgomeryAt t (s.regValue .rdi + BitVec.ofNat 64 off) value) :
    MontgomeryAt u (s.regValue .rdi + BitVec.ofNat 64 off) value := by
  apply Copy.preserves agrees _ input
  have hb : (s.regValue .rdi).toNat + 96 < 2^32 := pre.outputBounded
  have hd' : (s.regValue .rdi + BitVec.ofNat 64 dst).toNat = (s.regValue .rdi).toNat + dst := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have ho' : (s.regValue .rdi + BitVec.ofNat 64 off).toNat = (s.regValue .rdi).toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply RangeApart.of_toNat
  · rw [hd']; omega
  · rw [ho']; omega
  · rw [hd', ho']; omega

end P256.Proofs.Projective.Add.Output
