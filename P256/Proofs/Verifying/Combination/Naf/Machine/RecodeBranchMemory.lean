import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem append_padding [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {i k : Nat} {d : Int} (pre : Pre s boundary) (bound : i+k ≤ 256) (pos : 0<k)
    (first : t.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
      some (UInt8.ofNat (BitVec.ofInt 8 d).toNat))
    (zeroes : Bytes u.external (s.regValue .rdi+BitVec.ofNat 64 (i+1)) (k-1) (fun _ => 0))
    (memory : MemoryWriteFrame t u #v[digitRegion s (i+1) (k-1)]) :
    Bytes u.external (s.regValue .rdi+BitVec.ofNat 64 i) (d::List.replicate (k-1) 0).length
      (fun j => UInt8.ofNat (BitVec.ofInt 8 (((d::List.replicate (k-1) 0)[j]?).getD 0)).toNat) := by
  have low : (s.regValue .rdi).toNat+257 < 2^32 := pre.outputBounded
  have addr : (s.regValue .rdi+BitVec.ofNat 64 i).toNat = (s.regValue .rdi).toNat+i :=
    toNat_add_ofNat _ _ (by omega)
  have next : (s.regValue .rdi+BitVec.ofNat 64 (i+1)).toNat = (s.regValue .rdi).toNat+(i+1) :=
    toNat_add_ofNat _ _ (by omega)
  intro j hj
  cases j with
  | zero =>
    simp only [BitVec.add_zero, List.getElem?_cons_zero, Option.getD_some]
    rw [memory _]
    · exact first
    · intro region hr hin
      have same : region = digitRegion s (i+1) (k-1) := by simpa using hr
      subst region
      change (s.regValue .rdi+BitVec.ofNat 64 (i+1)).toNat ≤ _ ∧ _ < _ at hin
      rw [next, addr] at hin
      omega
  | succ j =>
    have small : j < k-1 := by
      simp only [List.length_cons, List.length_replicate] at hj
      omega
    have bytes := zeroes j small
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at bytes ⊢
    have address : i+1+j = i+(j+1) := by omega
    rw [address] at bytes
    simpa [small] using bytes

theorem slice_frame_trans [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}
    {i k : Nat} (pre : Pre s boundary) (bound : i+k ≤ 256) (pos : 0<k)
    (first : MemoryWriteFrame t u #v[digitRegion s i 1])
    (padding : MemoryWriteFrame u v #v[digitRegion s (i+1) (k-1)]) :
    MemoryWriteFrame t v #v[digitRegion s i k] := by
  have low : (s.regValue .rdi).toNat+257 < 2^32 := pre.outputBounded
  have addr : (s.regValue .rdi+BitVec.ofNat 64 i).toNat = (s.regValue .rdi).toNat+i :=
    toNat_add_ofNat _ _ (by omega)
  have next : (s.regValue .rdi+BitVec.ofNat 64 (i+1)).toNat = (s.regValue .rdi).toNat+(i+1) :=
    toNat_add_ofNat _ _ (by omega)
  intro a outside
  rw [padding a, first a]
  · intro region hr hin
    have same : region = digitRegion s i 1 := by simpa using hr
    subst region
    apply outside (digitRegion s i k) (by simp)
    change (s.regValue .rdi+BitVec.ofNat 64 i).toNat ≤ _ ∧
      _ < (s.regValue .rdi+BitVec.ofNat 64 i).toNat+k
    change (s.regValue .rdi+BitVec.ofNat 64 i).toNat ≤ _ ∧
      _ < (s.regValue .rdi+BitVec.ofNat 64 i).toNat+1 at hin
    omega
  · intro region hr hin
    have same : region = digitRegion s (i+1) (k-1) := by simpa using hr
    subst region
    apply outside (digitRegion s i k) (by simp)
    change (s.regValue .rdi+BitVec.ofNat 64 i).toNat ≤ _ ∧
      _ < (s.regValue .rdi+BitVec.ofNat 64 i).toNat+k
    change (s.regValue .rdi+BitVec.ofNat 64 (i+1)).toNat ≤ _ ∧
      _ < (s.regValue .rdi+BitVec.ofNat 64 (i+1)).toNat+(k-1) at hin
    rw [next] at hin
    rw [addr]
    omega

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
