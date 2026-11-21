import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Field.Preserve
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}

theorem stack_address (state : Frame s t) {off : Nat} (bound : off ≤ 760) :
    stackPtr t + BitVec.ofNat 64 off = stackPtr s - BitVec.ofNat 64 (760-off) :=
  ScalarFrame.scalar_stack_address state.rsp (by decide) bound

theorem stack_writable (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    {off len : Nat} (bound : off + len ≤ 760) (positive : 0 < len)
    (aligned : off % 8 + len ≤ 8) :
    MemWritable t (stackPtr t + BitVec.ofNat 64 off) len := by
  rw [stack_address state (by omega)]
  apply writable_of_grow (stack_sub_writable pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by omega) (by omega) positive ?_)
    state.allocated
  rw [stack_sub_toNat pre.stack (by omega)]
  have sp : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
  have bounds := stack_bounds pre.stack
  have hmod := Nat.mod_mod_of_dvd ((stackPtr s).toNat - (760-off)) (show 8 ∣ 4096 by decide)
  have hs : ((stackPtr s).toNat - (760-off)) % 8 = off % 8 := by omega
  omega

theorem stack_effect_frame (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    {cs : List Component} (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, c.isMem = true → ∃ off len : Nat,
      c = .mem (stackPtr t + BitVec.ofNat 64 off) len ∧ off + len ≤ 712)
    (rsp : .reg 4 ∉ cs) (df : .df ∉ cs) (mxcsr : .mxcsr ∉ cs) (fcw : .fcw ∉ cs) :
    Frame s u := by
  apply state.after_effect pre.toCalleePre (by decide) ready agrees ?_ rsp df mxcsr fcw
  intro c hc a ha
  have isMem : c.isMem = true := by cases c <;> first | rfl | exact ha.elim
  obtain ⟨off,len,rfl,bound⟩ := memory c hc isMem
  refine ⟨ScalarFrame.workRegion s 3360, by simp, ?_⟩
  rw [stack_address state (by omega)] at ha
  exact ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha

omit [Bindings] in
theorem effect_byte {t u : RamState} {cs : List Component}
    (agrees : AgreesExcept cs t u) {off len : Nat} (bound : off+len ≤ 2^64)
    (apart : ∀ c ∈ cs, c.isMem = true → ∃ a n : Nat,
      c = .mem (stackPtr t + BitVec.ofNat 64 a) n ∧ a+n ≤ 2^64 ∧
      (a+n ≤ off ∨ off+len ≤ a)) {i : Nat} (hi : i < len) :
    u.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  have isMem : c.isMem = true := by cases c <;> first | rfl | exact ha.elim
  obtain ⟨a,n,rfl,an,disjoint⟩ := apart c hc isMem
  obtain ⟨j,hj,eq⟩ := ha
  exact RangeApart.offsets (stackPtr t) an bound disjoint j hj i hi eq.symm

omit [Bindings] in
theorem effect_read {t u : RamState} {cs : List Component}
    (agrees : AgreesExcept cs t u) {off n : Nat} (bound : off+n/8 ≤ 2^64)
    (apart : ∀ c ∈ cs, c.isMem = true → ∃ a len : Nat,
      c = .mem (stackPtr t + BitVec.ofNat 64 a) len ∧ a+len ≤ 2^64 ∧
      (a+len ≤ off ∨ off+n/8 ≤ a)) :
    memLoad u.external (stackPtr t+BitVec.ofNat 64 off) n =
      memLoad t.external (stackPtr t+BitVec.ofNat 64 off) n := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun x : Option UInt8 => x.getD 0) (effect_byte agrees bound apart hi)

theorem zero_value (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    {off : Nat} (bound : off+32 ≤ 760)
    (grow : ∀ a : BitVec 64, (t.external[a]?).isSome → (u.external[a]?).isSome)
    (limbs : ∀ j < 4, memLoad u.external
      (stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 (8*j)) 64 = 0) :
    Field.MontgomeryAt u (stackPtr t+BitVec.ofNat 64 off) 0 := by
  apply Field.montgomeryAt_of_memLoad_limbs (by decide +kernel)
  · intro i hi
    exact grow _ ((ScalarFrame.stack_readable pre.toCalleePre state (by decide) bound).mem i hi)
  · intro j hj
    simpa only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div, BitVec.ofNat_eq_ofNat] using limbs j hj

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
