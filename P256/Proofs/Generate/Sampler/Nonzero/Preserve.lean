import P256.Proofs.Generate.Sampler.Nonzero.Clear
import P256.Proofs.Generate.Sampler.Nonzero.Zero
import P256.Proofs.Generate.Sampler.Nonzero.Choice
import P256.Proofs.Generate.Sampler.Entry

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

def tailClobbers (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.flags,.rip,
    .mem (stackPtr s-160) 8,.mem (stackPtr s-168) 8,.mem (stackPtr s-176) 8,
    .mem (stackPtr s-184) 8,.mem (stackPtr s-272) 8,.mem (stackPtr s-280) 8,
    .mem (stackPtr s-288) 8,.mem (stackPtr s-273) 1]

theorem tail_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (g : AgreesExcept (tailClobbers s) t u)
    {off len : Nat} (lower : 48+len ≤ off) (upper : off ≤ 152 ∨ 184+len ≤ off ∧ off ≤ 264) (i : Nat) (hi : i<len) :
    u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
    t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  apply g.byte
  intro c hc cover
  have bounds := stack_bounds pre.stack
  have addr : (stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat-off+i := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i<2^64),
      Nat.mod_eq_of_lt (by rw [stack_sub_toNat pre.stack (by omega)]; omega),
      stack_sub_toNat pre.stack (by omega)]
  have apart (start size : Nat) (hs : start ≤ 3624) (hz : size ≤ start+8)
      (disjoint : start+len ≤ off ∨ off+size ≤ start) :
      ¬ (Component.mem (stackPtr s-BitVec.ofNat 64 start) size).Covers
        (stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i) := by
    rintro ⟨j,hj,eq⟩
    have target : (stackPtr s-BitVec.ofNat 64 start+BitVec.ofNat 64 j).toNat =
        (stackPtr s).toNat-start+j := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j<2^64),
        Nat.mod_eq_of_lt (by rw [stack_sub_toNat pre.stack hs]; omega),stack_sub_toNat pre.stack hs]
    have h := congrArg BitVec.toNat eq
    rw [addr,target] at h
    rcases disjoint with h | h <;> omega
  simp only [tailClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · exact apart 160 8 (by decide) (by decide) (by omega) cover
  · exact apart 168 8 (by decide) (by decide) (by omega) cover
  · exact apart 176 8 (by decide) (by decide) (by omega) cover
  · exact apart 184 8 (by decide) (by decide) (by omega) cover
  · exact apart 272 8 (by decide) (by decide) (by omega) cover
  · exact apart 280 8 (by decide) (by decide) (by omega) cover
  · exact apart 288 8 (by decide) (by decide) (by omega) cover
  · exact apart 273 1 (by decide) (by decide) (by omega) cover

theorem clear_tail [Bindings] {s t u : RamState} (state : State s t)
    (g : AgreesExcept (clearClobbers t) t u) : AgreesExcept (tailClobbers s) t u := by
  have addr (off : Nat) (h : off ≤ 264) :=
    scalar_stack_address (frameOffset := 264) state.rsp (by decide) h
  have h128 := addr 104 (by decide)
  have h136 := addr 96 (by decide)
  have h144 := addr 88 (by decide)
  have h152 := addr 80 (by decide)
  simp only [clearClobbers,BitVec.ofNat_eq_ofNat,h128,h136,h144,h152] at g
  exact g.mono (by simp [tailClobbers])

end P256.Proofs.Generate.Sampler.Nonzero
