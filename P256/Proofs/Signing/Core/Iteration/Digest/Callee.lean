import P256.Proofs.Signing.Core.Iteration.Digest.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem NonceState.after_agrees [Bindings] {s t u : RamState} {state : Nonce.State} {nonce : Nat}
    {cs : List Component} (input : NonceState s t state nonce) (frame : Frame s u)
    (agrees : AgreesExcept cs t u) (memory : Preserved s t u)
    (safe : ∀ r ∈ [5,13,14,15], Component.reg r ∉ cs) : NonceState s u state nonce := by
  apply input.copy frame memory
  intro reg member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact agrees.read (n := 64) (r := 5) (safe 5 (by simp))

  · exact agrees.read (n := 64) (r := 13) (safe 13 (by simp))
  · exact agrees.read (n := 64) (r := 14) (safe 14 (by simp))
  · exact agrees.read (n := 64) (r := 15) (safe 15 (by simp))

theorem NonceState.after_result [Bindings] {s t v u : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce : Nat} {target ret : BitVec 64} {outputBytes reserve output : Nat}
    (pre : SignPre s boundary) (input : NonceState s t state nonce) (ready : ReadyToStep v)
    (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (result : CalleeResult v u boundary outputBytes reserve)
    (capacity : 2288+reserve ≤ 4584) (bound : output+outputBytes ≤ 2232)
    (di : t.regValue .rdi = frameBase s+BitVec.ofNat 64 output)
    (apart : ∀ offset, LiveOffset offset → offset < output ∨ output+outputBytes ≤ offset) :
    NonceState s u state nonce := by
  apply input.copy (after_call pre input.frame ready effect result capacity bound di)
  · intro i hi
    have h := local_result_copy pre input.frame effect result di
      (offset := i) (len := 1) (by unfold LiveOffset at hi; omega) (by omega)
      (by have := apart i hi; omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · intro reg member
    have saved := result.calleeSaved reg (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl|rfl|rfl|rfl <;> simp)
    apply saved.trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)

    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Iteration.Digest
