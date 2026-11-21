import P256.Proofs.Verifying.Wrapper.SignatureCopy.Step
import P256.Proofs.Verifying.Wrapper.SignatureCopy.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def codeOffset (n : Nat) : Nat := if n < 2 then 0x314b+13*n else 0x3165+10*(n-2)

theorem word_step [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (n : Nat) (bound : n < 6)
    (rip : s.RIP = Extracted.textAddress+BitVec.ofNat 64 (codeOffset n)) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = Extracted.textAddress+BitVec.ofNat 64 (codeOffset (n+1)) ∧
      memLoad t.external (stackPtr s+BitVec.ofNat 64 (56-8*n)) 64 =
        memLoad s.external (stackPtr s+BitVec.ofNat 64 (136-8*n)) 64 ∧
      AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 (56-8*n)) 8,.rip] s t := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step32 call state outside 0x314b 136 56 136 56 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) rip
  · exact step32 call state outside 0x3158 128 48 128 48 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) rip
  · exact step8 call state outside 0x3165 120 40 120 40 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) rip
  · exact step8 call state outside 0x316f 112 32 112 32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) rip
  · exact step8 call state outside 0x3179 104 24 104 24 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) rip
  · exact step8 call state outside 0x3183 96 16 96 16 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) rip

structure WordsState [Bindings] (initial start s : RamState) (n : Nat) : Prop
    extends ReturnState initial s where
  rip : s.RIP = Extracted.textAddress+BitVec.ofNat 64 (codeOffset n)
  agrees : AgreesExcept (components start) start s
  copied : ∀ j < 8, 8-n ≤ j →
    memLoad s.external (stackPtr start+BitVec.ofNat 64 (8*j)) 64 =
      memLoad start.external (stackPtr start+BitVec.ofNat 64 (80+8*j)) 64

theorem words_step [Bindings] {initial start s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {n : Nat}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (initialState : ReturnState initial start)
    (state : WordsState initial start s n) (bound : n < 6)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ WordsState initial start t (n+1) := by
  obtain ⟨fuel,t,run,stateT,ripT,value,ag⟩ := word_step call state.toReturnState outside n bound state.rip
  have sp : stackPtr s = stackPtr start :=
    state.agrees.read (n := 64) (r := 4) (by simp [components])
  have wide := word_frame ag (by omega)
  have full : AgreesExcept (components start) start t := by
    rw [components,sp] at wide
    exact (state.agrees.trans wide).mono (by simp [components])
  refine ⟨fuel,t,run,⟨stateT,ripT,full,?_⟩⟩
  intro j hj lower
  by_cases same : j = 7-n
  · have dst : 8*j = 56-8*n := by omega
    have src : 80+8*j = 136-8*n := by omega
    rw [sp,← dst,← src] at value
    exact value.trans (source_read initialState call.stackAvailable.1 state.agrees
      (offset := 8*j) (by omega))
  · have prior : 8-n ≤ j := by omega
    have preserved := word_read state.toReturnState call.stackAvailable.1 ag
      (query := 8*j) (by omega) (by omega) (Or.inl (by omega))
    rw [sp] at preserved
    exact preserved.trans (state.copied j hj prior)

theorem words_complete [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x10314b) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ WordsState initial s t 6 := by
  have first : WordsState initial s s 0 := by
    refine ⟨state,rip,.refl _ _,?_⟩
    intro j hj lower
    omega
  have loop (n : Nat) (bound : n ≤ 6) :
      ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ WordsState initial s t n := by
    induction n with
    | zero => exact ⟨0,s,.refl _,first⟩
    | succ n ih =>
      obtain ⟨fuel,t,run,st⟩ := ih (by omega)
      obtain ⟨fuel',u,run',su⟩ := words_step call state st (by omega) outside
      exact ⟨fuel+fuel',u,run.trans run',su⟩
  exact loop 6 (by decide)

end P256.Proofs.Verifying.Wrapper.SignatureCopy
