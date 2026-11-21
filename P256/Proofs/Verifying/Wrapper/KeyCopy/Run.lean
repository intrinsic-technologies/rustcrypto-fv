import P256.Proofs.Verifying.Wrapper.KeyCopy.HeadResult
import P256.Proofs.Verifying.Wrapper.KeyCopy.Words
import P256.Proofs.Verifying.Wrapper.KeyCopy.TailResult

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem words_complete [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre 0x103088 s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep t)
    (state : Words.State s t 0) (n : Nat) (bound : n ≤ 7) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧ Words.State s u n := by
  induction n with
  | zero => exact ⟨0,t,.refl _,ready,state⟩
  | succ n ih =>
    obtain ⟨fuel,u,run,ru,su⟩ := ih (by omega)
    obtain ⟨fuel',v,run',rv,sv⟩ := Words.step pre loaded outside ru su (by omega)
    exact ⟨fuel+fuel',v,run.trans run',rv,sv⟩

theorem copy_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre 0x103088 s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      AgreesExcept (components s) s t ∧ t.RIP = 0x1030e6 ∧
      ∀ i < 65, t.external[stackPtr s + BitVec.ofNat 64 i]? =
        s.external[s.regValue .rdx + BitVec.ofNat 64 i]? := by
  obtain ⟨nf,a,runA,ra,_,ea⟩ := Head.run boundary outside s ready
    (programText_slice (programLoaded_codeIn loaded) 0x3088 Head.bytes
      (by decide) (by decide +kernel)) pre
  have stateA : Words.State s a 0 :=
    ⟨ea.rip, Head.frame ea, ea.writes.2.2,
      fun i hi => Head.copied pre ea i (by omega)⟩
  obtain ⟨nw,b,runB,rb,stateB⟩ := words_complete pre loaded outside ra stateA 7 (by decide)
  have sp : stackPtr b = stackPtr s :=
    stateB.frame.read (n := 64) (r := 4) (by simp [components])
  have source : b.regValue .rdx = s.regValue .rdx :=
    stateB.frame.read (n := 64) (r := 2) (by simp [components])
  have before : Pre 0x1030d9 b := pre.after stateB.frame stateB.rip
  obtain ⟨nt,t,runT,rt,_,et⟩ := Tail.run boundary outside b rb
    (pre.code stateB.frame (by decide)
      (programText_slice (programLoaded_codeIn loaded) 0x30d9 Tail.bytes
        (by decide) (by decide +kernel))) before
  have ag : AgreesExcept (components s) b t := by
    simpa only [components, sp] using Tail.wide et
  have total : AgreesExcept (components s) s t :=
    (stateB.frame.trans ag).mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)
  have values : t.regValue .rcx = (memLoad b.external (b.regValue .rdx+63) 16).setWidth 64 ∧
      memLoad t.external (stackPtr b+63) 16 = memLoad b.external (b.regValue .rdx+63) 16 ∧
      memLoad t.external (stackPtr b+3) 32 = (Operand.reg 0 : Operand 32).read b := et.writes
  have rax : (Operand.reg 0 : Operand 32).read b = memLoad s.external (s.regValue .rdx+3) 32 := by
    change (b.regValue .rax).setWidth 32 = _
    rw [stateB.rax]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  have copied3 := chunk_bytes pre total.grow 3 32 (by decide)
    (by rw [sp] at values; exact values.2.2.trans rax)
  have copied63 := chunk_bytes pre total.grow 63 16 (by decide) (by
    rw [sp, source] at values
    exact values.2.1.trans (pre.source_load stateB.frame (off := 63) (n := 16) (by decide)))
  refine ⟨nf+nw+nt,t,(runA.trans runB).trans runT,rt,total,et.rip,?_⟩
  intro i hi
  by_cases first : i < 3
  · have unchanged := Tail.preserved et (Or.inl first)
    rw [sp] at unchanged
    exact unchanged.trans (stateB.copied i (Or.inl first))
  by_cases middle : i < 7
  · simpa only [Nat.add_sub_of_le (show 3 ≤ i by omega)] using copied3 (i-3) (by omega)
  by_cases words : i < 63
  · have unchanged := Tail.preserved et (Or.inr ⟨by omega,words⟩)
    rw [sp] at unchanged
    exact unchanged.trans (stateB.copied i (Or.inr ⟨by omega,by omega⟩))
  · simpa only [Nat.add_sub_of_le (show 63 ≤ i by omega)] using copied63 (i-63) (by omega)

end P256.Proofs.Verifying.Wrapper.KeyCopy
