import Sha1.Proofs.Compress.Routine.Frame
import Sha1.Proofs.Compress.Routine.State


namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

section

variable (hBlock : Machine.BlockCorrect) (bindings : Bindings) (boundary : ReturnBoundary)
  (c : Context) (hv : c.Valid bindings) (hOutside : Machine.OutsideCompression boundary.rip)
  (R : Nat → RamState → RamState → Prop) (Q : RamState → Prop)

include hBlock hv hOutside

theorem finishFrom_rel
    (hNext : ∀ k H s, k < c.count → @ReadyToStep bindings s →
      CodeIn Extracted.programImage s → s.RIP = 0x1036a2 → AtBlock c k H s →
      ∃ n t, @Advances bindings boundary n s t ∧ @ReadyToStep bindings t ∧
        CodeIn Extracted.programImage t ∧
        t.RIP = (if k + 1 < c.count then 0x102530 else 0x1036b4) ∧ AtBlock c (k + 1) H t ∧
        AgreesExcept (frameComponents c.stack) c.initial t)
    (hFinish : ∀ s, @ReadyToStep bindings s → CodeIn Extracted.programImage s →
      s.RIP = 0x1036b4 → AtBlock c c.count (c.state c.count) s →
      ∃ n t, R n s t ∧ @ReadyToStep bindings t ∧ Q t)
    (hJoin : ∀ {n m s t u}, @Advances bindings boundary n s t → R m t u → R (n + m) s u)
    (k : Nat) (hk : k < c.count) (s : RamState)
    (hReady : @ReadyToStep bindings s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x102530) (hAt : AtBlock c k (c.state k) s) :
    ∃ n t, R n s t ∧ @ReadyToStep bindings t ∧ Q t := by
  letI := bindings
  obtain ⟨n, t, hAdvance, hReady', hCode', hRip', hData', hAgree⟩ :=
    hBlock boundary s c.stack (c.input k) (c.state k) (c.message k)
      hOutside hReady hCode hRip (atBlock_blockData hv hk hAt)
  have hAt' : AtBlock c k (c.state (k + 1)) t := by
    rw [c.state_succ hk]
    exact ⟨Frame.of_agrees hv hAt.frame hAgree, hData'.registers, hData'.inputPointer,
      (hAt.agrees.trans hAgree).mono (by simp [frameComponents, Machine.scratchComponents])⟩
  obtain ⟨m, u, hAdvance', hReady'', hCode'', hRip'', hAt'', _⟩ :=
    hNext k (c.state (k + 1)) t hk hReady' hCode' hRip' hAt'
  by_cases hn : k + 1 < c.count
  · simp only [hn, ↓reduceIte] at hRip''
    obtain ⟨r, v, hRun, hReady''', hResult⟩ :=
      finishFrom_rel hNext hFinish hJoin (k + 1) hn u hReady'' hCode'' hRip'' hAt''
    exact ⟨n + m + r, v, hJoin (hAdvance.trans hAdvance') hRun, hReady''', hResult⟩
  · have he : k + 1 = c.count := by omega
    simp only [hn, ↓reduceIte] at hRip''
    rw [he] at hAt''
    obtain ⟨r, v, hRun, hReady''', hResult⟩ := hFinish u hReady'' hCode'' hRip'' hAt''
    exact ⟨n + m + r, v, hJoin (hAdvance.trans hAdvance') hRun, hReady''', hResult⟩
termination_by c.count - k

end

end Sha1.Proofs.Compress.Routine

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

theorem finishFrom (hBlock : Machine.BlockCorrect) (hNext : NextCorrect)
    (hFinish : FinishCorrect) (bindings : Bindings) (c : Context) (hv : c.Valid bindings)
    (k : Nat) (hk : k < c.count) (s : RamState)
    (hReady : @ReadyToStep bindings s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x102530) (hAt : AtBlock c k (c.state k) s) :
    ∃ n t, @Returns bindings (returnBoundary c.initial) n s t ∧
      @ReadyToStep bindings t ∧ Result c t := by
  letI := bindings
  exact finishFrom_rel (hBlock := hBlock) (bindings := bindings)
    (boundary := returnBoundary c.initial) (c := c) (hv := hv) (hOutside := hv.outside)
    (R := fun n s t ↦ @Returns bindings (returnBoundary c.initial) n s t) (Q := Result c)
    (hNext bindings c hv) (hFinish bindings c hv)
    (fun ha hb ↦ ha.returns hb) k hk s hReady hCode hRip hAt

theorem execution_of_parts (hBlock : Machine.BlockCorrect) (hPrologue : PrologueCorrect)
    (hNext : NextCorrect) (hFinish : FinishCorrect)
    (bindings : Bindings) (c : Context) (hv : c.Valid bindings) (hn : 0 < c.count) :
    ∃ n t, @Returns bindings (returnBoundary c.initial) n c.initial t ∧
      @ReadyToStep bindings t ∧ Result c t := by
  letI := bindings
  obtain ⟨n, s, hAdvance, hReady, hCode, hRip, hAt⟩ := hPrologue bindings c hv hn
  rw [← c.state_zero] at hAt
  obtain ⟨m, t, hReturn, hReady', hResult⟩ :=
    finishFrom hBlock hNext hFinish bindings c hv 0 hn s hReady hCode hRip hAt
  exact ⟨n + m, t, hAdvance.returns hReturn, hReady', hResult⟩


end Sha1.Proofs.Compress.Routine
