import P256.Proofs.Verifying.Wrapper.KeyCopy.WordResult

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Words

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def pc (n : Nat) : BitVec 64 := 0x10309a + BitVec.ofNat 64 (9*n)

structure State (s t : RamState) (n : Nat) : Prop where
  rip : t.RIP = pc n
  frame : AgreesExcept (components s) s t
  rax : t.regValue .rax = (memLoad s.external (s.regValue .rdx+3) 32).setWidth 64
  copied : ∀ i : Nat, i < 3 ∨ (7 ≤ i ∧ i < 7+8*n) →
    t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 i]?

theorem offset_eq {n : Nat} (bound : n < 7) :
    (BitVec.ofNat 8 (7+8*n)).signExtend 64 = BitVec.ofNat 64 (7+8*n) := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem code_eq {n : Nat} (bound : n < 7) :
    Extracted.textBytes.toListFrom (0x309a+9*n) (Word.bytes (BitVec.ofNat 8 (7+8*n))).length =
      Word.bytes (BitVec.ofNat 8 (7+8*n)) := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem pc_succ (n : Nat) : pc n + 9 = pc (n+1) := by
  simp only [pc, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem step [Bindings] {s t : RamState} {n : Nat} {boundary : ReturnBoundary}
    (pre : Pre 0x103088 s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep t)
    (state : State s t n) (bound : n < 7) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧ State s u (n+1) := by
  have before := pre.after state.frame state.rip
  have sp : stackPtr t = stackPtr s := state.frame.read (n := 64) (r := 4) (by simp [components])
  have source : t.regValue .rdx = s.regValue .rdx :=
    state.frame.read (n := 64) (r := 2) (by simp [components])
  have offset := offset_eq bound
  have size : 0x309a+9*n+(Word.bytes (BitVec.ofNat 8 (7+8*n))).length ≤ 118431 := by
    simp only [Word.bytes, List.length_cons, List.length_nil]
    omega
  have code := pre.code state.frame size
    (programText_slice (programLoaded_codeIn loaded) (0x309a+9*n)
      (Word.bytes (BitVec.ofNat 8 (7+8*n))) size (code_eq bound))
  have pcEq : Extracted.textAddress + BitVec.ofNat 64 (0x309a+9*n) = pc n := by
    simp only [BitVec.ofNat_add, pc, Extracted.textAddress, ← BitVec.add_assoc]
    rfl
  rw [pcEq] at code
  have next (i : Nat) (ibound : i ≤ 9) : pc n + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply boundary_ne_program outside
    have h := inProgram_of_textOffset (0x309a+9*n+i) (by omega)
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc, pc, Extracted.textAddress] using h
  obtain ⟨fuel,u,run,ru,_,eff⟩ := Word.run boundary (pc n) (BitVec.ofNat 8 (7+8*n))
    (next 4 (by decide)) (next 9 (by decide)) t ready code
    ⟨state.rip, by simpa [offset, stackPtr, State.regValue, Syntax.Reg.fin, Operand.read_reg64, gprIndex] using before.readable (7+8*n) 8 (by omega),
      by simpa [offset, stackPtr, State.regValue, Syntax.Reg.fin, Operand.read_reg64, gprIndex] using before.writable.add (7+8*n) (show 7+8*n+8 ≤ 65 by omega),
      by simpa [offset, pcEq, stackPtr, State.regValue, Syntax.Reg.fin, Operand.read_reg64, gprIndex] using
        before.codeApart (7+8*n) 8 (by omega) (0x309a+9*n) 9 (by omega)⟩
  have ag := Word.wide eff offset (by omega)
  have ag' : AgreesExcept (components s) t u := by simpa only [components, sp] using ag
  have total : AgreesExcept (components s) s u :=
    (state.frame.trans ag').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)
  refine ⟨fuel,u,run,ru,eff.rip.trans (pc_succ n),total,
    ((Word.frame eff).read (n := 64) (r := 0) (by simp)).trans state.rax, ?_⟩
  intro i hi
  by_cases old : i < 7+8*n
  · have oldCopied := state.copied i (by omega)
    have unchanged := Word.preceding eff offset (by omega) old
    rw [sp] at unchanged
    exact unchanged.trans oldCopied
  · have newCopied := Word.copied before eff offset (by omega) (i-(7+8*n)) (by omega)
    rw [Nat.add_sub_of_le (show 7+8*n ≤ i by omega), sp, source] at newCopied
    exact newCopied.trans (pre.source_byte state.frame (by omega))

end P256.Proofs.Verifying.Wrapper.KeyCopy.Words
