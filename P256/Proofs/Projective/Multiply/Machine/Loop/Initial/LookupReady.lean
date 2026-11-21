import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Copy
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Arguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Interface

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_lookup [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x1032df ∧ ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      ProjectiveAt t (stackPtr s - 144) Projective.identity ∧
      t.regValue .rdi = stackPtr s - 240 ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.regValue .rdx = (memLoad s.external (s.regValue .rcx + 64) 8).setWidth 64 ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .rbp = s.regValue .rcx ∧
      t.regValue .r12 = stackPtr s - 240 ∧ t.regValue .r13 = 0 ∧
      t.regValue .r14 = stackPtr s - 144 ∧ t.regValue .r15 = s.regValue .rsi ∧
      memLoad t.external (stackPtr s - 376) 64 = 65 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, point, copy, bx, r9, r15, r13, r14, counter, output⟩ :=
    initialize_copy pre.toCalleePre pre.tableCount pre.digitCount
  have readable : MemReadable u (u.regValue .r9 + u.regValue .r13 + 64) 1 := by
    have addr : u.regValue .r9 + u.regValue .r13 + 64 = s.regValue .rcx + 64 := by
      rw [r9, r13]
      change (s.regValue .rcx + (0 : BitVec 64)) + (64 : BitVec 64) = _
      simp
    rw [addr]
    exact pre.digit_readable state (i := 64) (by decide)
  obtain ⟨m, t, step, ready, _, effect⟩ := arguments_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x32c8 argumentsBytes
      (by decide) (by decide +kernel)) ⟨rip, readable⟩
  have agrees : AgreesExcept [.reg 2, .reg 12, .reg 7, .reg 6, .reg 5, .rip] u t :=
    effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := state.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have dst : stackPtr u + 136 = stackPtr s - 240 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have values := effect.writes
  change t.regValue .rdx = (memLoad u.external
      (u.regValue .r9 + u.regValue .r13 + 64) 8).setWidth 64 ∧
    t.regValue .r12 = stackPtr u + 136 ∧ t.regValue .rdi = stackPtr u + 136 ∧
    t.regValue .rsi = u.regValue .r15 ∧ t.regValue .rbp = u.regValue .r9 at values
  have addr : u.regValue .r9 + u.regValue .r13 + 64 = s.regValue .rcx + 64 := by
    rw [r9, r13]
    change (s.regValue .rcx + (0 : BitVec 64)) + (64 : BitVec 64) = _
    simp
  rw [addr, dst, r15, r9] at values
  have digit : memLoad u.external (s.regValue .rcx + 64) 8 =
      memLoad s.external (s.regValue .rcx + 64) 8 := pre.digit_value state (i := 64) (by decide)
  rw [digit] at values
  refine ⟨n+m, t, run.trans step, frame, effect.rip, ?_, ?_, values.2.2.1,
    values.2.2.2.1, values.1, ?_, values.2.2.2.2, values.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact point.of_bytes_eq (by intro i hi; rw [memory])
  · exact copy.of_bytes_eq (by intro i hi; rw [memory])
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans bx
  · exact (agrees.read (n := 64) (r := 13) (by simp)).trans r13
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans r14
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans r15
  · rw [memory]; exact counter
  · rw [memory]; exact output

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
