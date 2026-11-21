import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.LookupReady
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_lookup_call [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 384 ∧
      CalleePre t boundary 0x1044a0 768 96 496 ∧
      (returnBoundary t).rip = 0x1032e4 ∧
      ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      ProjectiveAt t (stackPtr s - 144) Projective.identity ∧
      t.regValue .rdi = stackPtr s - 240 ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.regValue .rdx = (memLoad s.external (s.regValue .rcx + 64) 8).setWidth 64 ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .rbp = s.regValue .rcx ∧
      t.regValue .r12 = stackPtr s - 240 ∧ t.regValue .r13 = 0 ∧
      t.regValue .r14 = stackPtr s - 144 ∧ t.regValue .r15 = s.regValue .rsi ∧
      memLoad t.external (stackPtr s - 376) 64 = 65 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, point, copy, dst, src, digit,
    bx, bp, r12, r13, r14, r15, counter, output⟩ := initialize_lookup pre
  obtain ⟨t, step, ready, effect⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state 0x32df 0x11bc (by decide) (by decide +kernel) (by decide +kernel)
    (by exact inProgram_of_textOffset 0x44a0 (by decide)) rip
  change (callEffect (fun _ => 0x1044a0) 0x1032e4 u).Holds u t at effect
  have frame : FrameState s t 96 1400 384 :=
    state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have source : t.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have destination : t.regValue .rdi = stackPtr s - 240 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have ret : (returnBoundary t).rip = 0x1032e4 := (callEffect_stack effect).1
  have child : CalleePre t boundary 0x1044a0 768 96 496 :=
    CalleePre.of_input_and_stack pre.toCalleePre
      (⟨384, 240, by decide, by decide, by decide, by decide⟩ : StackBufferLayout 1400 96 496)
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated
      effect.rip frame.rsp source destination
      (by rw [ret]; exact inProgram_of_textOffset 0x32e4 (by decide))
  refine ⟨n+1, t, run.trans step, frame, child, ret, ?_, ?_, destination, source,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact point.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect
      (offset := 336) (by decide) (by decide) hi)
  · exact copy.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect
      (offset := 144) (by decide) (by decide) hi)
  · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans digit
  · exact (effect.agrees.read (n := 64) (r := 3) (by simp)).trans bx
  · exact (effect.agrees.read (n := 64) (r := 5) (by simp)).trans bp
  · exact (effect.agrees.read (n := 64) (r := 12) (by simp)).trans r12
  · exact (effect.agrees.read (n := 64) (r := 13) (by simp)).trans r13
  · exact (effect.agrees.read (n := 64) (r := 14) (by simp)).trans r14
  · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans r15
  · exact (scalar_call_read (by decide) state effect (offset := 376) (n := 64)
      (by decide) (by decide)).trans counter
  · exact (scalar_call_read (by decide) state effect (offset := 360) (n := 64)
      (by decide) (by decide)).trans output

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
