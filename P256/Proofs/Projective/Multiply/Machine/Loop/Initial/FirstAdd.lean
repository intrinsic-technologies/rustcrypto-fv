import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.LookupResult
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.AddArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Add

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_first_add [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) table) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x1032ef ∧ ProjectiveAt t (stackPtr s - (336 : BitVec 64)) Projective.identity ∧
      ProjectiveAt t (stackPtr s - (144 : BitVec 64)) (Projective.identity.add
        (ProjectiveLookup.signedLookup table (memLoad s.external (s.regValue .rcx + 64) 8))) ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .rbp = s.regValue .rcx ∧
      t.regValue .r12 = stackPtr s - (240 : BitVec 64) ∧ t.regValue .r13 = 0 ∧
      t.regValue .r14 = stackPtr s - (144 : BitVec 64) ∧ t.regValue .r15 = s.regValue .rsi ∧
      memLoad t.external (stackPtr s - (376 : BitVec 64)) 64 = 65 ∧
      memLoad t.external (stackPtr s - (360 : BitVec 64)) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, point, copy, selected,
    bx, bp, r12, r13, r14, r15, counter, output⟩ := initialize_lookup_result pre input
  obtain ⟨m, v, prepare, ready, _, effect⟩ := addArguments_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x32e4 addArgumentsBytes
      (by decide) (by decide +kernel)) rip
  have agrees : AgreesExcept [.reg 7, .reg 6, .rip] u v := effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := state.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have values := effect.writes
  change v.regValue .rdi = u.regValue .r14 ∧ v.regValue .rsi = u.regValue .r12 at values
  obtain ⟨t, addition⟩ := add_call pre frame initialAdd effect.rip
    (values.1.trans r14) (values.2.trans r12)
    (copy.of_bytes_eq (by intro i hi; rw [memory]))
    (selected.of_bytes_eq (by intro i hi; rw [memory]))
  obtain ⟨k, step⟩ := addition.execution
  have regs (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = u.regValue r := by
    apply (addition.registers r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact agrees.read (n := 64) (r := 3) (by simp)
    · exact agrees.read (n := 64) (r := 5) (by simp)
    · exact agrees.read (n := 64) (r := 12) (by simp)
    · exact agrees.read (n := 64) (r := 13) (by simp)
    · exact agrees.read (n := 64) (r := 14) (by simp)
    · exact agrees.read (n := 64) (r := 15) (by simp)
  refine ⟨n+m+k, t, (run.trans prepare).trans step, addition.toFrameState,
    addition.rip, ?_, addition.value, (regs .rbx (by simp)).trans bx,
    (regs .rbp (by simp)).trans bp, (regs .r12 (by simp)).trans r12,
    (regs .r13 (by simp)).trans r13, (regs .r14 (by simp)).trans r14,
    (regs .r15 (by simp)).trans r15, ?_, ?_⟩
  · apply point.of_bytes_eq
    intro i hi
    have h := addition.bytes 336 96 (by decide) (by decide) (Or.inr (by decide)) i hi
    rw [memory] at h
    exact h
  · have h := addition.read (offset := 376) (n := 64)
      (by decide) (by decide) (Or.inr (by decide))
    change memLoad t.external _ 64 = memLoad v.external _ 64 at h
    rw [memory] at h
    exact h.trans counter
  · have h := addition.read (offset := 360) (n := 64)
      (by decide) (by decide) (Or.inr (by decide))
    change memLoad t.external _ 64 = memLoad v.external _ 64 at h
    rw [memory] at h
    exact h.trans output

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
