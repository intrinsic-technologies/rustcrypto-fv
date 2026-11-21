import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.LookupCall
import P256.Proofs.Projective.Multiply.Machine.Loop.Memory
import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Projective.Multiply.Machine.Lookup

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

theorem initialize_lookup_result [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) table) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x1032e4 ∧ ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      ProjectiveAt t (stackPtr s - 144) Projective.identity ∧
      ProjectiveAt t (stackPtr s - 240)
        (ProjectiveLookup.signedLookup table (memLoad s.external (s.regValue .rcx + 64) 8)) ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .rbp = s.regValue .rcx ∧
      t.regValue .r12 = stackPtr s - 240 ∧ t.regValue .r13 = 0 ∧
      t.regValue .r14 = stackPtr s - 144 ∧ t.regValue .r15 = s.regValue .rsi ∧
      memLoad t.external (stackPtr s - 376) 64 = 65 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, child, ret, point, copy, dst, src, digit,
    bx, bp, r12, r13, r14, r15, counter, output⟩ := initialize_lookup_call pre
  have tableU : Lookup.TableAt u (u.regValue .rsi) table := by
    rw [src]
    exact table_at pre.toCalleePre state input
  have digitU : (u.regValue .rdx).setWidth 8 =
      memLoad s.external (s.regValue .rcx + 64) 8 := by
    rw [digit]
    simp
  obtain ⟨t, result, value⟩ := Lookup.lookup_correct bindings u boundary table _ child tableU digitU
  have memory := stack_result_work_frame (frameOffset := 376) pre.toCalleePre state result
    dst (by decide) (by decide) (by decide) (by decide)
  have frame := after_result (frameOffset := 376) pre.toCalleePre state result (by decide) memory
  obtain ⟨m, step⟩ := result.execution
  have bytes (offset len : Nat) (bound : offset ≤ 376) (size : len ≤ offset + 8)
      (apart : offset + 96 ≤ 240 ∨ 240 + len ≤ offset) (i : Nat) (hi : i < len) :=
    stack_result_byte (frameOffset := 376) pre.toCalleePre state result dst
      (by decide) (by decide) bound size apart hi
  have word (offset : Nat) (bound : offset ≤ 376) (apart : 248 ≤ offset) :
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
      (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
    rw [bytes offset 8 bound (by omega) (Or.inr apart) i hi]
  refine ⟨n+m, t, run.trans step, frame, result.rip.trans ret, ?_, ?_, dst ▸ value,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact point.of_bytes_eq (bytes 336 96 (by decide) (by decide) (Or.inr (by decide)))
  · exact copy.of_bytes_eq (bytes 144 96 (by decide) (by decide) (Or.inl (by decide)))
  · exact (result.calleeSaved .rbx (by simp)).trans bx
  · exact (result.calleeSaved .rbp (by simp)).trans bp
  · exact (result.calleeSaved .r12 (by simp)).trans r12
  · exact (result.calleeSaved .r13 (by simp)).trans r13
  · exact (result.calleeSaved .r14 (by simp)).trans r14
  · exact (result.calleeSaved .r15 (by simp)).trans r15
  · exact (word 376 (by decide) (by decide)).trans counter
  · exact (word 360 (by decide) (by decide)).trans output

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
