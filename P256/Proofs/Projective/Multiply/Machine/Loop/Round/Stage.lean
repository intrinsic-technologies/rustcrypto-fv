import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Result
import P256.Proofs.Projective.Copy
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure RoundState [Bindings] (s t : RamState) (n : Nat) (pc : BitVec 64)
    (address : Nat) (point : Projective) : Prop extends FrameState s t 96 1400 376 where
  bound : n < 64
  rip : t.RIP = pc
  value : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 address) point
  rbx : t.regValue .rbx = 0
  rbp : t.regValue .rbp = stackPtr s - 144
  r12 : t.regValue .r12 = stackPtr s - 240
  r13 : t.regValue .r13 = stackPtr s - 336
  r14 : t.regValue .r14 = 65
  r15 : t.regValue .r15 = s.regValue .rsi
  count : (Operand.mem (stackPtr s - 376) : Operand 64).read t = 65
  output : (Operand.mem (stackPtr s - 360) : Operand 64).read t = s.regValue .rdi
  table : (Operand.mem (stackPtr s - 352) : Operand 64).read t = s.regValue .rsi
  cursor : (Operand.mem (stackPtr s - 368) : Operand 64).read t =
    s.regValue .rcx + BitVec.ofNat 64 (63-n)
  remaining : (Operand.mem (stackPtr s - 344) : Operand 64).read t = BitVec.ofNat 64 (63-n)

theorem RoundState.after_registers [Bindings] {s t u : RamState} {cs : List Component}
    {n address : Nat} {pc pc' : BitVec 64} {point : Projective}
    (state : RoundState s t n pc address point) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u) (rip : u.RIP = pc')
    (noMem : ∀ c ∈ cs, ∀ a, ¬c.Covers a) (sp : .reg 4 ∉ cs)
    (kept : ∀ r ∈ [3,5,12,13,14,15], Component.reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    RoundState s u n pc' address point := by
  have memory := agrees.external noMem
  refine ⟨state.toFrameState.after_registers ready agrees noMem sp,
    state.bound, rip, state.value.of_bytes_eq (by intro i hi; rw [memory]),
    (agrees.read (n := 64) (r := 3) (kept _ (by simp))).trans state.rbx,
    (agrees.read (n := 64) (r := 5) (kept _ (by simp))).trans state.rbp,
    (agrees.read (n := 64) (r := 12) (kept _ (by simp))).trans state.r12,
    (agrees.read (n := 64) (r := 13) (kept _ (by simp))).trans state.r13,
    (agrees.read (n := 64) (r := 14) (kept _ (by simp))).trans state.r14,
    (agrees.read (n := 64) (r := 15) (kept _ (by simp))).trans state.r15,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals change memLoad u.external _ 64 = _
  all_goals rw [memory]
  · exact state.count
  · exact state.output
  · exact state.table
  · exact state.cursor
  · exact state.remaining

theorem RoundState.after_point_call [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {n address address' dst : Nat} {pc ret : BitVec 64} {point resultPoint point' : Projective}
    (state : RoundState s t n pc address point)
    (result : PointCallResult s t u boundary ret dst resultPoint) (bound : dst ≤ 336)
    (value : ProjectiveAt u (stackPtr s - BitVec.ofNat 64 address') point') :
    RoundState s u n ret address' point' := by
  refine ⟨result.toFrameState, state.bound, result.rip, value,
    (result.registers .rbx (by simp)).trans state.rbx,
    (result.registers .rbp (by simp)).trans state.rbp,
    (result.registers .r12 (by simp)).trans state.r12,
    (result.registers .r13 (by simp)).trans state.r13,
    (result.registers .r14 (by simp)).trans state.r14,
    (result.registers .r15 (by simp)).trans state.r15,
    (result.read (offset := 376) (n := 64) (by decide) (by decide) (by omega)).trans state.count,
    (result.read (offset := 360) (n := 64) (by decide) (by decide) (by omega)).trans state.output,
    (result.read (offset := 352) (n := 64) (by decide) (by decide) (by omega)).trans state.table,
    (result.read (offset := 368) (n := 64) (by decide) (by decide) (by omega)).trans state.cursor,
    (result.read (offset := 344) (n := 64) (by decide) (by decide) (by omega)).trans state.remaining⟩

theorem RoundState.after_copy [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {n address address' dst : Nat} {pc pc' : BitVec 64} {point point' : Projective}
    (pre : Pre s boundary) (state : RoundState s t n pc address point)
    (frame : FrameState s u 96 1400 376) (rip : u.RIP = pc')
    (value : ProjectiveAt u (stackPtr s - BitVec.ofNat 64 address') point')
    (agrees : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr s - BitVec.ofNat 64 dst) 96, .rip] t u)
    (bound : dst ≤ 336) (small : 96 ≤ dst+8) : RoundState s u n pc' address' point' := by
  have writes : ∀ c ∈ [Component.reg 6, .reg 7, .reg 1,
      .mem (stackPtr s - BitVec.ofNat 64 dst) 96, .rip], ∀ a, c.Covers a →
      (Component.mem (stackPtr s - BitVec.ofNat 64 dst) 96).Covers a := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ha
  have read (offset : Nat) (ho : offset ≤ 376) (lower : 344 ≤ offset) :
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand 64).read u =
        (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand 64).read t :=
    stack_read_of_agrees pre agrees writes (by omega) small (by omega) (by omega) (by omega)
  exact ⟨frame, state.bound, rip, value,
    (agrees.read (n := 64) (r := 3) (by simp)).trans state.rbx,
    (agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp,
    (agrees.read (n := 64) (r := 12) (by simp)).trans state.r12,
    (agrees.read (n := 64) (r := 13) (by simp)).trans state.r13,
    (agrees.read (n := 64) (r := 14) (by simp)).trans state.r14,
    (agrees.read (n := 64) (r := 15) (by simp)).trans state.r15,
    (read 376 (by decide) (by decide)).trans state.count,
    (read 360 (by decide) (by decide)).trans state.output,
    (read 352 (by decide) (by decide)).trans state.table,
    (read 368 (by decide) (by decide)).trans state.cursor,
    (read 344 (by decide) (by decide)).trans state.remaining⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
