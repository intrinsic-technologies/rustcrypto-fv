import P256.Proofs.Signing.Core.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Nonce.Fill.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.NextNonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem scalarFrame [Bindings] {s t : RamState} (frame : Frame s t) :
    ScalarFrame.FrameState s t 65 4584 2280 :=
  ⟨frame.bindingsSupported, frame.machine, frame.loaded, frame.directionFlag,
    frame.allocated, frame.frame, frame.rsp, frame.saved, frame.returnAddress,
    frame.mxcsr, frame.fp87⟩

theorem coreFrame [Bindings] {s t : RamState} (frame : ScalarFrame.FrameState s t 65 4584 2280) :
    Frame s t :=
  ⟨frame.machine, frame.bindingsSupported, frame.loaded, frame.directionFlag,
    frame.allocated, frame.frame, frame.rsp, frame.saved, frame.returnAddress,
    frame.mxcsr, frame.fp87⟩

theorem base_add (s : RamState) {offset : Nat} (bound : offset ≤ 2280) :
    frameBase s + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (2280-offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 2280 offset (by omega) bound]
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem base_nat [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) {offset : Nat} (bound : offset ≤ 2288) :
    (frameBase s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - 2280 + offset := by
  have bounds := stack_bounds pre.stack
  have base : (frameBase s).toNat = (stackPtr s).toNat - 2280 :=
    stack_sub_toNat pre.stack (by decide)
  rw [BitVec.toNat_add, base, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]

theorem arguments_copy {s t u : RamState} (input : StoredArguments s t)
    (copy : ∀ offset, 72 ≤ offset ∧ offset < 104 →
      u.external[frameBase s + BitVec.ofNat 64 offset]? =
        t.external[frameBase s + BitVec.ofNat 64 offset]?) : StoredArguments s u := by
  have word (offset : Nat) (range : 72 ≤ offset ∧ offset + 8 ≤ 104) :
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read u =
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read t := by
    apply memLoad_congr
    intro i hi'
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, copy _ (by omega)]
  exact ⟨(word 72 (by decide)).trans input.output,
    (word 80 (by decide)).trans input.secret,
    (word 88 (by decide)).trans input.digest,
    (word 96 (by decide)).trans input.length⟩

theorem loop_after_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {cs : List Component}
    (pre : SignPre s boundary) (input : Loop s t state)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a → ∃ offset, 40 ≤ offset ∧ offset < 72 ∧
      a = frameBase s + BitVec.ofNat 64 offset)
    (regs : ∀ r ∈ [4,5,3,13,14,15], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) (mxcsr : Component.mxcsr ∉ cs) (fp87 : Component.fcw ∉ cs) :
    Loop s u state := by
  have memory : WritesWithin cs #v[registerRegion s .rdi 65, ScalarFrame.workRegion s 4584] := by
    intro c hc a ha
    obtain ⟨offset, lo, hi, rfl⟩ := writes c hc a ha
    refine ⟨ScalarFrame.workRegion s 4584, by simp, ?_⟩
    rw [base_add s (by omega)]
    exact ScalarFrame.work_contains pre.toCalleePre (offset := 2280-offset) (len := 1)
      (by omega) (by omega) ⟨0, by decide, by simp⟩
  have frame := (scalarFrame input.frame).after_effect pre.toCalleePre (by decide)
    ready agrees memory (regs 4 (by simp)) df mxcsr fp87
  have copy (offset : Nat) (apart : offset < 40 ∨ 72 ≤ offset) (hi : offset < 2^64) :
      u.external[frameBase s + BitVec.ofNat 64 offset]? =
        t.external[frameBase s + BitVec.ofNat 64 offset]? := by
    apply agrees.byte
    intro c hc cover
    obtain ⟨j, lower, upper, eq⟩ := writes c hc _ cover
    have eqNat := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase s)).mp eq)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt (by omega : j < 2^64)] at eqNat
    omega
  have bytes (offset len : Nat) (lo : 72 ≤ offset) (hi : offset + len < 2^64) :
      ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hin
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact copy (offset + i) (by omega) (by omega)
  exact ⟨coreFrame frame, arguments_copy input.arguments (fun offset range => copy offset (by omega) (by omega)),
    input.generator.copy (bytes 2160 72 (by decide) (by decide))
      ⟨input.generator.2.1.1, fun i hi =>
        (bytes 272 32 (by decide) (by decide) i hi).trans (input.generator.2.1.2 i hi)⟩,
    (agrees.read (n := 64) (r := 5) (regs 5 (by simp))).trans input.rbp,
    (agrees.read (n := 64) (r := 3) (regs 3 (by simp))).trans input.rbx,
    (agrees.read (n := 64) (r := 13) (regs 13 (by simp))).trans input.r13,
    (agrees.read (n := 64) (r := 14) (regs 14 (by simp))).trans input.r14,
    (agrees.read (n := 64) (r := 15) (regs 15 (by simp))).trans input.r15⟩

end P256.Proofs.Signing.Core.NextNonce
