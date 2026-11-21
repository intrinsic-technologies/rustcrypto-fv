import P256.Proofs.Signing.Core.NextNonce.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat arguments_copy)

theorem local_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) {offset len : Nat}
    (bound : offset + len ≤ 2280) :
    MemReadable t (frameBase s + BitVec.ofNat 64 offset) len := by
  rw [← frame.rsp]
  exact ScalarFrame.stack_readable pre.toCalleePre (scalarFrame frame) (by decide) bound

theorem local_writable8 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) {offset : Nat}
    (bound : offset + 8 ≤ 2280) (aligned : offset % 8 = 0) :
    MemWritable t (frameBase s + BitVec.ofNat 64 offset) 8 := by
  rw [base_add s (by omega)]
  apply writable_of_grow _ frame.allocated
  apply stack_sub_writable8 pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega)
  omega

theorem local_code_apart [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) {offset len codeOffset codeLen : Nat}
    (bound : offset + len ≤ 2280) (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (frameBase s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  rw [← frame.rsp]
  exact ScalarFrame.stack_code pre.toCalleePre (scalarFrame frame) (by decide) bound codeBound

def WordWrites (base : BitVec 64) (offsets : List Nat) (cs : List Component) : Prop :=
  ∀ c ∈ cs, ∀ a, c.Covers a → ∃ offset ∈ offsets, ∃ i < 8,
    a = base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i

theorem word_writes_within [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {offsets : List Nat} (pre : SignPre s boundary)
    (writes : WordWrites (frameBase s) offsets cs)
    (bound : ∀ offset ∈ offsets, offset + 8 ≤ 2232) :
    WritesWithin cs #v[registerRegion s .rdi 65, ScalarFrame.workRegion s 4584] := by
  intro c hc a ha
  obtain ⟨offset, member, i, hi, rfl⟩ := writes c hc a ha
  refine ⟨ScalarFrame.workRegion s 4584, by simp, ?_⟩
  rw [base_add s (by have := bound offset member; omega)]
  exact ScalarFrame.work_contains pre.toCalleePre (by omega)
    (by have := bound offset member; omega) ⟨i, hi, rfl⟩

theorem word_writes_byte {s t u : RamState} {offsets : List Nat} {cs : List Component}
    (writes : WordWrites (frameBase s) offsets cs) (agrees : AgreesExcept cs t u)
    {offset : Nat} (bound : offset < 2^64)
    (apart : ∀ off ∈ offsets, off + 8 ≤ 2^64 ∧ (offset < off ∨ off + 8 ≤ offset)) :
    u.external[frameBase s + BitVec.ofNat 64 offset]? =
      t.external[frameBase s + BitVec.ofNat 64 offset]? := by
  apply agrees.byte
  intro c hc cover
  obtain ⟨off, ho, i, hi, eq⟩ := writes c hc _ cover
  have facts := apart off ho
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at eq
  have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase s)).mp eq)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    Nat.mod_eq_of_lt (by omega : off + i < 2^64)] at hn
  omega

theorem after_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 65, ScalarFrame.workRegion s 4584])
    (rsp : stackPtr u = stackPtr t) (df : Component.df ∉ cs)
    (mxcsr : Component.mxcsr ∉ cs) (fp87 : Component.fcw ∉ cs) : Frame s u := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans frame.frame (ScalarFrame.output_work_frame pre.toCalleePre memory)
  refine ⟨supportedMachine_of_ready_agrees frame.machine ready agrees,
    bindingsSupported_of_ready_agrees frame.bindingsSupported ready agrees,
    ScalarFrame.loaded_of_frame pre.toCalleePre total, agrees.directionFlagClear df frame.directionFlag,
    fun a ha => agrees.grow a (frame.allocated a ha), total, rsp.trans frame.rsp, ?_, ?_,
    (agrees.mxcsr mxcsr).trans frame.mxcsr, (agrees.fcw fp87).trans frame.fp87⟩
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.output_work_read pre.toCalleePre (by decide) memory bound (by omega)).trans
      (frame.saved entry he)
  · have h := ScalarFrame.output_work_read pre.toCalleePre (by decide) memory
      (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress

theorem after_registers [Bindings] {s t u : RamState} {cs : List Component}
    (frame : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (noMem : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (rsp : Component.reg 4 ∉ cs) (df : Component.df ∉ cs)
    (mxcsr : Component.mxcsr ∉ cs) (fp87 : Component.fcw ∉ cs) : Frame s u :=
  coreFrame ((scalarFrame frame).after_registers ready agrees noMem rsp df mxcsr fp87)

theorem after_effect [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {offsets : List Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u) (writes : WordWrites (frameBase s) offsets cs)
    (bound : ∀ offset ∈ offsets, offset + 8 ≤ 2232)
    (rsp : Component.reg 4 ∉ cs) (df : Component.df ∉ cs)
    (mxcsr : Component.mxcsr ∉ cs) (fp87 : Component.fcw ∉ cs) : Frame s u :=
  coreFrame ((scalarFrame frame).after_effect pre.toCalleePre (by decide) ready agrees
    (word_writes_within pre writes bound) rsp df mxcsr fp87)

end P256.Proofs.Signing.Core.Iteration
