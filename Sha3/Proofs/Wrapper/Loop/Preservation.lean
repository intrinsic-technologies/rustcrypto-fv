import Sha3.Proofs.Wrapper.Loop.Context
import Sha3.Proofs.Wrapper.Setup.Prologue
import Sha3.Proofs.Update.Frame

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

theorem prefixClobbers_no_memory (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) :
    ∀ c ∈ prefixClobbers kind v fullState, ∀ address, ¬ c.Covers address := by
  intro c hc address
  simp only [prefixClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact id

theorem suffixClobbers_no_memory (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) :
    ∀ c ∈ suffixClobbers kind v fullState, ∀ address, ¬ c.Covers address := by
  intro c hc address
  simp only [suffixClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact id

theorem bound_read_of_memory_eq {kind : Kind} {v : Variant} {fullState : Bool}
    {s t : RamState}
    (hsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s)
    (he : t.external = s.external)
    (hreg : kind.memoryBound v fullState = false →
      (Operand.reg (kind.boundReg v fullState) : Operand 64).read t =
        (Operand.reg (kind.boundReg v fullState) : Operand 64).read s) :
    (kind.boundOperand t v fullState).read t = (kind.boundOperand s v fullState).read s := by
  cases hb : kind.memoryBound v fullState with
  | false => simpa only [Kind.boundOperand, hb, Bool.false_eq_true, ite_false] using hreg hb
  | true =>
    simp only [Kind.boundOperand, hb, ite_true]
    rw [hsp]
    change memLoad t.external _ 64 = memLoad s.external _ 64
    rw [he]

theorem State.after_prefix [bindings : Bindings] {initial s t : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {start stop i split : Nat}
    (h : State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (hready : ReadyToStep t) (ha : AgreesExcept (prefixClobbers kind v fullState) s t) :
    State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i t := by
  have he := ha.external (prefixClobbers_no_memory kind v fullState)
  refine ⟨h.invariant.of_agreesExcept hCall hready ha ?_ (by simp [prefixClobbers]),
    h.saved.of_external_eq he, ?_, ?_, h.state.of_bytes_eq (by intro j hj; rw [he])⟩
  · intro c hc address hcover
    exact (prefixClobbers_no_memory kind v fullState c hc address hcover).elim
  · constructor
    · exact (ha.read (n := 64) (r := 4) (by cases kind <;> cases v <;> cases fullState <;> simp [prefixClobbers, Kind.nextReg, Kind.largeFollower])).trans
        h.registers.stack
    · exact (ha.read (n := 64) (r := 12) (by cases kind <;> cases v <;> cases fullState <;> simp [prefixClobbers, Kind.nextReg, Kind.largeFollower])).trans
        h.registers.pointers
    · exact (ha.read (n := 64) (r := 14) (by cases kind <;> cases v <;> cases fullState <;> simp [prefixClobbers, Kind.nextReg, Kind.largeFollower])).trans
        h.registers.lengths
    · apply Eq.trans ?_ h.registers.bound
      apply bound_read_of_memory_eq (ha.read (n := 64) (r := 4) (by
        cases kind <;> cases v <;> cases fullState <;>
          simp [prefixClobbers, Kind.nextReg, Kind.largeFollower])) he
      intro hm
      exact ha.read (by
        cases kind <;> cases v <;> cases fullState <;>
          simp_all [prefixClobbers, Kind.nextReg, Kind.boundReg, Kind.memoryBound, Kind.largeFollower])
    · exact (ha.read (n := 64) (r := (kind.stateReg v fullState)) (by
        cases kind <;> cases v <;> cases fullState <;> simp [prefixClobbers, Kind.nextReg, Kind.stateReg, Kind.largeFollower])).trans
        h.registers.pointer
    · intro r hr
      apply Eq.trans ?_ (h.registers.cursor r hr)
      exact ha.read (by
        cases kind <;> cases v <;> cases fullState <;>
          simp_all [prefixClobbers, Kind.nextReg, Kind.cursorReg, Kind.largeFollower] <;> subst r <;> decide)
  · exact (ha.read (n := 64) (r := (kind.indexReg v fullState)) (by
      cases kind <;> cases v <;> cases fullState <;> simp [prefixClobbers, Kind.nextReg, Kind.indexReg, Kind.largeFollower])).trans h.index

theorem clobbers_trans {initial s t u : RamState} {v : Variant} {kind : Kind}
    (h : AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t)
    (h' : AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) t u) :
    AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s u :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem prefixClobbers_subset (initial : RamState) (v : Variant) (kind : Kind) :
    ∀ c ∈ prefixClobbers kind v fullState, c ∈ clobbers (keccak := keccak) (fullState := fullState) initial v kind := by
  intro c hc
  simp only [prefixClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clobbers]

theorem suffixClobbers_subset (initial : RamState) (v : Variant) (kind : Kind) :
    ∀ c ∈ suffixClobbers kind v fullState, c ∈ clobbers (keccak := keccak) (fullState := fullState) initial v kind := by
  intro c hc
  simp only [suffixClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [clobbers]

end Sha3.Proofs.Wrapper.Loop
