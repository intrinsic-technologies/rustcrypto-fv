import Sha3.Proofs.Wrapper.Loop.Instructions
import Sha3.Proofs.Wrapper.Loop.Iteration

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

theorem finish_iteration [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {start stop i split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hInv : Invariant (keccak := keccak) (fullState := fullState) initial v kind.mode s) (hSaved : SavedFrame initial s)
    (hRegs : Registers (keccak := keccak) (fullState := fullState) initial v kind stop s)
    (hState : Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) (absorbed v inputs start (i + 1)) s)
    (hNext : (Operand.reg (kind.nextReg v fullState) : Operand 64).read s = BitVec.ofNat 64 (i + 1))
    (hip : s.RIP = kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.returnOffset v fullState)) (hi : i < stop) (hstop : stop ≤ inputs.size) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧
      State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop (i + 1) t ∧
      t.RIP = position kind v (keccak := keccak) (fullState := fullState) (i + 1) stop ∧ AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t := by
  have hread : ∀ address, kind.boundOperand s v fullState = .mem address →
      MemReadable s address 8 := by
    intro address haddress
    unfold Kind.boundOperand at haddress
    split at haddress
    · injection haddress with haddress
      subst address
      change MemReadable s (s.regValue .rsp + _) 8
      rw [hRegs.stack]
      cases fullState with
      | false =>
          exact hInv.frameReadable (offset := 0) (count := 8) hCall.stackAvailable
            (by cases kind <;> cases v <;> cases keccak <;> decide)
      | true =>
          exact hInv.frameReadable (offset := 8) (count := 8) hCall.stackAvailable
            (by cases kind <;> cases v <;> cases keccak <;> decide)
    · cases haddress
  obtain ⟨t, hrun, hready, _, hrip, hindex, ha⟩ :=
    suffix_advance kind v (keccak := keccak) (fullState := fullState) (hfull := fun hf ↦ (hCall.fullState_valid hf).1) (hread := hread) s hInv.ready hInv.loaded outside hip
  have he := ha.external (suffixClobbers_no_memory kind v fullState)
  have hsize : inputs.size < 2 ^ 64 := by
    rw [← (hCall.inputSlices kind.mode_ne_digest).countArgumentMatchesInputs]
    exact (initial.regValue .rsi).isLt
  have hnext64 : i + 1 < 2 ^ 64 := by omega
  have hstop64 : stop < 2 ^ 64 := by omega
  have hEq : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 stop ↔ i + 1 = stop := by
    constructor
    · intro hh
      have hn := congrArg BitVec.toNat hh
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnext64,
        Nat.mod_eq_of_lt hstop64] using hn
    · exact congrArg (BitVec.ofNat 64)
  refine ⟨t, hrun, ?_, ?_, ha.mono (suffixClobbers_subset initial v kind)⟩
  · refine ⟨hInv.of_agreesExcept hCall hready ha ?_ (by cases kind <;> simp [suffixClobbers]), hSaved.of_external_eq he,
      ?_, hindex.trans hNext, hState.of_bytes_eq (by intro j hj; rw [he])⟩
    · intro c hc address hcover
      exact (suffixClobbers_no_memory kind v fullState c hc address hcover).elim
    · constructor
      · exact (ha.read (n := 64) (r := 4) (by
          cases kind <;> cases v <;> cases fullState <;> simp [suffixClobbers, Kind.indexReg, Kind.largeFollower])).trans hRegs.stack
      · exact (ha.read (n := 64) (r := 12) (by
          cases kind <;> cases v <;> cases fullState <;> simp [suffixClobbers, Kind.indexReg, Kind.largeFollower])).trans hRegs.pointers
      · exact (ha.read (n := 64) (r := 14) (by
          cases kind <;> cases v <;> cases fullState <;> simp [suffixClobbers, Kind.indexReg, Kind.largeFollower])).trans hRegs.lengths
      · apply Eq.trans ?_ hRegs.bound
        apply bound_read_of_memory_eq (ha.read (n := 64) (r := 4) (by
          cases kind <;> cases v <;> cases fullState <;>
            simp [suffixClobbers, Kind.indexReg, Kind.largeFollower])) he
        intro hm
        exact ha.read (by
          cases kind <;> cases v <;> cases fullState <;>
            simp_all [suffixClobbers, Kind.indexReg, Kind.boundReg, Kind.memoryBound, Kind.largeFollower])
      · exact (ha.read (n := 64) (r := (kind.stateReg v fullState)) (by
          cases kind <;> cases v <;> cases fullState <;> simp [suffixClobbers, Kind.indexReg, Kind.stateReg, Kind.largeFollower])).trans hRegs.pointer
      · intro r hr
        apply Eq.trans ?_ (hRegs.cursor r hr)
        exact ha.read (by
          cases kind <;> cases v <;> cases fullState <;>
            simp_all [suffixClobbers, Kind.indexReg, Kind.cursorReg, Kind.largeFollower] <;> subst r <;> decide)
  · rw [hNext, hRegs.bound] at hrip
    by_cases hs : i + 1 = stop
    · simpa only [position, hEq, hs, Nat.lt_irrefl, ↓reduceIte] using hrip
    · have hlt : i + 1 < stop := by omega
      simpa only [position, hEq, hs, hlt, ↓reduceIte] using hrip

end Sha3.Proofs.Wrapper.Loop
