import Sha3.Proofs.Wrapper.Loop.Layout
import Sha3.Proofs.Wrapper.Invariant
import Sha3.Proofs.Update.Layout
import Sha3.Proofs.Incremental.Canonical
import Sha3.Proofs.Incremental.Inputs

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def stackBase (initial : RamState) (v : Variant) (kind : Kind) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 336

def writeRegions (initial : RamState) (v : Variant) (kind : Kind) (keccak : Bool := false) (fullState : Bool := false) : Vector MemoryRegion 2 :=
  #v[⟨(stackBase (keccak := keccak) (fullState := fullState) initial v kind).toNat, 336⟩,
    ⟨(statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode).toNat, 201⟩]

def extraClobbers : List Component :=
  List.ofFn (fun i : Fin 16 ↦ .reg (BitVec.ofNat 5 (16 + i.val))) ++
    List.ofFn (fun i : Fin 32 ↦ .xmm (BitVec.ofNat 5 i.val))

theorem extraClobbers_no_memory :
    ∀ c ∈ extraClobbers, ∀ address, ¬ c.Covers address := by
  intro c hc address
  simp only [extraClobbers, List.mem_append, List.mem_ofFn] at hc
  rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> exact id

def clobbers (initial : RamState) (v : Variant) (kind : Kind) (keccak : Bool := false) (fullState : Bool := false) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .reg (kind.indexReg v fullState), .reg (kind.nextReg v fullState), .flags, .rip,
    .mem (stackBase (keccak := keccak) (fullState := fullState) initial v kind) 336, .mem (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) 201] ++ extraClobbers

structure Registers (initial : RamState) (v : Variant) (kind : Kind) (stop : Nat) (s : RamState) (keccak : Bool := false) (fullState : Bool := false) : Prop where
  stack : s.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r14 = initial.regValue .rdx
  bound : (kind.boundOperand s v fullState).read s = BitVec.ofNat 64 stop
  pointer : (Operand.reg (kind.stateReg v fullState) : Operand 64).read s = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode

  cursor : ∀ r, kind.cursorReg v fullState = some r → (Operand.reg r : Operand 64).read s = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode + 200

structure UpdateEntryRegisters (initial : RamState) (v : Variant) (kind : Kind)
    (slice : Input) (s : RamState) (keccak : Bool := false) (fullState : Bool := false) (wrapperMode : Mode := kind.mode) : Prop where
  stack : s.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v wrapperMode - 8
  pointer : s.regValue .rsi = statePointer (keccak := keccak) (fullState := fullState) initial v wrapperMode
  input : s.regValue .rdx = slice.address
  length : s.regValue .rcx = BitVec.ofNat 64 slice.bytes.size

  cursor : s.regValue .rdi = statePointer (keccak := keccak) (fullState := fullState) initial v wrapperMode + 200

def absorbed (v : Variant) (inputs : Array Input) (start i : Nat) : Incremental.State :=
  Incremental.canonicalState Keccak.keccakLanes v.rate (message (inputs.extract start i))

structure State [Bindings] (initial : RamState) (v : Variant) (kind : Kind)
    (inputs : Array Input) (start stop i : Nat) (s : RamState) (keccak : Bool := false) (fullState : Bool := false) : Prop where
  invariant : Invariant (keccak := keccak) (fullState := fullState) initial v kind.mode s
  saved : SavedFrame initial s
  registers : Registers (keccak := keccak) (fullState := fullState) initial v kind stop s
  index : (Operand.reg (kind.indexReg v fullState) : Operand 64).read s = BitVec.ofNat 64 i
  state : Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) (absorbed v inputs start i) s

def UpdateCorrect [Bindings] (v : Variant) (boundary : ReturnBoundary) : Prop :=
  ∀ called bytes state, Update.CallContext v called bytes state →
    ∃ fuel final, Advances boundary fuel called final ∧ ReadyToStep final ∧
      ProgramLoaded final ∧
      Update.CallResult called final (Incremental.update Keccak.keccakLanes v.rate state bytes)

theorem absorbed_cursor_lt (v : Variant) (inputs : Array Input) (start i : Nat) :
    (absorbed v inputs start i).cursor < v.rate :=
  Nat.mod_lt _ v.rate_pos

theorem absorbed_succ (v : Variant) (inputs : Array Input) (start i : Nat)
    (hs : start ≤ i) (hi : i < inputs.size) :
    Incremental.update Keccak.keccakLanes v.rate (absorbed v inputs start i) inputs[i].bytes =
      absorbed v inputs start (i + 1) := by
  rw [absorbed, Incremental.update_canonicalState _ _ v.rate_pos,
    ← Incremental.message_extract_succ inputs start i hs hi]
  rfl

end Sha3.Proofs.Wrapper.Loop
