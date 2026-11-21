import Sha3.Proofs.Wrapper.Loop.Code
import X86Proofs.Instructions.Lea.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Triple
import X86Proofs.Instructions.Branch.Triple
import Sha3.Proofs.Run
import Sha3.Proofs.X86.Instructions.Cmp.Memory

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def nextMode (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : AddrMode := .base ((kind.indexReg v fullState).setWidth 4) (.d8 1)

def tableMode (kind : Kind) (base : BitVec 4) (v : Variant := .sha256) (fullState : Bool := false) : AddrMode :=
  .sib base (some ((kind.indexReg v fullState).setWidth 4)) 3 .none

def tableAddress (kind : Kind) (base : BitVec 5) (s : RamState) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 64 :=
  (Operand.reg base : Operand 64).read s +
    ((Operand.reg (kind.indexReg v fullState) : Operand 64).read s <<< 3)

theorem next_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (fun s ↦ s.RIP = kind.start v keccak fullState) (codeRange (kind.start v keccak fullState) (nextBytes kind v fullState))
      (leaR64Effect (kind.start v keccak fullState) (kind.nextReg v fullState) (nextMode kind v fullState)) := by
  generalize hp : kind.start v keccak fullState = p
  have shape : nextBytes kind v fullState = [0x48, 0x8d, 0x58, 1] ∧ kind.nextReg v fullState = 3 ∧ kind.indexReg v fullState = 0 ∨
      nextBytes kind v fullState = [0x4c, 0x8d, 0x68, 1] ∧ kind.nextReg v fullState = 13 ∧ kind.indexReg v fullState = 0 ∨
      nextBytes kind v fullState = [0x48, 0x8d, 0x68, 1] ∧ kind.nextReg v fullState = 5 ∧ kind.indexReg v fullState = 0 ∨
      nextBytes kind v fullState = [0x48, 0x8d, 0x6b, 1] ∧ kind.nextReg v fullState = 5 ∧ kind.indexReg v fullState = 3 ∨
      nextBytes kind v fullState = [0x49, 0x8d, 0x5d, 1] ∧ kind.nextReg v fullState = 3 ∧ kind.indexReg v fullState = 13 ∨
      nextBytes kind v fullState = [0x4c, 0x8d, 0x78, 1] ∧ kind.nextReg v fullState = 15 ∧ kind.indexReg v fullState = 0 ∨
      nextBytes kind v fullState = [0x4c, 0x8d, 0x7b, 1] ∧ kind.nextReg v fullState = 15 ∧ kind.indexReg v fullState = 3 := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with ⟨hb, hn, hi⟩ | ⟨hb, hn, hi⟩ | ⟨hb, hn, hi⟩ | ⟨hb, hn, hi⟩ | ⟨hb, hn, hi⟩ | ⟨hb, hn, hi⟩ | ⟨hb, hn, hi⟩
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 3 (.base 0 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x4c (by unfold RexWPrefix; decide) 5 (.base 0 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 5 (.base 0 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 5 (.base 3 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x49 (by unfold RexWPrefix; decide) 3 (.base 13 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x4c (by unfold RexWPrefix; decide) 7 (.base 0 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl
  · simp only [hb, hn, nextMode, hi]
    exact lea_r64_effect_step _ 0x4c (by unfold RexWPrefix; decide) 7 (.base 3 (.d8 1)) (by unfold AddrMode.Valid; decide) rfl rfl

theorem pointer_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (LoadPre (kind.start v keccak fullState + (4 : BitVec 64)) (fun s ↦ tableAddress kind 12 s v fullState) 8)
      (codeRange (kind.start v keccak fullState + (4 : BitVec 64)) (pointerBytes kind v fullState))
      (movR64M64Effect (kind.start v keccak fullState + (4 : BitVec 64)) 2 (tableMode kind 12 v fullState)) := by
  generalize hp : kind.start v keccak fullState = p
  have shape : kind.indexReg v fullState = 0 ∨
      kind.indexReg v fullState = 3 ∨
      kind.indexReg v fullState = 13 := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with hi | hi | hi
  · have h : StepEffect (LoadPre (p + 4) (fun s ↦ (AddrMode.sib 12 (some 0) 3 .none).addr s 0) 8)
        (codeRange (p + 4) [0x49, 0x8b, 20, 196])
        (movR64M64Effect (p + 4) 2 (.sib 12 (some 0) 3 .none)) :=
      mov_r64_m64_effect_step _ 0x49 (by unfold RexWPrefix; decide) 2
        (.sib 12 (some 0) 3 .none) (by unfold AddrMode.Valid; decide) rfl rfl
    simpa [pointerBytes, tableAddress, tableMode, hi, AddrMode.addr, AddrMode.reg64, Disp.value] using h
  · have h : StepEffect (LoadPre (p + 4) (fun s ↦ (AddrMode.sib 12 (some 3) 3 .none).addr s 0) 8)
        (codeRange (p + 4) [0x49, 0x8b, 20, 220])
        (movR64M64Effect (p + 4) 2 (.sib 12 (some 3) 3 .none)) :=
      mov_r64_m64_effect_step _ 0x49 (by unfold RexWPrefix; decide) 2
        (.sib 12 (some 3) 3 .none) (by unfold AddrMode.Valid; decide) rfl rfl
    simpa [pointerBytes, tableAddress, tableMode, hi, AddrMode.addr, AddrMode.reg64, Disp.value] using h
  · have h : StepEffect (LoadPre (p + 4) (fun s ↦ (AddrMode.sib 12 (some 13) 3 .none).addr s 0) 8)
        (codeRange (p + 4) [0x4b, 0x8b, 20, 236])
        (movR64M64Effect (p + 4) 2 (.sib 12 (some 13) 3 .none)) :=
      mov_r64_m64_effect_step _ 0x4b (by unfold RexWPrefix; decide) 2
        (.sib 12 (some 13) 3 .none) (by unfold AddrMode.Valid; decide) rfl rfl
    simpa [pointerBytes, tableAddress, tableMode, hi, AddrMode.addr, AddrMode.reg64, Disp.value] using h

theorem length_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (LoadPre (kind.start v keccak fullState + (8 : BitVec 64)) (fun s ↦ tableAddress kind 14 s v fullState) 8)
      (codeRange (kind.start v keccak fullState + (8 : BitVec 64)) (lengthBytes kind v fullState))
      (movR64M64Effect (kind.start v keccak fullState + (8 : BitVec 64)) 1 (tableMode kind 14 v fullState)) := by
  generalize hp : kind.start v keccak fullState = p
  have shape : kind.indexReg v fullState = 0 ∨
      kind.indexReg v fullState = 3 ∨
      kind.indexReg v fullState = 13 := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with hi | hi | hi
  · have h : StepEffect (LoadPre (p + 8) (fun s ↦ (AddrMode.sib 14 (some 0) 3 .none).addr s 0) 8)
        (codeRange (p + 8) [0x49, 0x8b, 12, 198])
        (movR64M64Effect (p + 8) 1 (.sib 14 (some 0) 3 .none)) :=
      mov_r64_m64_effect_step _ 0x49 (by unfold RexWPrefix; decide) 1
        (.sib 14 (some 0) 3 .none) (by unfold AddrMode.Valid; decide) rfl rfl
    simpa [lengthBytes, tableAddress, tableMode, hi, AddrMode.addr, AddrMode.reg64, Disp.value] using h
  · have h : StepEffect (LoadPre (p + 8) (fun s ↦ (AddrMode.sib 14 (some 3) 3 .none).addr s 0) 8)
        (codeRange (p + 8) [0x49, 0x8b, 12, 222])
        (movR64M64Effect (p + 8) 1 (.sib 14 (some 3) 3 .none)) :=
      mov_r64_m64_effect_step _ 0x49 (by unfold RexWPrefix; decide) 1
        (.sib 14 (some 3) 3 .none) (by unfold AddrMode.Valid; decide) rfl rfl
    simpa [lengthBytes, tableAddress, tableMode, hi, AddrMode.addr, AddrMode.reg64, Disp.value] using h
  · have h : StepEffect (LoadPre (p + 8) (fun s ↦ (AddrMode.sib 14 (some 13) 3 .none).addr s 0) 8)
        (codeRange (p + 8) [0x4b, 0x8b, 12, 238])
        (movR64M64Effect (p + 8) 1 (.sib 14 (some 13) 3 .none)) :=
      mov_r64_m64_effect_step _ 0x4b (by unfold RexWPrefix; decide) 1
        (.sib 14 (some 13) 3 .none) (by unfold AddrMode.Valid; decide) rfl rfl
    simpa [lengthBytes, tableAddress, tableMode, hi, AddrMode.addr, AddrMode.reg64, Disp.value] using h

def cursorValue (kind : Kind) (s : RamState) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 64 :=
  match kind.cursorReg v fullState with
  | some r => (Operand.reg r : Operand 64).read s
  | none => (Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (kind.cursorStackOffset v fullState)

def cursorEffect (kind : Kind) (v : Variant) {keccak : optParam Bool false} {fullState : optParam Bool false} (s : RamState) : Effect :=
  { rip := kind.start v keccak fullState + BitVec.ofNat 64 (kind.stateOffset v fullState)
    writes := [⟨(Operand.reg 7 : Operand 64), cursorValue kind s v fullState⟩] }

theorem cursorEffect_components (kind : Kind) (v : Variant) {keccak : optParam Bool false} {fullState : optParam Bool false} (s : RamState) :
    (cursorEffect kind v (keccak := keccak) (fullState := fullState) s).components = [.reg 7, .rip] := rfl

theorem cursor_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (fun s ↦ s.RIP = kind.start v keccak fullState + (12 : BitVec 64))
      (codeRange (kind.start v keccak fullState + (12 : BitVec 64)) (cursorBytes kind v fullState)) (cursorEffect kind v (keccak := keccak) (fullState := fullState)) := by
  unfold cursorEffect
  generalize hp : kind.start v keccak fullState = p
  have shape : kind.cursorReg v fullState = some 13 ∨ kind.cursorReg v fullState = some 5 ∨
      (kind.cursorReg v fullState = none ∧ kind.cursorStackOffset v fullState = 208) ∨
      (kind.cursorReg v fullState = none ∧ kind.cursorStackOffset v fullState = 224) ∨
      (kind.cursorReg v fullState = none ∧ kind.cursorStackOffset v fullState = 464) := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with hr | hr | ⟨hr, ho⟩ | ⟨hr, ho⟩ | ⟨hr, ho⟩
  · have he : movR64R64Effect (p + 12) 7 13 = (fun s ↦
        { rip := p + BitVec.ofNat 64 (kind.stateOffset v fullState),
          writes := [⟨(Operand.reg 7 : Operand 64), cursorValue kind s v fullState⟩] }) := by
      funext s
      simp [movR64R64Effect, cursorValue, Kind.stateOffset, hr, BitVec.add_assoc]
    rw [← he]
    simp only [cursorBytes, hr]
    exact mov_r64_r64_effect_step _ 0x4c 0xef (by unfold RexWPrefix; decide) (by decide)
  · have he : movR64R64Effect (p + 12) 7 5 = (fun s ↦
        { rip := p + BitVec.ofNat 64 (kind.stateOffset v fullState),
          writes := [⟨(Operand.reg 7 : Operand 64), cursorValue kind s v fullState⟩] }) := by
      funext s
      simp [movR64R64Effect, cursorValue, Kind.stateOffset, hr, BitVec.add_assoc]
    rw [← he]
    simp only [cursorBytes, hr]
    exact mov_r64_r64_effect_step _ 0x48 0xef (by unfold RexWPrefix; decide) (by decide)
  · have he : leaR64Effect (p + 12) 7 (.sib 4 none 0 (.d32 208)) = (fun s ↦
        { rip := p + BitVec.ofNat 64 (kind.stateOffset v fullState),
          writes := [⟨(Operand.reg 7 : Operand 64), cursorValue kind s v fullState⟩] }) := by
      funext s
      simp [leaR64Effect, cursorValue, Kind.stateOffset, hr, ho,
        leaLen, AddrMode.tail, Disp.bytes, AddrMode.addr, AddrMode.reg64, Disp.value, BitVec.add_assoc]
    rw [← he]
    simp only [cursorBytes, hr, ho]
    exact lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 208)) (by unfold AddrMode.Valid; decide) rfl rfl
  · have he : leaR64Effect (p + 12) 7 (.sib 4 none 0 (.d32 224)) = (fun s ↦
        { rip := p + BitVec.ofNat 64 (kind.stateOffset v fullState),
          writes := [⟨(Operand.reg 7 : Operand 64), cursorValue kind s v fullState⟩] }) := by
      funext s
      simp [leaR64Effect, cursorValue, Kind.stateOffset, hr, ho,
        leaLen, AddrMode.tail, Disp.bytes, AddrMode.addr, AddrMode.reg64, Disp.value, BitVec.add_assoc]
    rw [← he]
    simp only [cursorBytes, hr, ho]
    exact lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 224)) (by unfold AddrMode.Valid; decide) rfl rfl
  · have he : leaR64Effect (p + 12) 7 (.sib 4 none 0 (.d32 464)) = (fun s ↦
        { rip := p + BitVec.ofNat 64 (kind.stateOffset v fullState),
          writes := [⟨(Operand.reg 7 : Operand 64), cursorValue kind s v fullState⟩] }) := by
      funext s
      simp [leaR64Effect, cursorValue, Kind.stateOffset, hr, ho,
        leaLen, AddrMode.tail, Disp.bytes, AddrMode.addr, AddrMode.reg64, Disp.value, BitVec.add_assoc]
    rw [← he]
    simp only [cursorBytes, hr, ho]
    exact lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 464)) (by unfold AddrMode.Valid; decide) rfl rfl

theorem state_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (fun s ↦ s.RIP = kind.start v keccak fullState + BitVec.ofNat 64 (kind.stateOffset v fullState))
      (codeRange (kind.start v keccak fullState + BitVec.ofNat 64 (kind.stateOffset v fullState)) (stateBytes kind v fullState))
      (movR64R64Effect (kind.start v keccak fullState + BitVec.ofNat 64 (kind.stateOffset v fullState)) 6 (kind.stateReg v fullState)) := by
  have shape : stateBytes kind v fullState = [0x48, 0x89, 0xde] ∧ kind.stateReg v fullState = 3 ∨
      stateBytes kind v fullState = [0x4c, 0x89, 0xee] ∧ kind.stateReg v fullState = 13 ∨
      stateBytes kind v fullState = [0x48, 0x89, 0xee] ∧ kind.stateReg v fullState = 5 := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb, hr⟩
  · simp only [hb, hr]
    exact mov_r64_r64_effect_step _ 0x48 0xde (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hr]
    exact mov_r64_r64_effect_step _ 0x4c 0xee (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hr]
    exact mov_r64_r64_effect_step _ 0x48 0xee (by unfold RexWPrefix; decide) (by decide)

theorem index_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (fun s ↦ s.RIP = kind.start v keccak fullState + BitVec.ofNat 64 (kind.returnOffset v fullState))
      (codeRange (kind.start v keccak fullState + BitVec.ofNat 64 (kind.returnOffset v fullState)) (indexBytes kind v fullState))
      (movR64R64Effect (kind.start v keccak fullState + BitVec.ofNat 64 (kind.returnOffset v fullState)) (kind.indexReg v fullState) (kind.nextReg v fullState)) := by
  have shape : indexBytes kind v fullState = [0x48, 0x89, 0xd8] ∧ kind.indexReg v fullState = 0 ∧ kind.nextReg v fullState = 3 ∨
      indexBytes kind v fullState = [0x4c, 0x89, 0xe8] ∧ kind.indexReg v fullState = 0 ∧ kind.nextReg v fullState = 13 ∨
      indexBytes kind v fullState = [0x48, 0x89, 0xe8] ∧ kind.indexReg v fullState = 0 ∧ kind.nextReg v fullState = 5 ∨
      indexBytes kind v fullState = [0x48, 0x89, 0xeb] ∧ kind.indexReg v fullState = 3 ∧ kind.nextReg v fullState = 5 ∨
      indexBytes kind v fullState = [0x49, 0x89, 0xdd] ∧ kind.indexReg v fullState = 13 ∧ kind.nextReg v fullState = 3 ∨
      indexBytes kind v fullState = [0x4c, 0x89, 0xf8] ∧ kind.indexReg v fullState = 0 ∧ kind.nextReg v fullState = 15 ∨
      indexBytes kind v fullState = [0x4c, 0x89, 0xfb] ∧ kind.indexReg v fullState = 3 ∧ kind.nextReg v fullState = 15 := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with ⟨hb, hi, hn⟩ | ⟨hb, hi, hn⟩ | ⟨hb, hi, hn⟩ | ⟨hb, hi, hn⟩ | ⟨hb, hi, hn⟩ | ⟨hb, hi, hn⟩ | ⟨hb, hi, hn⟩
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x48 0xd8 (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x4c 0xe8 (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x48 0xe8 (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x48 0xeb (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x49 0xdd (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x4c 0xf8 (by unfold RexWPrefix; decide) (by decide)
  · simp only [hb, hi, hn]
    exact mov_r64_r64_effect_step _ 0x4c 0xfb (by unfold RexWPrefix; decide) (by decide)

def compareEffect (kind : Kind) (v : Variant) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false) : Effect :=
  { rip := kind.start v keccak fullState + BitVec.ofNat 64 (kind.compareOffset v fullState) +
      BitVec.ofNat 64 (if kind.memoryBound v fullState then (if fullState then 5 else 4) else 3)
    writes := []
    flags := some (.ofStatusFlags (cmpSpec ((kind.boundOperand s v fullState).read s)
      ((Operand.reg (kind.nextReg v fullState) : Operand 64).read s))) }

theorem compareEffect_components (kind : Kind) (v : Variant) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false) :
    (compareEffect kind v s keccak fullState).components = [.flags, .rip] := rfl

theorem compare_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (fun s ↦ s.RIP = kind.start v keccak fullState + BitVec.ofNat 64 (kind.compareOffset v fullState) ∧
      ∀ addr, kind.boundOperand s v fullState = .mem addr → MemReadable s addr 8)
      (codeRange (kind.start v keccak fullState + BitVec.ofNat 64 (kind.compareOffset v fullState)) (compareBytes kind v fullState))
      (fun s ↦ compareEffect kind v s keccak fullState) := by
  have shape : (kind.memoryBound v fullState = false ∧ kind.boundReg v fullState = 15 ∧ kind.nextReg v fullState = 3 ∧ compareBytes kind v fullState = [0x49, 0x39, 0xdf]) ∨
      (kind.memoryBound v fullState = false ∧ kind.boundReg v fullState = 3 ∧ kind.nextReg v fullState = 13 ∧ compareBytes kind v fullState = [0x4c, 0x39, 0xeb]) ∨
      (kind.memoryBound v fullState = false ∧ kind.boundReg v fullState = 13 ∧ kind.nextReg v fullState = 5 ∧ compareBytes kind v fullState = [0x49, 0x39, 0xed]) ∨
      (kind.memoryBound v fullState = false ∧ kind.boundReg v fullState = 15 ∧ kind.nextReg v fullState = 5 ∧ compareBytes kind v fullState = [0x49, 0x39, 0xef]) ∨
      (kind.memoryBound v fullState = false ∧ kind.boundReg v fullState = 3 ∧ kind.nextReg v fullState = 15 ∧ compareBytes kind v fullState = [0x4c, 0x39, 0xfb]) ∨
      (kind.memoryBound v fullState = true ∧ fullState = false ∧ kind.nextReg v fullState = 15 ∧ compareBytes kind v fullState = [0x4c, 0x39, 0x3c, 0x24]) ∨
      (kind.memoryBound v fullState = true ∧ fullState = true ∧ kind.nextReg v fullState = 15 ∧ compareBytes kind v fullState = [0x4c, 0x39, 0x7c, 0x24, 8]) := by
    cases kind <;> cases v <;> cases fullState <;> decide +kernel
  rcases shape with ⟨hm, hb, hn, hc⟩ | ⟨hm, hb, hn, hc⟩ | ⟨hm, hb, hn, hc⟩ |
    ⟨hm, hb, hn, hc⟩ | ⟨hm, hb, hn, hc⟩ | ⟨hm, hf, hn, hc⟩ | ⟨hm, hf, hn, hc⟩
  · simp only [compareEffect, Kind.boundOperand, hm, hb, hn, hc, Bool.false_eq_true, ite_false]
    exact (cmp_r64_r64_effect_step _ 0x49 0xdf (by unfold RexWPrefix; decide) (by decide)).mono_pre (fun _ h ↦ h.1)
  · simp only [compareEffect, Kind.boundOperand, hm, hb, hn, hc, Bool.false_eq_true, ite_false]
    exact (cmp_r64_r64_effect_step _ 0x4c 0xeb (by unfold RexWPrefix; decide) (by decide)).mono_pre (fun _ h ↦ h.1)
  · simp only [compareEffect, Kind.boundOperand, hm, hb, hn, hc, Bool.false_eq_true, ite_false]
    exact (cmp_r64_r64_effect_step _ 0x49 0xed (by unfold RexWPrefix; decide) (by decide)).mono_pre (fun _ h ↦ h.1)
  · simp only [compareEffect, Kind.boundOperand, hm, hb, hn, hc, Bool.false_eq_true, ite_false]
    exact (cmp_r64_r64_effect_step _ 0x49 0xef (by unfold RexWPrefix; decide) (by decide)).mono_pre (fun _ h ↦ h.1)
  · simp only [compareEffect, Kind.boundOperand, hm, hb, hn, hc, Bool.false_eq_true, ite_false]
    exact (cmp_r64_r64_effect_step _ 0x4c 0xfb (by unfold RexWPrefix; decide) (by decide)).mono_pre (fun _ h ↦ h.1)
  · subst fullState
    simp only [compareEffect, Kind.boundOperand, hm, hn, hc, Bool.false_eq_true, ite_true, ite_false]
    exact (cmp_m64_r64_effect_step _ 0x4c (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 .none) (by unfold AddrMode.Valid; decide) rfl rfl).mono_pre
      (fun s h ↦ ⟨h.1, h.2 _ rfl⟩)
  · subst fullState
    simp only [compareEffect, Kind.boundOperand, hm, hn, hc, ite_true]
    exact (cmp_m64_r64_effect_step _ 0x4c (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 8)) (by unfold AddrMode.Valid; decide) rfl rfl).mono_pre
      (fun s h ↦ ⟨h.1, h.2 _ rfl⟩)

theorem branch_step [Bindings] (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (fun s ↦ s.RIP = kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState))
      (codeRange (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) (branchBytes kind v fullState))
      (jccEffect (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) 2 5 ((kind.branchDisp v fullState).signExtend 64)) :=
  (jcc_rel8_effect_step (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) 5 (kind.branchDisp v fullState)).mono_pre fun s hs ↦
    ⟨hs, fun _ ↦ by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide +kernel⟩

private theorem advance [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap} {effect : RamState → Effect}
    (step : StepEffect pre code effect)
    (sub : ∀ x ∈ code, x ∈ Extracted.programImage)
    (nomem : ∀ c ∈ (effect s).components, ∀ a, ¬ c.Covers a)
    (target : InProgram (effect s).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (hp : pre s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (effect s).Holds s t := by
  have codeIn := (CodeIn.of_loaded loaded
    (SectionsLow.codeLow programSections_low)).mono sub
  obtain ⟨t, ht, hr, he⟩ := step s ready codeIn hp
  refine ⟨t, Advances.of_step ht (.inl ?_), hr, ?_, he⟩
  · rw [he.rip]
    exact fun h ↦ outside (h ▸ target)
  · unfold ProgramLoaded
    rw [he.agrees.external nomem]
    exact loaded

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem suffix_advance [Bindings] {boundary : ReturnBoundary} (kind : Kind) (v : Variant)
    {keccak : optParam Bool false} {fullState : optParam Bool false}
    (s : RamState) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip)
    (ip : s.RIP = kind.start v keccak fullState + BitVec.ofNat 64 (kind.returnOffset v fullState))
    (hfull : fullState = true → v = .sha256 := by simp_all)
    (hread : ∀ addr, kind.boundOperand s v fullState = .mem addr → MemReadable s addr 8 := by
      intro addr h; cases kind <;> simp_all [Kind.boundOperand, Kind.memoryBound, Kind.largeFollower]) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if (Operand.reg (kind.nextReg v fullState) : Operand 64).read s =
        (kind.boundOperand s v fullState).read s then kind.exit v keccak fullState else kind.start v keccak fullState) ∧
      (Operand.reg (kind.indexReg v fullState) : Operand 64).read t =
        (Operand.reg (kind.nextReg v fullState) : Operand 64).read s ∧
      AgreesExcept (suffixClobbers kind v fullState) s t := by
  obtain ⟨s1, a1, r1, l1, e1⟩ := advance (index_step kind v (keccak := keccak) (fullState := fullState)) (index_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [Component.Covers])
    (by have h := inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.compareOffset v fullState) (by simp)
        simpa only [BitVec.ofNat_add, movR64R64Effect, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset,
          Kind.returnOffset, Kind.compareOffset, Kind.branchOffset, Kind.endOffset,
          BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h) ready loaded outside ip
  have rsp1 : (Operand.reg 4 : Operand 64).read s1 = (Operand.reg 4 : Operand 64).read s :=
    e1.agrees.read (by simp only [movR64R64Effect_components]; cases kind <;> cases v <;> cases fullState <;> decide)
  have bo1 : kind.boundOperand s1 v fullState = kind.boundOperand s v fullState := by
    simp only [Kind.boundOperand, rsp1]
  have ext1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have b1 : (kind.boundOperand s1 v fullState).read s1 =
      (kind.boundOperand s v fullState).read s := by
    rw [bo1]
    unfold Kind.boundOperand
    split
    · simp only [Operand.read, ext1]
    · exact e1.agrees.read (by simp only [movR64R64Effect_components]; cases kind <;> cases v <;> cases fullState <;> first | decide | simp_all [Kind.memoryBound, Kind.largeFollower])
  have n1 : (Operand.reg (kind.nextReg v fullState) : Operand 64).read s1 =
      (Operand.reg (kind.nextReg v fullState) : Operand 64).read s :=
    e1.agrees.read (by simp only [movR64R64Effect_components]; cases kind <;> cases v <;> cases fullState <;> decide)
  obtain ⟨s2, a2, r2, l2, e2⟩ := advance (compare_step kind v (keccak := keccak) (fullState := fullState)) (compare_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [compareEffect_components, Component.Covers])
    (by have h := inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.branchOffset v fullState) (by simp)
        simpa only [BitVec.ofNat_add, compareEffect, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset,
          Kind.returnOffset, Kind.compareOffset, Kind.branchOffset, Kind.endOffset,
          BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h) r1 l1 outside
    ⟨by simpa only [BitVec.ofNat_add, movR64R64Effect, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e1.rip,
      fun addr h ↦ (hread addr (bo1.symm.trans h)).of_external_eq ext1⟩
  have z2 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (((kind.boundOperand s v fullState).read s -
        (Operand.reg (kind.nextReg v fullState) : Operand 64).read s) == 0) := by
    simpa [compareEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows,
      StatusFlagsOutcome.ofStatusFlags, FlagAllows, cmpSpec, subSpec, b1, n1] using
      e2.flags.2.2.2.1
  have target (u : RamState) :
      InProgram (jccEffect (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) 2 5
        ((kind.branchDisp v fullState).signExtend 64) u).rip := by
    simp only [jccEffect, branchEffect]
    split
    · have h : branchTarget (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) 2 ((kind.branchDisp v fullState).signExtend 64) =
          kind.start v keccak fullState := by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> rfl
      rw [h]
      simpa [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 0 (by simp)
    · have h := inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.endOffset v fullState) (by simp)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset,
        Kind.returnOffset, Kind.branchOffset, Kind.endOffset, BitVec.add_assoc,
        Nat.reduceAdd, BitVec.reduceAdd] using h
  obtain ⟨s3, a3, r3, l3, e3⟩ := advance (branch_step kind v (keccak := keccak) (fullState := fullState)) (branch_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [jccEffect, Component.Covers]) (target s2) r2 l2 outside
    (by simpa only [BitVec.ofNat_add, compareEffect, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e2.rip)
  refine ⟨s3, a1.trans (a2.trans a3), r3, l3, ?_, ?_, ?_⟩
  · have hback : branchTarget (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) 2
        ((kind.branchDisp v fullState).signExtend 64) = kind.start v keccak fullState := by
      cases fullState <;> cases keccak <;> cases kind <;> cases v <;> rfl
    have hz (a b : BitVec 64) : (a - b == 0) = decide (b = a) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add,
        BitVec.ofNat_eq_ofNat, BitVec.zero_add]
      exact eq_comm
    have hp := e3.rip
    change s3.RIP = (if !(StatusFlags.ofRFLAGS s2.RFLAGS).ZF then
      branchTarget (kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState)) 2
        ((kind.branchDisp v fullState).signExtend 64)
      else kind.start v keccak fullState + BitVec.ofNat 64 (kind.branchOffset v fullState) + 2) at hp
    rw [z2, hback, hz] at hp
    by_cases he : (Operand.reg (kind.nextReg v fullState) : Operand 64).read s =
        (kind.boundOperand s v fullState).read s
    · simpa only [BitVec.ofNat_add, he, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
        Kind.exit, Kind.endOffset, Kind.returnOffset, Kind.callOffset, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.branchOffset, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hp
    · simpa only [he, decide_false, Bool.not_false, ite_true, ite_false] using hp
  · have i3 := e3.agrees.read (n := 64) (r := (kind.indexReg v fullState)) (by simp [jccEffect])
    have i2 := e2.agrees.read (n := 64) (r := (kind.indexReg v fullState)) (by simp only [compareEffect_components, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true])
    exact i3.trans (i2.trans e1.writes)
  · exact (e1.agrees.trans (e2.agrees.trans e3.agrees)).mono (by
      simp [suffixClobbers, jccEffect, compareEffect_components])

private theorem tableMode_addr (kind : Kind) (base : BitVec 4) (s : RamState)
    (p : BitVec 64) (v : Variant := .sha256) (fullState : Bool := false) :
    (tableMode kind base v fullState).addr s p = tableAddress kind (base.setWidth 5) s v fullState := by
  cases kind <;> cases v <;> cases fullState <;> simp [tableMode, tableAddress, AddrMode.addr, AddrMode.reg64,
    Kind.indexReg, Kind.largeFollower, Disp.value, BitVec.ofNat_eq_ofNat, BitVec.add_zero]

private theorem tableAddress_eq {kind : Kind} {base : BitVec 5} {s t : RamState}
    {cs : List Component} {v : Variant} {fullState : Bool} (h : AgreesExcept cs s t)
    (hb : .reg base ∉ cs) (hi : .reg (kind.indexReg v fullState) ∉ cs) :
    tableAddress kind base t v fullState = tableAddress kind base s v fullState := by
  simp only [tableAddress, h.read hb, h.read hi]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem prefix_advance [Bindings] {boundary : ReturnBoundary} (kind : Kind) (v : Variant)
    {keccak : optParam Bool false} {fullState : optParam Bool false}
    (s : RamState) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip)
    (ip : s.RIP = kind.start v keccak fullState)
    (pointers : MemReadable s (tableAddress kind 12 s v fullState) 8)
    (lengths : MemReadable s (tableAddress kind 14 s v fullState) 8)
    (cursor : cursorValue kind s v fullState = (Operand.reg (kind.stateReg v fullState) : Operand 64).read s + 200)
    (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = kind.start v keccak fullState + BitVec.ofNat 64 (kind.callOffset v fullState) ∧
      (Operand.reg (kind.nextReg v fullState) : Operand 64).read t =
        (Operand.reg (kind.indexReg v fullState) : Operand 64).read s + 1 ∧
      (Operand.reg 2 : Operand 64).read t =
        (Operand.mem (tableAddress kind 12 s v fullState) : Operand 64).read s ∧
      (Operand.reg 1 : Operand 64).read t =
        (Operand.mem (tableAddress kind 14 s v fullState) : Operand 64).read s ∧
      (Operand.reg 6 : Operand 64).read t =
        (Operand.reg (kind.stateReg v fullState) : Operand 64).read s ∧
      (Operand.reg 7 : Operand 64).read t = (Operand.reg 6 : Operand 64).read t + 200 ∧
      AgreesExcept (prefixClobbers kind v fullState) s t := by
  obtain ⟨s1, a1, r1, l1, e1⟩ := advance (next_step kind v (keccak := keccak) (fullState := fullState)) (next_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [Component.Covers])
    (inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 4 (by simp)) ready loaded outside ip
  have ext1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have ptr1 : tableAddress kind 12 s1 v fullState = tableAddress kind 12 s v fullState :=
    tableAddress_eq e1.agrees (by simp only [leaR64Effect_components]; cases kind <;> cases v <;> cases fullState <;> decide)
      (by simp only [leaR64Effect_components]; cases kind <;> cases v <;> cases fullState <;> decide)
  obtain ⟨s2, a2, r2, l2, e2⟩ := advance (pointer_step kind v (keccak := keccak) (fullState := fullState)) (pointer_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [Component.Covers])
    (by simpa [movR64M64Effect, movLoadLen, tableMode, AddrMode.tail, Disp.bytes,
      List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc,
      Nat.reduceAdd, BitVec.reduceAdd] using inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 8 (by simp))
    r1 l1 outside ⟨e1.rip, by rw [ptr1]; exact pointers.of_external_eq ext1⟩
  have f12 := e1.agrees.trans e2.agrees
  have ext12 : s2.external = s.external := f12.external (by simp [Component.Covers])
  have len2 : tableAddress kind 14 s2 v fullState = tableAddress kind 14 s v fullState :=
    tableAddress_eq f12
      (by simp only [leaR64Effect_components, movR64M64Effect_components]; cases kind <;> cases v <;> cases fullState <;> decide)
      (by simp only [leaR64Effect_components, movR64M64Effect_components]; cases kind <;> cases v <;> cases fullState <;> decide)
  obtain ⟨s3, a3, r3, l3, e3⟩ := advance (length_step kind v (keccak := keccak) (fullState := fullState)) (length_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [Component.Covers])
    (by simpa [movR64M64Effect, movLoadLen, tableMode, AddrMode.tail, Disp.bytes,
      List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc,
      Nat.reduceAdd, BitVec.reduceAdd] using inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 12 (by simp)) r2 l2 outside
    ⟨by simpa [movR64M64Effect, movLoadLen, tableMode, AddrMode.tail, Disp.bytes,
        List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc,
        Nat.reduceAdd, BitVec.reduceAdd] using e2.rip,
      by rw [len2]; exact lengths.of_external_eq ext12⟩
  obtain ⟨s4, a4, r4, l4, e4⟩ := advance (cursor_step kind v (keccak := keccak) (fullState := fullState)) (cursor_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp only [cursorEffect_components, List.mem_cons, List.not_mem_nil, or_false];
        intro c hc a; rcases hc with rfl | rfl <;> simp [Component.Covers])
    (inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.stateOffset v fullState) (by simp)) r3 l3 outside
    (by simpa [movR64M64Effect, movLoadLen, tableMode, AddrMode.tail, Disp.bytes,
      List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc,
      Nat.reduceAdd, BitVec.reduceAdd] using e3.rip)
  obtain ⟨s5, a5, r5, l5, e5⟩ := advance (state_step kind v (keccak := keccak) (fullState := fullState)) (state_code kind v (keccak := keccak) (fullState := fullState) (hfull := hfull))
    (by simp [Component.Covers])
    (by have h := inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.callOffset v fullState) (by simp)
        simpa only [BitVec.ofNat_add, movR64R64Effect, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset,
          BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h)
    r4 l4 outside e4.rip
  have n1 : (Operand.reg (kind.nextReg v fullState) : Operand 64).read s1 =
      (Operand.reg (kind.indexReg v fullState) : Operand 64).read s + 1 := by
    have hn := e1.writes
    cases kind <;> cases v <;> cases fullState <;> exact hn
  have p2 : (Operand.reg 2 : Operand 64).read s2 =
      (Operand.mem (tableAddress kind 12 s v fullState) : Operand 64).read s := by
    have hp := e2.writes
    change (Operand.reg 2 : Operand 64).read s2 =
      (Operand.mem ((tableMode kind 12 v fullState).addr s1 _) : Operand 64).read s1 at hp
    rw [tableMode_addr (v := v) (fullState := fullState)] at hp
    change (Operand.reg 2 : Operand 64).read s2 =
      (Operand.mem (tableAddress kind 12 s1 v fullState) : Operand 64).read s1 at hp
    rw [ptr1] at hp
    simpa [Operand.read, ext1] using hp
  have l3read : (Operand.reg 1 : Operand 64).read s3 =
      (Operand.mem (tableAddress kind 14 s v fullState) : Operand 64).read s := by
    have hl := e3.writes
    change (Operand.reg 1 : Operand 64).read s3 =
      (Operand.mem ((tableMode kind 14 v fullState).addr s2 _) : Operand 64).read s2 at hl
    rw [tableMode_addr (v := v) (fullState := fullState)] at hl
    change (Operand.reg 1 : Operand 64).read s3 =
      (Operand.mem (tableAddress kind 14 s2 v fullState) : Operand 64).read s2 at hl
    rw [len2] at hl
    simpa [Operand.read, ext12] using hl
  have lanes : (Operand.reg 6 : Operand 64).read s5 =
      (Operand.reg (kind.stateReg v fullState) : Operand 64).read s := by
    exact e5.writes.trans ((f12.trans (e3.agrees.trans e4.agrees)).read
      (by simp only [leaR64Effect_components, movR64M64Effect_components, cursorEffect_components];
          cases kind <;> cases v <;> cases fullState <;> decide))
  have cur : cursorValue kind s3 v fullState = cursorValue kind s v fullState := by
    have h := f12.trans e3.agrees
    cases kind <;> cases v <;> cases fullState <;>
      first
      | exact h.read (by simp only [leaR64Effect_components, movR64M64Effect_components]; decide)
      | exact congrArg (· + _) (h.read (r := 4) (by simp only [leaR64Effect_components, movR64M64Effect_components]; decide))

  refine ⟨s5, a1.trans (a2.trans (a3.trans (a4.trans a5))), r5, l5, ?_, ?_, ?_, ?_, lanes, ?_, ?_⟩
  · simpa only [BitVec.ofNat_add, movR64R64Effect, Kind.stateOffset, Kind.cursorReg, Kind.largeFollower, Kind.memoryBound, Kind.callOffset, Kind.returnOffset, Kind.compareOffset,
      Kind.branchOffset, Kind.endOffset, BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e5.rip
  · exact ((e2.agrees.trans (e3.agrees.trans (e4.agrees.trans e5.agrees))).read
      (by simp only [movR64M64Effect_components, movR64R64Effect_components, cursorEffect_components];
          cases kind <;> cases v <;> cases fullState <;> decide)).trans n1
  · exact ((e3.agrees.trans (e4.agrees.trans e5.agrees)).read (by simp only [movR64M64Effect_components, movR64R64Effect_components, cursorEffect_components]; decide)).trans p2
  · exact ((e4.agrees.trans e5.agrees).read (by simp only [movR64R64Effect_components, cursorEffect_components]; decide)).trans l3read
  · rw [lanes]
    exact (e5.agrees.read (by simp only [movR64R64Effect_components]; decide)).trans (e4.writes.trans (cur.trans cursor))
  · exact (f12.trans (e3.agrees.trans (e4.agrees.trans e5.agrees))).mono
      (by simp only [leaR64Effect_components, movR64M64Effect_components, movR64R64Effect_components, cursorEffect_components]; simp [prefixClobbers])

end Sha3.Proofs.Wrapper.Loop
