import Sha3.Proofs.Wrapper.Reset.Call
import Sha3.Proofs.Finalize.Layout
import Sha3.Proofs.Memcpy
import Sha3.Proofs.Wrapper.Finish.Plain.Copy224Block
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Wrapper.Reset.Output

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def tempOffset (v : Variant) (fullState : Bool := false) : Nat :=
  if fullState then 440 else match v with
    | .sha224 | .sha256 => 56 | .sha384 => 72 | .sha512 => 88

def prepareOffset (v : Variant) (fullState : Bool := false) : Nat :=
  if fullState then 0xbc else match v with
    | .sha224 => 0xbc | .sha256 => 0xbd | .sha384 => 0xde | .sha512 => 0xf9

def callOffset (v : Variant) (fullState : Bool := false) : Nat :=
  prepareOffset v fullState + if fullState then 8 else 13

def compareOffset (v : Variant) (fullState : Bool := false) : Nat :=
  if fullState then 0xf6 else match v with
    | .sha224 => 0x103 | .sha256 => 0x107 | .sha384 => 0x144 | .sha512 => 0x184

def tempPointer (initial : RamState) (v : Variant) (mode : Mode)
    (keccak fullState : Bool) : BitVec 64 :=
  frameBase initial v mode keccak fullState + BitVec.ofNat 64 (tempOffset v fullState)

def preparePC (v : Variant) (mode : Mode) (keccak fullState : Bool) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (prepareOffset v fullState)

def callPC (v : Variant) (mode : Mode) (keccak fullState : Bool) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (callOffset v fullState)

def comparePC (v : Variant) (mode : Mode) (keccak fullState : Bool) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (compareOffset v fullState)

def stateDisp (v : Variant) (fullState : Bool) : Disp :=
  if fullState then .d8 32 else
    .d32 (BitVec.ofNat 32 (Mode.finalizeFixedReset.stateOffset v))

theorem state_image (v : Variant) (mode : Mode) (keccak fullState : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hf : fullState = true → v = .sha256 ∧ keccak = true) :
    ImageAt (preparePC v mode keccak fullState)
      (encodeLeaR64M 7 (.sib 4 none 0 (stateDisp v fullState))) := by
  rcases hm with rfl | rfl <;> cases fullState <;> cases keccak <;> cases v <;>
    first | (solve | have := hf rfl; simp_all) | (unfold ImageAt; decide +kernel)

theorem output_image (v : Variant) (mode : Mode) (keccak : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    ImageAt (preparePC v mode keccak false + 8)
      (encodeLeaR64M 6 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (tempOffset v))))) := by
  rcases hm with rfl | rfl <;> cases keccak <;> cases v <;>
    unfold ImageAt <;> decide +kernel

def callDisp (v : Variant) (mode : Mode) (keccak fullState : Bool) : BitVec 32 :=
  (Finalize.entryAddress v true keccak fullState - (callPC v mode keccak fullState + 5)).setWidth 32

theorem call_image (v : Variant) (mode : Mode) (keccak fullState : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hf : fullState = true → v = .sha256 ∧ keccak = true) :
    ImageAt (callPC v mode keccak fullState)
      (encodeCallRel32 (callDisp v mode keccak fullState)) := by
  rcases hm with rfl | rfl <;> cases fullState <;> cases keccak <;> cases v <;>
    first | (solve | have := hf rfl; simp_all) | (unfold ImageAt; decide +kernel)

theorem call_target (v : Variant) (mode : Mode) (keccak fullState : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    branchTarget (callPC v mode keccak fullState) 5
      ((callDisp v mode keccak fullState).signExtend 64) =
        Finalize.entryAddress v true keccak fullState := by
  rcases hm with rfl | rfl <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel

theorem temp_bounds (v : Variant) (mode : Mode) (keccak fullState : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    tempOffset v fullState + v.digestBytes fullState ≤ mode.frameSize v keccak fullState - 48 ∧
    (tempOffset v fullState + v.digestBytes fullState ≤ mode.stateOffset v keccak fullState ∨
      mode.stateOffset v keccak fullState + 201 ≤ tempOffset v fullState) := by
  rcases hm with rfl | rfl <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel

theorem prepare_state [bindings : Bindings] (v : Variant) (mode : Mode)
    {keccak fullState : Bool} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState)
    (hp : s.RIP = preparePC v mode keccak fullState)
    (hs : stackPtr s = frameBase initial v mode keccak fullState) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial v mode t keccak fullState ∧
      t.RIP = preparePC v mode keccak fullState + (if fullState then (5 : BitVec 64) else 8) ∧
      t.regValue .rdi = statePointer initial v mode keccak fullState ∧
      AgreesExcept [.reg 7, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  have himage := state_image v mode keccak fullState hm hCall.fullState_valid
  have heq : encodeLeaR64M 7 (.sib 4 none 0 (stateDisp v fullState)) =
      0x48 :: 0x8d :: (AddrMode.sib 4 none 0 (stateDisp v fullState)).modrm 7 ::
        (AddrMode.sib 4 none 0 (stateDisp v fullState)).tail := by
    cases v <;> cases fullState <;> rfl
  rw [heq] at himage
  obtain ⟨t, ht, it, _, et, ag⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (preparePC v mode keccak fullState) 0x48
      (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (stateDisp v fullState))
      (by cases v <;> cases fullState <;> decide +kernel)
      (by cases v <;> cases fullState <;> decide +kernel)
      (by cases v <;> cases fullState <;> decide +kernel))
    himage (changes := [.reg 7, .rip]) (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) inv hsp hp
  refine ⟨t, ht, it, ?_, ?_, ag⟩
  · have h := et.rip
    cases fullState <;> cases v <;> exact h
  · have h := et.writes
    change t.regValue .rdi = _ at h
    rw [statePointer]
    rcases hm with rfl | rfl <;> cases v <;> cases fullState <;>
      exact h.trans (congrArg (fun p : BitVec 64 ↦ p + _) hs)

theorem prepare_output [bindings : Bindings] (v : Variant) (mode : Mode)
    {keccak : Bool} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak false)
    (inv : Invariant initial v mode s keccak false)
    (hp : s.RIP = preparePC v mode keccak false + (8 : BitVec 64))
    (hs : stackPtr s = frameBase initial v mode keccak false) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial v mode t keccak false ∧
      t.RIP = callPC v mode keccak false ∧
      t.regValue .rsi = tempPointer initial v mode keccak false ∧
      AgreesExcept [.reg 6, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
  have himage := output_image v mode keccak hm
  have heq : encodeLeaR64M 6 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (tempOffset v)))) =
      0x48 :: 0x8d :: (AddrMode.sib 4 none 0 (.d8 (BitVec.ofNat 8 (tempOffset v)))).modrm 6 ::
        (AddrMode.sib 4 none 0 (.d8 (BitVec.ofNat 8 (tempOffset v)))).tail := by
    cases v <;> rfl
  rw [heq] at himage
  obtain ⟨t, ht, it, _, et, ag⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (preparePC v mode keccak false + 8) 0x48
      (by unfold RexWPrefix; decide +kernel) 6
      (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (tempOffset v))))
      (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
      (by cases v <;> decide +kernel))
    himage (changes := [.reg 6, .rip]) (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) inv hsp hp
  refine ⟨t, ht, it, et.rip.trans ?_, ?_, ag⟩
  · cases v <;> simp [leaR64Effect, preparePC, callPC, callOffset, prepareOffset, leaLen, AddrMode.tail,
      Disp.bytes, immBytes, BitVec.add_assoc]
  · have h := et.writes
    change t.regValue .rsi = _ at h
    cases v <;> exact h.trans (congrArg (fun p : BitVec 64 ↦ p + _) hs)

theorem full_output_image (mode : Mode)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    ImageAt (preparePC .sha256 mode true true + 5) [0x4c, 0x89, 0xee] := by
  rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel

theorem prepare_full_output [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = preparePC .sha256 mode true true + (5 : BitVec 64))
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (ho : s.regValue .r13 = tempPointer initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = callPC .sha256 mode true true ∧
      t.regValue .rsi = tempPointer initial .sha256 mode true true ∧
      AgreesExcept [.reg 6, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨t, ht, it, _, et, ag⟩ := advanceNoMemory hCall
    (mov_r64_r64_effect_step (preparePC .sha256 mode true true + 5) 0x4c 0xee
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (full_output_image mode hm) (changes := [.reg 6, .rip])
    (by simp only [movR64R64Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) inv hsp hp
  refine ⟨t, ht, it, et.rip.trans ?_, et.writes.trans ho, ag⟩
  simp [movR64R64Effect, preparePC, callPC, callOffset, prepareOffset, BitVec.add_assoc]

def zeroBytes : Variant → List UInt8
  | .sha224 =>
    [0xc7, 0x44, 0x24, 0x50, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x48, 0x0, 0x0, 0x0,
      0x0, 0x48, 0xc7, 0x44, 0x24, 0x40, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x38, 0x0,
      0x0, 0x0, 0x0]
  | .sha256 =>
    [0x48, 0xc7, 0x44, 0x24, 0x50, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x48, 0x0, 0x0,
      0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x40, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x38,
      0x0, 0x0, 0x0, 0x0]
  | .sha384 =>
    [0x48, 0xc7, 0x44, 0x24, 0x70, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x68, 0x0, 0x0,
      0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x60, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x58,
      0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x50, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44,
      0x24, 0x48, 0x0, 0x0, 0x0, 0x0]
  | .sha512 =>
    [0x48, 0xc7, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24,
      0x88, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x78, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44,
      0x24, 0x70, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x68, 0x0, 0x0, 0x0, 0x0, 0x48,
      0xc7, 0x44, 0x24, 0x60, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x58, 0x0, 0x0, 0x0,
      0x0]

def copyBytes : Variant → List UInt8
  | .sha224 =>
    [0x8b, 0x44, 0x24, 0x50, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x4c, 0x24, 0x48, 0x48, 0x89, 0x4c,
      0x24, 0x28, 0x48, 0x8b, 0x54, 0x24, 0x38, 0x48, 0x8b, 0x74, 0x24, 0x40, 0x48, 0x89, 0x74, 0x24,
      0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x89, 0x45, 0x18, 0x48, 0x89, 0x4d, 0x10, 0x48, 0x89, 0x75,
      0x8, 0x48, 0x89, 0x55, 0x0]
  | .sha256 =>
    [0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x4c, 0x24, 0x48, 0x48,
      0x89, 0x4c, 0x24, 0x28, 0x48, 0x8b, 0x54, 0x24, 0x38, 0x48, 0x8b, 0x74, 0x24, 0x40, 0x48, 0x89,
      0x74, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0x45, 0x18, 0x48, 0x89, 0x4d, 0x10,
      0x48, 0x89, 0x75, 0x8, 0x48, 0x89, 0x55, 0x0]
  | .sha384 =>
    [0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x4c, 0x24, 0x68, 0x48,
      0x89, 0x4c, 0x24, 0x38, 0x48, 0x8b, 0x54, 0x24, 0x60, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x8b,
      0x74, 0x24, 0x58, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x8b, 0x7c, 0x24, 0x48, 0x4c, 0x8b, 0x44,
      0x24, 0x50, 0x4c, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x7c, 0x24, 0x18, 0x48, 0x89, 0x45, 0x28,
      0x48, 0x89, 0x4d, 0x20, 0x48, 0x89, 0x55, 0x18, 0x48, 0x89, 0x75, 0x10, 0x4c, 0x89, 0x45, 0x8,
      0x48, 0x89, 0x7d, 0x0]
  | .sha512 =>
    [0x48, 0x8b, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x8b, 0x8c,
      0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x48, 0x48, 0x8b, 0x94, 0x24, 0x80, 0x0,
      0x0, 0x0, 0x48, 0x89, 0x54, 0x24, 0x40, 0x48, 0x8b, 0x74, 0x24, 0x78, 0x48, 0x89, 0x74, 0x24,
      0x38, 0x48, 0x8b, 0x7c, 0x24, 0x70, 0x48, 0x89, 0x7c, 0x24, 0x30, 0x4c, 0x8b, 0x44, 0x24, 0x68,
      0x4c, 0x89, 0x44, 0x24, 0x28, 0x4c, 0x8b, 0x4c, 0x24, 0x58, 0x4c, 0x8b, 0x54, 0x24, 0x60, 0x4c,
      0x89, 0x54, 0x24, 0x20, 0x4c, 0x89, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x45, 0x38, 0x48, 0x89, 0x4d,
      0x30, 0x48, 0x89, 0x55, 0x28, 0x48, 0x89, 0x75, 0x20, 0x48, 0x89, 0x7d, 0x18, 0x4c, 0x89, 0x45,
      0x10, 0x4c, 0x89, 0x55, 0x8, 0x4c, 0x89, 0x4d, 0x0]

def zeroOffset (v : Variant) : Nat :=
  match v with | .sha224 | .sha256 => 0x99 | .sha384 | .sha512 => 0xa8

theorem zero_image (v : Variant) (mode : Mode) (keccak : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    ImageAt ((mode.entry v keccak).entryAddress + BitVec.ofNat 64 (zeroOffset v))
      (zeroBytes v) := by
  rcases hm with rfl | rfl <;> cases keccak <;> cases v <;>
    unfold ImageAt <;> decide +kernel

theorem copy_image (v : Variant) (mode : Mode) (keccak : Bool)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    ImageAt (callPC v mode keccak false + 5) (copyBytes v) := by
  rcases hm with rfl | rfl <;> cases keccak <;> cases v <;>
    unfold ImageAt <;> decide +kernel

theorem zero_end (v : Variant) : zeroOffset v + (zeroBytes v).length = prepareOffset v := by
  cases v <;> decide +kernel

theorem copy_end (v : Variant) :
    callOffset v + 5 + (copyBytes v).length = compareOffset v := by
  cases v <;> decide +kernel


def fullCopyPC (mode : Mode) (offset : Nat) : BitVec 64 :=
  (mode.entry .sha256 true true).entryAddress + BitVec.ofNat 64 offset

def fullCopyChanges : List Component := [.reg 7, .reg 5, .reg 2, .reg 6, .rip]

theorem prepare_full_copy [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xc9)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (ho : s.regValue .r13 = tempPointer initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = fullCopyPC mode 0xe0 ∧
      t.regValue .rdi = frameBase initial .sha256 mode true true + 240 ∧
      t.regValue .rsi = tempPointer initial .sha256 mode true true ∧
      t.regValue .rdx = 200 ∧ t.regValue .rbp = 0x106a70 ∧
      AgreesExcept fullCopyChanges s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨a, ha, ia, spa, ea, aga⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (fullCopyPC mode 0xc9) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullCopyChanges) (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [fullCopyChanges, Component.Covers]) (by simp [fullCopyChanges]) inv hsp hp
  have ipa : a.RIP = fullCopyPC mode 0xd1 := ea.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  obtain ⟨b, hb, ib, spb, eb, agb⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (fullCopyPC mode 0xd1) 0x48 (by unfold RexWPrefix; decide +kernel) 5 (.rip ((0x106a70 - (fullCopyPC mode 0xd8)).setWidth 32)) trivial rfl rfl)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullCopyChanges) (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [fullCopyChanges, Component.Covers]) (by simp [fullCopyChanges]) ia spa ipa
  have ipb : b.RIP = fullCopyPC mode 0xd8 := eb.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  obtain ⟨c, hc, ic, spc, ec, agc⟩ := advanceNoMemory hCall
    (mov_r32_imm32_effect_step (fullCopyPC mode 0xd8) 0xba (by decide +kernel) 200)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullCopyChanges) (by simp only [movR32Imm32Effect_components]; decide +kernel)
    (by simp [fullCopyChanges, Component.Covers]) (by simp [fullCopyChanges]) ib spb ipb
  have ipc : c.RIP = fullCopyPC mode 0xdd := ec.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  obtain ⟨t, ht, it, spt, et, agt⟩ := advanceNoMemory hCall
    (mov_r64_r64_effect_step (fullCopyPC mode 0xdd) 0x4c 0xee (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullCopyChanges) (by simp only [movR64R64Effect_components]; decide +kernel)
    (by simp [fullCopyChanges, Component.Covers]) (by simp [fullCopyChanges]) ic spc ipc
  have ipt : t.RIP = fullCopyPC mode 0xe0 := et.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have ag := ((aga.trans agb).trans agc).trans agt
  have ag' : AgreesExcept fullCopyChanges s t := ag.mono (by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq <;> exact hq)
  refine ⟨t, ha.trans (hb.trans (hc.trans ht)), it, ipt, ?_, ?_, ?_, ?_, ag'⟩
  · have ea' : a.regValue .rdi = stackPtr s + 240 := ea.writes
    have hab : b.regValue .rdi = a.regValue .rdi := eb.agrees.read (r := 7) (n := 64) (by
      simp only [leaR64Effect_components]; decide +kernel)
    have hbc : c.regValue .rdi = b.regValue .rdi := ec.agrees.read (r := 7) (n := 64) (by
      simp only [movR32Imm32Effect_components]; decide +kernel)
    have hct : t.regValue .rdi = c.regValue .rdi := et.agrees.read (r := 7) (n := 64) (by
      simp only [movR64R64Effect_components]; decide +kernel)
    exact hct.trans (hbc.trans (hab.trans (ea'.trans (congrArg (fun p : BitVec 64 ↦ p + 240) hs))))
  · exact et.writes.trans ((agc.read (r := 13) (n := 64) (by simp [fullCopyChanges])).trans
      ((agb.read (r := 13) (n := 64) (by simp [fullCopyChanges])).trans
        ((aga.read (r := 13) (n := 64) (by simp [fullCopyChanges])).trans ho)))
  · exact (et.agrees.read (r := 2) (n := 64) (by
      simp only [movR64R64Effect_components]; decide +kernel)).trans ec.writes
  · have hb : b.regValue .rbp = 0x106a70 := eb.writes.trans (by
      rcases hm with rfl | rfl <;> rfl)
    exact (et.agrees.read (r := 5) (n := 64) (by
      simp only [movR64R64Effect_components]; decide +kernel)).trans
      ((ec.agrees.read (r := 5) (n := 64) (by
        simp only [movR32Imm32Effect_components]; decide +kernel)).trans hb)


theorem full_copy_call [bindings : Bindings] (mode : Mode) (offset : Nat)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hc : offset = 0xe0 ∨ offset = 0xf4)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode offset)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (htarget : s.regValue .rbp = 0x106a70) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial .sha256 mode t true true ∧ t.RIP = (0x106a70 : BitVec 64) ∧
      stackPtr t = initial.regValue .rsp - 704 ∧ stackTop t = fullCopyPC mode offset + (2 : BitVec 64) ∧
      AgreesExcept [.reg 4, .mem (initial.regValue .rsp - 704) 8, .rip] s t ∧
      (callEffect (fun _ ↦ 0x106a70) (fullCopyPC mode offset + (2 : BitVec 64)) s).Holds s t := by
  have hb : 704 ≤ (mode.entry .sha256 true true).minStackBytes := by
    rcases hm with rfl | rfl <;> decide +kernel
  have hsp : stackPtr s = initial.regValue .rsp - 696 := by
    rcases hm with rfl | rfl <;> exact hs
  have hMem := stack_push_readable_after (n := 87) inv hCall.stackAvailable hb hsp
  have himage : ImageAt (fullCopyPC mode offset) [0xff, 0xd5] := by
    rcases hm with rfl | rfl <;> rcases hc with rfl | rfl <;>
      unfold ImageAt <;> decide +kernel
  have hcode := himage.code inv.loaded
  have htarget' : ((Operand.reg 5 : Operand 64).read s).toNat < 2^32 := by
    change (s.regValue .rbp).toNat < 2^32
    rw [htarget]
    decide +kernel
  have hstep := call_r64_step_of_readable s inv.ready [] (by simp) (by simp) rfl rfl rfl
    0xd5 (by decide +kernel) (by decide +kernel)
    (hp ▸ hcode.bytesAt) (hp ▸ hcode.low (by simp) (by simp)) htarget' hMem.1 hMem.2
  have hstep' : Machine.step s = some (.next (afterStep s 2 fun t ↦
      callState (callFrom false t (fullCopyPC mode offset + (2 : BitVec 64)))
        (fullCopyPC mode offset + (2 : BitVec 64)) 0x106a70)) := by
    simpa only [List.length_nil, Nat.zero_add, BitVec.add_eq, BitVec.ofNat_eq_ofNat, hp, show
      (Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
        (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm 0xd5)) : Operand 64).read s =
        s.regValue .rbp from rfl, htarget] using hstep
  exact Finish.callAt 696 2 false (fullCopyPC mode offset + (2 : BitVec 64)) 0x106a70
    hCall hb inv hsp hstep'


theorem prepare_full_second_copy [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xe2)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (ho : (Operand.mem (frameBase initial .sha256 mode true true + 16) : Operand 64).read s = out) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧
      Invariant initial .sha256 mode t true true ∧ t.RIP = fullCopyPC mode 0xf4 ∧
      t.regValue .rdi = out ∧ t.regValue .rsi = frameBase initial .sha256 mode true true + 240 ∧
      t.regValue .rdx = 200 ∧ AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨a, ha, ia, spa, ea, aga⟩ := advanceNoMemory hCall
    (mov_r32_imm32_effect_step (fullCopyPC mode 0xe2) 0xba (by decide +kernel) 200)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 2, .reg 7, .reg 6, .rip])
    (by simp only [movR32Imm32Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) inv hsp hp
  have ipa : a.RIP = fullCopyPC mode 0xe7 := ea.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have hsa : stackPtr a = frameBase initial .sha256 mode true true :=
    (aga.read (r := 4) (n := 64) (by decide +kernel)).trans hs
  have hra : MemReadable a (stackPtr a + 16) 8 := by
    rw [hsa]
    apply ia.frameReadable hCall.stackAvailable
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨b, hb, ib, spb, eb, agb⟩ := advanceNoMemory hCall
    (mov_r64_m64_effect_step (fullCopyPC mode 0xe7) 0x48
      (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 16))
      (by decide +kernel) rfl rfl)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 2, .reg 7, .reg 6, .rip])
    (by simp only [movR64M64Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) ia spa ⟨ipa, hra⟩
  have ipb : b.RIP = fullCopyPC mode 0xec := eb.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have hsb : stackPtr b = frameBase initial .sha256 mode true true :=
    (agb.read (r := 4) (n := 64) (by decide +kernel)).trans hsa
  obtain ⟨t, ht, it, _, et, agt⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (fullCopyPC mode 0xec) 0x48
      (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d32 240))
      (by decide +kernel) rfl rfl)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 2, .reg 7, .reg 6, .rip])
    (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) ib spb ipb
  have ag : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t :=
    ((aga.trans agb).trans agt).mono (by
      intro q hq
      simp only [List.mem_append] at hq
      rcases hq with (hq | hq) | hq <;> exact hq)
  refine ⟨t, ha.trans (hb.trans ht), it, et.rip.trans ?_, ?_, ?_, ?_, ag⟩
  · rcases hm with rfl | rfl <;> rfl
  · have heb : b.regValue .rdi = out := by
      have he : b.regValue .rdi = (Operand.mem (stackPtr a + 16) : Operand 64).read a := eb.writes
      rw [hsa] at he
      exact he.trans ((congrArg (fun mem ↦ memLoad mem
        (frameBase initial .sha256 mode true true + 16) 64)
        (aga.external (by simp [Component.Covers]))).trans ho)
    exact (et.agrees.read (r := 7) (n := 64) (by
      simp only [leaR64Effect_components]; decide +kernel)).trans heb
  · exact et.writes.trans (congrArg (fun p : BitVec 64 ↦ p + 240) hsb)
  · exact (et.agrees.read (r := 2) (n := 64) (by
      simp only [leaR64Effect_components]; decide +kernel)).trans
      ((eb.agrees.read (r := 2) (n := 64) (by
        simp only [movR64M64Effect_components]; decide +kernel)).trans ea.writes)


theorem full_first_copy_pre [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (ip : s.RIP = (0x106a70 : BitVec 64))
    (sp : stackPtr s = frameBase initial .sha256 mode true true - 8)
    (dst : (Operand.reg 7 : Operand 64).read s = frameBase initial .sha256 mode true true + 240)
    (src : (Operand.reg 6 : Operand 64).read s = frameBase initial .sha256 mode true true + 440)
    (len : (Operand.reg 2 : Operand 64).read s = 200)
    (ret : stackTop s = fullCopyPC mode 0xe2) : Memcpy.Pre (returnBoundary initial) s 200 false := by
  have hStack := hCall.stackAvailable
  have budget : mode.frameSize .sha256 true true ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true]; omega
  have hf : mode.frameSize .sha256 true true = 696 := by
    rcases hm with rfl | rfl <;> rfl
  have destRead : MemReadable s (frameBase initial .sha256 mode true true + 240) 200 :=
    inv.frameReadable hStack (by rw [hf]; decide +kernel)
  have sourceRead : MemReadable s (frameBase initial .sha256 mode true true + 440) 200 :=
    inv.frameReadable hStack (by rw [hf]; decide +kernel)
  have destNat : (frameBase initial .sha256 mode true true + 240).toNat =
      (frameBase initial .sha256 mode true true).toNat + 240 :=
    frameAddress_toNat hStack budget (offset := 240) (by rw [hf]; decide +kernel)
  have srcNat : (frameBase initial .sha256 mode true true + 440).toNat =
      (frameBase initial .sha256 mode true true).toNat + 440 :=
    frameAddress_toNat hStack budget (offset := 440) (by rw [hf]; decide +kernel)
  have destCover : ∀ address,
      (MemoryRegion.mk (frameBase initial .sha256 mode true true + 240).toNat 200).Contains address →
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).Contains address := by
    intro address ha
    obtain ⟨hLo, hHi⟩ := frameBase_bounds hStack budget
    change _ ≤ address ∧ address < _ at ha ⊢
    rw [destNat] at ha
    dsimp only [MemoryRegion.start, MemoryRegion.size] at ha
    rw [hf] at hHi
    omega
  have h704 : 704 ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true, hf]; decide +kernel
  have he : frameBase initial .sha256 mode true true - 8 =
      initial.regValue .rsp - BitVec.ofNat 64 704 := by
    rw [frameBase, hf, BitVec.sub_sub]
    rfl
  have stackRead : MemReadable s (frameBase initial .sha256 mode true true - 8) 8 := by
    rw [he]
    refine ⟨?_, ?_⟩
    · have hl := stack_sub_low hStack h704
      change _ + 704 < 2^32 at hl
      change (initial.regValue .rsp - BitVec.ofNat 64 704).toNat + 8 ≤ 2^32
      omega
    · intro i hi
      exact inv.grows _ (Option.isSome_iff_exists.mpr
        (stack_sub_allocated hStack h704 (by omega)))
  refine ⟨ip, len, trivial, inv.direction, src ▸ sourceRead, dst ▸ destRead, ?_, ?_, ?_,
    sp ▸ stackRead, ?_, ?_, ?_, ?_⟩
  · rw [src, dst, srcNat, destNat]
    exact .inr (by omega)
  · rw [dst]
    intro address ha ht
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial .sha256 mode true true)
      address (destCover _ ha) (.inr ht)
  · rw [dst]
    intro address ha hp
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial .sha256 mode true true)
      address (destCover _ ha) (.inl hp)
  · rw [ret]
    rcases hm with rfl | rfl <;> decide +kernel
  · rw [dst, sp]
    have haddr : frameBase initial .sha256 mode true true + 240 =
        (frameBase initial .sha256 mode true true - 8) + 248 := by
      rw [show (248 : BitVec 64) = 8 + 240 from rfl,
        ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [haddr]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
        (a := 248) (b := 0) (len := 200) (count := 8)
        (by decide) (by decide) (.inr (by decide))
  · rw [sp, he]
    exact Finish.stackSub_ne_returnBoundary initial (704 : BitVec 64) (by decide)
  · right
    rw [sp, BitVec.sub_add_cancel, frameBase, hf]
    exact Finish.stackSub_ne_returnBoundary initial (696 : BitVec 64) (by decide)


theorem full_second_copy_pre [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (ip : s.RIP = (0x106a70 : BitVec 64))
    (sp : stackPtr s = frameBase initial .sha256 mode true true - 8)
    (dst : (Operand.reg 7 : Operand 64).read s = out)
    (src : (Operand.reg 6 : Operand 64).read s = frameBase initial .sha256 mode true true + 240)
    (len : (Operand.reg 2 : Operand 64).read s = 200)
    (ret : stackTop s = fullCopyPC mode 0xf6)
    (hOut : ValidOutput initial ⟨out.toNat, 200⟩)
    (hMember : (⟨out.toNat, 200⟩ : MemoryRegion) ∈ writeRegions initial .sha256 mode true true)
    (hApart : (⟨out.toNat, 200⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes)) :
    Memcpy.Pre (returnBoundary initial) s 200 false := by
  have hStack := hCall.stackAvailable
  have budget : mode.frameSize .sha256 true true ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true]; omega
  have hf : mode.frameSize .sha256 true true = 696 := by
    rcases hm with rfl | rfl <;> rfl
  have h704 : 704 ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true, hf]; decide +kernel
  have he : frameBase initial .sha256 mode true true - 8 =
      initial.regValue .rsp - BitVec.ofNat 64 704 := by
    rw [frameBase, hf, BitVec.sub_sub]
    rfl
  have stackRead : MemReadable s (frameBase initial .sha256 mode true true - 8) 8 := by
    rw [he]
    refine ⟨?_, ?_⟩
    · have hl := stack_sub_low hStack h704
      change _ + 704 < 2^32 at hl
      change (initial.regValue .rsp - BitVec.ofNat 64 704).toNat + 8 ≤ 2^32
      omega
    · intro i hi
      exact inv.grows _ (Option.isSome_iff_exists.mpr
        (stack_sub_allocated hStack h704 (by omega)))
  have sourceRead : MemReadable s (frameBase initial .sha256 mode true true + 240) 200 :=
    inv.frameReadable hStack (by rw [hf]; decide +kernel)
  have destRead : MemReadable s out 200 := by
    apply memReadable_of_region hOut.2.1 _ (Nat.le_refl _) (Nat.le_refl _)
    intro address ha
    exact Option.isSome_iff_exists.mp
      (inv.grows address (Option.isSome_iff_exists.mpr (hOut.2.2 address ha)))
  have sourceNat : (frameBase initial .sha256 mode true true + 240).toNat =
      (frameBase initial .sha256 mode true true).toNat + 240 :=
    frameAddress_toNat hStack budget (offset := 240) (by rw [hf]; decide +kernel)
  have sourceCover : ∀ address,
      (MemoryRegion.mk (frameBase initial .sha256 mode true true + 240).toNat 200).Contains address →
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).Contains address := by
    intro address ha
    obtain ⟨hLo, hHi⟩ := frameBase_bounds hStack budget
    change _ ≤ address ∧ address < _ at ha ⊢
    rw [sourceNat] at ha
    dsimp only [MemoryRegion.start, MemoryRegion.size] at ha
    rw [hf] at hHi
    omega
  refine ⟨ip, len, trivial, inv.direction, src ▸ sourceRead, dst ▸ destRead, ?_, ?_, ?_,
    sp ▸ stackRead, ?_, ?_, ?_, ?_⟩
  · rw [src, dst]
    apply Classical.byContradiction
    intro h
    have h' := hApart (max out.toNat (frameBase initial .sha256 mode true true + 240).toNat)
    simp only [MemoryRegion.Contains] at h'
    apply h' ⟨Nat.le_max_left _ _, by omega⟩
    apply sourceCover
    change _ ≤ _ ∧ _ < _
    dsimp only [MemoryRegion.start, MemoryRegion.size]
    constructor
    · exact Nat.le_max_right _ _
    · omega
  · rw [dst]
    intro address ha ht
    exact writeRegions_avoid hCall _ hMember address ha (.inr ht)
  · rw [dst]
    intro address ha hp
    exact writeRegions_avoid hCall _ hMember address ha (.inl hp)
  · rw [ret]
    rcases hm with rfl | rfl <;> decide +kernel
  · rw [dst, sp]
    intro i hi j hj hEq
    apply hApart (out + BitVec.ofNat 64 i).toNat
    · exact Memcpy.range_contains (Nat.le_of_lt hOut.2.1) hi
    · rw [hEq, he]
      exact stack_sub_contains hStack h704 (by omega)
  · rw [sp, he]
    exact Finish.stackSub_ne_returnBoundary initial (704 : BitVec 64) (by decide)
  · right
    rw [sp, BitVec.sub_add_cancel, frameBase, hf]
    exact Finish.stackSub_ne_returnBoundary initial (696 : BitVec 64) (by decide)


def fullFirstCopyChanges (initial : RamState) (mode : Mode) : List Component :=
  fullCopyChanges ++ [.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] ++
    Memcpy.clobbers (frameBase initial .sha256 mode true true + 240) 200

theorem full_first_copy_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    (mode : Mode) {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xc9)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (ho : s.regValue .r13 = tempPointer initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial)
        (5 + Memcpy.memcpy200Steps (frameBase initial .sha256 mode true true + 240)) s t ∧
      Invariant initial .sha256 mode t true true ∧ t.RIP = fullCopyPC mode 0xe2 ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧ t.regValue .rbp = 0x106a70 ∧
      (∀ i < 200, t.external[frameBase initial .sha256 mode true true + 240 + BitVec.ofNat 64 i]? =
        s.external[tempPointer initial .sha256 mode true true + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (fullFirstCopyChanges initial mode) s t := by
  have hf : mode.frameSize .sha256 true true = 696 := by
    rcases hm with rfl | rfl <;> rfl
  have hframe : initial.regValue .rsp - 704 = frameBase initial .sha256 mode true true - 8 := by
    rw [frameBase, hf, BitVec.sub_sub]
    rfl
  obtain ⟨a, ha, ia, ipa, da, sa, la, ta, aga⟩ :=
    prepare_full_copy mode hm hCall inv hp hs ho
  have spa : stackPtr a = frameBase initial .sha256 mode true true :=
    (aga.read (r := 4) (n := 64) (by simp [fullCopyChanges])).trans hs
  obtain ⟨b, hb, ib, ipb, spb, retb, agb, eb⟩ :=
    full_copy_call mode 0xe0 hm (.inl rfl) hCall ia ipa spa ta
  rw [hframe] at spb agb
  have db : (Operand.reg 7 : Operand 64).read b = frameBase initial .sha256 mode true true + 240 :=
    (agb.read (r := 7) (n := 64) (by simp)).trans da
  have sb : (Operand.reg 6 : Operand 64).read b = frameBase initial .sha256 mode true true + 440 :=
    (agb.read (r := 6) (n := 64) (by simp)).trans sa
  have lb : (Operand.reg 2 : Operand 64).read b = 200 :=
    (agb.read (r := 2) (n := 64) (by simp)).trans la
  have tb : b.regValue .rbp = 0x106a70 :=
    (agb.read (r := 5) (n := 64) (by simp)).trans ta
  have retb' : stackTop b = fullCopyPC mode 0xe2 := retb.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have pre := full_first_copy_pre mode hm hCall ib ipb spb db sb lb retb'
  obtain ⟨t, ht, done⟩ := Memcpy.memcpy200_steps hstride (returnBoundary initial) b ib.ready ib.code pre
  rw [db] at ht
  have agbt : AgreesExcept (Memcpy.clobbers (frameBase initial .sha256 mode true true + 240) 200) b t :=
    db ▸ done.agrees
  have it : Invariant initial .sha256 mode t true true := by
    apply ib.of_agreesExcept hCall done.ready agbt (hd := by simp [Memcpy.clobbers])
    apply Memcpy.clobbers_writesWithin
    intro i hi
    refine ⟨_, stack_mem_writeRegions initial .sha256 mode true true, ?_⟩
    rw [BitVec.add_assoc, show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl, ← BitVec.ofNat_add]
    apply frameAddress_contains hCall.stackAvailable (by
      rw [Mode.stackBudget mode .sha256 true true]; omega)
    rw [hf]
    omega
  refine ⟨t, ?_, it, done.rip.trans retb', ?_, ?_, ?_, (aga.trans agb).trans agbt⟩
  · have run := ha.trans (hb.trans ht)
    simpa only [← Nat.add_assoc, show 4 + 1 = 5 from rfl] using run
  · rw [done.rsp, spb, BitVec.sub_add_cancel]
  · exact (agbt.read (r := 5) (n := 64) (by simp [Memcpy.clobbers])).trans tb
  · intro i hi
    rw [show tempPointer initial .sha256 mode true true =
      frameBase initial .sha256 mode true true + 440 from rfl]
    have hcopy := done.copy i hi
    rw [db, sb] at hcopy
    rw [hcopy, agb.byte, aga.external (by simp [fullCopyChanges, Component.Covers])]
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨j, hj, he⟩ := hcov
    have hr := RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
      (a := 448) (b := 0) (len := 200) (count := 8)
      (by decide) (by decide) (.inr (by decide)) i hi j hj
    have heq : frameBase initial .sha256 mode true true - 8 + 448 =
        frameBase initial .sha256 mode true true + 440 := by
      rw [show (448 : BitVec 64) = 8 + 440 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hr heq
    rw [heq] at hr
    exact hr he


def fullSecondCopyChanges (initial : RamState) (mode : Mode) (out : BitVec 64) : List Component :=
  [.reg 2, .reg 7, .reg 6, .rip] ++
    [.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] ++
    Memcpy.clobbers out 200

theorem full_second_copy_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    (mode : Mode) {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xe2)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (ho : (Operand.mem (frameBase initial .sha256 mode true true + 16) : Operand 64).read s = out)
    (htarget : s.regValue .rbp = 0x106a70)
    (hOut : ValidOutput initial ⟨out.toNat, 200⟩)
    (hMember : (⟨out.toNat, 200⟩ : MemoryRegion) ∈ writeRegions initial .sha256 mode true true)
    (hApart : (⟨out.toNat, 200⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes)) :
    ∃ t, Advances (returnBoundary initial) (4 + Memcpy.memcpy200Steps out) s t ∧
      Invariant initial .sha256 mode t true true ∧ t.RIP = comparePC .sha256 mode true true ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      (∀ i < 200, t.external[out + BitVec.ofNat 64 i]? =
        s.external[frameBase initial .sha256 mode true true + 240 + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (fullSecondCopyChanges initial mode out) s t := by
  have hf : mode.frameSize .sha256 true true = 696 := by
    rcases hm with rfl | rfl <;> rfl
  have hframe : initial.regValue .rsp - 704 = frameBase initial .sha256 mode true true - 8 := by
    rw [frameBase, hf, BitVec.sub_sub]
    rfl
  obtain ⟨a, ha, ia, ipa, da, sa, la, aga⟩ :=
    prepare_full_second_copy mode hm hCall inv hp hs ho
  have spa : stackPtr a = frameBase initial .sha256 mode true true :=
    (aga.read (r := 4) (n := 64) (by decide +kernel)).trans hs
  have ta : a.regValue .rbp = 0x106a70 :=
    (aga.read (r := 5) (n := 64) (by decide +kernel)).trans htarget
  obtain ⟨b, hb, ib, ipb, spb, retb, agb, eb⟩ :=
    full_copy_call mode 0xf4 hm (.inr rfl) hCall ia ipa spa ta
  rw [hframe] at spb agb
  have db : (Operand.reg 7 : Operand 64).read b = out :=
    (agb.read (r := 7) (n := 64) (by simp)).trans da
  have sb : (Operand.reg 6 : Operand 64).read b = frameBase initial .sha256 mode true true + 240 :=
    (agb.read (r := 6) (n := 64) (by simp)).trans sa
  have lb : (Operand.reg 2 : Operand 64).read b = 200 :=
    (agb.read (r := 2) (n := 64) (by simp)).trans la
  have retb' : stackTop b = fullCopyPC mode 0xf6 := retb.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have pre := full_second_copy_pre mode hm hCall ib ipb spb db sb lb retb' hOut hMember hApart
  obtain ⟨t, ht, done⟩ := Memcpy.memcpy200_steps hstride (returnBoundary initial) b ib.ready ib.code pre
  rw [db] at ht
  have agbt : AgreesExcept (Memcpy.clobbers out 200) b t := db ▸ done.agrees
  have it : Invariant initial .sha256 mode t true true := by
    apply ib.of_agreesExcept hCall done.ready agbt (hd := by simp [Memcpy.clobbers])
    apply Memcpy.clobbers_writesWithin
    intro i hi
    exact ⟨_, hMember, Memcpy.range_contains (Nat.le_of_lt hOut.2.1) hi⟩
  refine ⟨t, ?_, it, done.rip.trans retb', ?_, ?_, (aga.trans agb).trans agbt⟩
  · have run := ha.trans (hb.trans ht)
    simpa only [← Nat.add_assoc, show 3 + 1 = 4 from rfl] using run
  · rw [done.rsp, spb, BitVec.sub_add_cancel]
  · intro i hi
    have hcopy := done.copy i hi
    rw [db, sb] at hcopy
    rw [hcopy, agb.byte, aga.external (by simp [Component.Covers])]
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨j, hj, he⟩ := hcov
    have hr := RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
      (a := 248) (b := 0) (len := 200) (count := 8)
      (by decide) (by decide) (.inr (by decide)) i hi j hj
    have heq : frameBase initial .sha256 mode true true - 8 + 248 =
        frameBase initial .sha256 mode true true + 240 := by
      rw [show (248 : BitVec 64) = 8 + 240 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hr heq
    rw [heq] at hr
    exact hr he


theorem full_first_copy_byte {initial s t : RamState} {mode : Mode} {offset : Nat}
    (ha : AgreesExcept (fullFirstCopyChanges initial mode) s t) (ho : offset < 704)
    (haway : offset < 240 ∨ 440 ≤ offset) :
    t.external[frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset]? =
      s.external[frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset]? := by
  apply ha.byte
  intro c hc hcov
  simp only [fullFirstCopyChanges, fullCopyChanges, Memcpy.clobbers,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    have hr := RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
      (a := 8) (b := 0) (len := 704) (count := 8)
      (by decide) (by decide) (.inr (by decide)) offset ho j hj
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.sub_add_cancel] at hr
    exact hr he
  · obtain ⟨j, hj, he⟩ := hcov
    have hr := RangeApart.offsets (frameBase initial .sha256 mode true true)
      (a := offset) (b := 240) (len := 1) (count := 200)
      (by omega) (by decide) (by omega) 0 (by decide) j hj
    simp only [BitVec.add_zero] at hr
    exact hr he

theorem full_second_copy_byte {initial s t : RamState} {mode : Mode} {offset : Nat}
    {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hStack : Stack.Valid initial (mode.entry .sha256 true true).minStackBytes)
    (hOut : out.toNat + 200 < 2^32)
    (hApart : (⟨out.toNat, 200⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes))
    (ha : AgreesExcept (fullSecondCopyChanges initial mode out) s t) (ho : offset < 704) :
    t.external[frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset]? =
      s.external[frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset]? := by
  apply ha.byte
  intro c hc hcov
  simp only [fullSecondCopyChanges, Memcpy.clobbers,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    have hr := RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
      (a := 8) (b := 0) (len := 704) (count := 8)
      (by decide) (by decide) (.inr (by decide)) offset ho j hj
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.sub_add_cancel] at hr
    exact hr he
  · obtain ⟨j, hj, he⟩ := hcov
    apply hApart (out + BitVec.ofNat 64 j).toNat (Memcpy.range_contains (Nat.le_of_lt hOut) hj)
    rw [← he]
    apply frameAddress_contains hStack (by
      rw [Mode.stackBudget mode .sha256 true true]; omega)
    rcases hm with rfl | rfl <;> exact ho

theorem full_copy_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    (mode : Mode) {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xc9)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hTemp : s.regValue .r13 = tempPointer initial .sha256 mode true true)
    (ho : (Operand.mem (frameBase initial .sha256 mode true true + 16) : Operand 64).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, 200⟩)
    (hMember : (⟨out.toNat, 200⟩ : MemoryRegion) ∈ writeRegions initial .sha256 mode true true)
    (hApart : (⟨out.toNat, 200⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes)) :
    ∃ t, Advances (returnBoundary initial)
        (9 + Memcpy.memcpy200Steps (frameBase initial .sha256 mode true true + 240) +
          Memcpy.memcpy200Steps out) s t ∧
      Invariant initial .sha256 mode t true true ∧ t.RIP = comparePC .sha256 mode true true ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      (∀ i < 200, t.external[out + BitVec.ofNat 64 i]? =
        s.external[tempPointer initial .sha256 mode true true + BitVec.ofNat 64 i]?) ∧
      (∀ offset < 704, offset < 240 ∨ 440 ≤ offset →
        t.external[frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset]? =
          s.external[frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset]?) ∧
      AgreesExcept (fullFirstCopyChanges initial mode ++ fullSecondCopyChanges initial mode out) s t := by
  obtain ⟨a, ha, ia, ipa, spa, ta, bytesa, aga⟩ :=
    full_first_copy_steps hstride mode hm hCall inv hp hs hTemp
  have oa : (Operand.mem (frameBase initial .sha256 mode true true + 16) : Operand 64).read a = out := by
    refine Eq.trans ?_ ho
    apply memLoad_congr
    intro j hj
    simp only [memByte, PhysicalMemory.read]
    rw [BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    rw [full_first_copy_byte (offset := 16 + j) aga (by omega) (Or.inl (by omega))]
  obtain ⟨t, ht, it, ipt, spt, bytest, agt⟩ :=
    full_second_copy_steps hstride mode hm hCall ia ipa spa oa ta hOut hMember hApart
  refine ⟨t, ?_, it, ipt, spt, fun i hi ↦ (bytest i hi).trans (bytesa i hi),
    fun offset hb ha ↦ (full_second_copy_byte hm hCall.stackAvailable hOut.2.1 hApart agt hb).trans
      (full_first_copy_byte aga hb ha), aga.trans agt⟩
  have run := ha.trans ht
  have hcount : (5 + Memcpy.memcpy200Steps (frameBase initial .sha256 mode true true + 240)) +
      (4 + Memcpy.memcpy200Steps out) =
      9 + Memcpy.memcpy200Steps (frameBase initial .sha256 mode true true + 240) +
        Memcpy.memcpy200Steps out := by omega
  rw [hcount] at run
  exact run

structure InlineCopyPre (boundary : ReturnBoundary) (p base out : BitVec 64)
    (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = p
  rsp : (Operand.reg 4 : Operand 64).read s = base
  output : (Operand.reg 5 : Operand 64).read s = out
  stackRead : ∀ offset n, offset + n ≤ tempOffset v + v.digestBytes →
    MemReadable s (base + BitVec.ofNat 64 offset) n
  outputRead : ∀ offset n, offset + n ≤ v.digestBytes →
    MemReadable s (out + BitVec.ofNat 64 offset) n
  stackAvoid : ∀ offset < tempOffset v + v.digestBytes,
    ¬ (InProgram (base + BitVec.ofNat 64 offset) ∨ InPageTables (base + BitVec.ofNat 64 offset))
  outputAvoid : ∀ offset < v.digestBytes,
    ¬ (InProgram (out + BitVec.ofNat 64 offset) ∨ InPageTables (out + BitVec.ofNat 64 offset))
  apart : RangeApart out v.digestBytes base (tempOffset v + v.digestBytes)
  boundary : ∀ offset ≤ (copyBytes v).length, p + BitVec.ofNat 64 offset ≠ boundary.rip

namespace InlineCopyPre

variable {boundary : ReturnBoundary} {p base out : BitVec 64} {v : Variant} {s : RamState}
    (h : InlineCopyPre boundary p base out v s)

include h

theorem stack_tables (offset n : Nat) (hr : offset + n ≤ tempOffset v + v.digestBytes) :
    ∀ i < n, ¬ InPageTables (base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact fun ht ↦ h.stackAvoid (offset + i) (by omega) (.inr ht)

theorem output_tables (offset n : Nat) (hr : offset + n ≤ v.digestBytes) :
    ∀ i < n, ¬ InPageTables (out + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact fun ht ↦ h.outputAvoid (offset + i) (by omega) (.inr ht)

theorem stack_store_avoids (offset : Nat) {n : Nat} (value : BitVec n) (next : BitVec 64)
    (hr : offset + n / 8 ≤ tempOffset v + v.digestBytes) :
    (Effect.mk next [⟨(Operand.mem (base + BitVec.ofNat 64 offset) : Operand n), value⟩] none).Avoids
      Extracted.programImage := by
  intro x hx c hc
  simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rintro ⟨i, hi, he⟩
    apply h.stackAvoid (offset + i) (by omega)
    left
    refine ⟨x.2, ?_⟩
    have hh : base + BitVec.ofNat 64 (offset + i) = x.1 := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
    rw [hh]
    exact hx
  · exact id

theorem output_store_avoids (offset : Nat) {n : Nat} (value : BitVec n) (next : BitVec 64)
    (hr : offset + n / 8 ≤ v.digestBytes) :
    (Effect.mk next [⟨(Operand.mem (out + BitVec.ofNat 64 offset) : Operand n), value⟩] none).Avoids
      Extracted.programImage := by
  intro x hx c hc
  simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rintro ⟨i, hi, he⟩
    apply h.outputAvoid (offset + i) (by omega)
    left
    refine ⟨x.2, ?_⟩
    have hh : out + BitVec.ofNat 64 (offset + i) = x.1 := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
    rw [hh]
    exact hx
  · exact id

theorem load_output_store (memory : Ram) (offset sourceOffset : BitVec 64)
    {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : offset.toNat + n / 8 ≤ v.digestBytes)
    (hsource : sourceOffset.toNat + width / 8 ≤ tempOffset v + v.digestBytes) :
    memLoad (memStore memory (out + offset) value) (base + sourceOffset) width =
      memLoad memory (base + sourceOffset) width := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi he
  apply h.apart (offset.toNat + i) (by omega) (sourceOffset.toNat + j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc] using he

theorem load_output_store_zero (memory : Ram) (sourceOffset : BitVec 64)
    {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : n / 8 ≤ v.digestBytes)
    (hsource : sourceOffset.toNat + width / 8 ≤ tempOffset v + v.digestBytes) :
    memLoad (memStore memory out value) (base + sourceOffset) width =
      memLoad memory (base + sourceOffset) width := by
  simpa using h.load_output_store memory 0 sourceOffset value width (by simpa using houtput) hsource

end InlineCopyPre

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add
  Finish.Plain.copy224StoreEffect movR32M32LegacyEffect
attribute [local x86_local] Finish.Plain.copy224StoreEffect_local movR32M32LegacyEffect_local


local macro "inline_load " img:term:max step:term:max off:num delta:num width:num endpoint:num : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hsp := hp.rsp
    x86_norm at hsp
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm) (fun _ _ obs => AddrMode.addr_obs obs _ _) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _⟩
    x86_norm [hsp]
    exact hp.stackRead $off ($width / 8) (by decide +kernel)
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte ((($img).slice $delta (by decide +kernel)) x hx).2
  case boundary =>
    intro s t hp he
    x86_norm
    exact hp.boundary $endpoint (by decide +kernel)
  case' k => x86_norm))

local macro "inline_store " img:term:max step:term:max off:num delta:num width:num endpoint:num dest:ident tables:ident avoids:ident : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hsp := hp.rsp
    have hout := hp.output
    x86_norm at hsp hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine StorePreReadable.of_holds he (ho true) (by x86_norm) ?_ ?_
      · x86_norm [hsp, hout]
        simpa only [BitVec.add_zero] using hp.$dest $off ($width / 8) (by decide +kernel)
      · x86_norm [hsp, hout]
        simpa only [BitVec.add_zero, BitVec.add_assoc] using hp.$tables $off ($width / 8) (by decide +kernel)
    · x86_norm [hsp, hout]
      simpa only [BitVec.add_zero] using hp.$avoids $off (n := $width) _ _ (by decide +kernel)
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte ((($img).slice $delta (by decide +kernel)) x hx).2
  case boundary =>
    intro s t hp he
    x86_norm
    exact hp.boundary $endpoint (by decide +kernel)
  case' k => x86_norm))

def inline224Effect (p base out : BitVec 64) (s : RamState) : Effect where
  rip := p + 53
  writes := [
    ⟨(Operand.reg 0 : Operand 64), ((Operand.mem (base + 80) : Operand 32).read s).setWidth 64⟩,
    ⟨(Operand.mem (base + 48) : Operand 32), (Operand.mem (base + 80) : Operand 32).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 32), (Operand.mem (base + 80) : Operand 32).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩]


def inline224PrefixEffect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 38
  writes := [
    ⟨(Operand.reg 0 : Operand 64), ((Operand.mem (base + 80) : Operand 32).read s).setWidth 64⟩,
    ⟨(Operand.mem (base + 48) : Operand 32), (Operand.mem (base + 80) : Operand 32).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩]

attribute [local x86_compose] inline224PrefixEffect

set_option maxHeartbeats 2400000 in
theorem inline224_prefix_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha224)) :
    AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha224)
      Extracted.programImage (Effect.post (inline224PrefixEffect p base out)) := by
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR32M32LegacyEffect p 0 (.sib 4 none 0 (.d8 80))) from (mov_r32_m32_legacy_effect_step p 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (himage x ((codeRange_mem_of_take (by decide +kernel)) x hx)).2
  case pre =>
    intro s hp
    have hsp := hp.rsp
    x86_norm at hsp
    refine ⟨by simpa only [BitVec.add_zero] using hp.rip, ?_⟩
    x86_norm [hsp]
    exact hp.stackRead 80 4 (by decide +kernel)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR32M32LegacyEffect, Effect.components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm
    exact hp.boundary 4 (by decide +kernel)
  case' k => x86_norm
  inline_store himage (show StepEffect _ _ (Finish.Plain.copy224StoreEffect (p + 4) (.sib 4 none 0 (.d8 48))) from (mov_m32_r32_legacy_effect_step_of_readable (p + 4) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)) 48 4 32 8 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 8) 1 (.sib 4 none 0 (.d8 72))) from (mov_r64_m64_effect_step (p + 8) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)) 72 8 64 13
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 13) 1 (.sib 4 none 0 (.d8 40))) from (mov_m64_r64_effect_step_of_readable (p + 13) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)) 40 13 64 18 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 18) 2 (.sib 4 none 0 (.d8 56))) from (mov_r64_m64_effect_step (p + 18) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)) 56 18 64 23
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 23) 6 (.sib 4 none 0 (.d8 64))) from (mov_r64_m64_effect_step (p + 23) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)) 64 23 64 28
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 28) 6 (.sib 4 none 0 (.d8 32))) from (mov_m64_r64_effect_step_of_readable (p + 28) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)) 32 28 64 33 stackRead stack_tables stack_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 33) 2 (.sib 4 none 0 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 33) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)) 24 33 64 38 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline224PrefixEffect]
  · x86_norm [inline224PrefixEffect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external, BitVec.setWidth_setWidth_of_le]
  · intro i; cases i <;> x86_norm [inline224PrefixEffect]
  · x86_norm [inline224PrefixEffect, hsp, hout]

set_option maxHeartbeats 2400000 in
theorem inline224_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha224)) :
    AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha224)
      Extracted.programImage (Effect.post (inline224Effect p base out)) := by
  have hprefix := inline224_prefix_block boundary p base out himage
  suffices h : AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha224)
      Extracted.programImage (Effect.post (inline224PrefixEffect p base out)) →
      AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha224)
        Extracted.programImage (Effect.post (inline224Effect p base out)) from h hprefix
  inline_store himage (show StepEffect _ _ (Finish.Plain.copy224StoreEffect (p + 38) (.base 5 (.d8 24))) from (mov_m32_r32_legacy_effect_step_of_readable (p + 38) 0 (.base 5 (.d8 24)) (by decide +kernel) rfl rfl)) 24 38 32 41 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 41) 1 (.base 5 (.d8 16))) from (mov_m64_r64_effect_step_of_readable (p + 41) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.base 5 (.d8 16)) (by decide +kernel) rfl rfl)) 16 41 64 45 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 45) 6 (.base 5 (.d8 8))) from (mov_m64_r64_effect_step_of_readable (p + 45) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.base 5 (.d8 8)) (by decide +kernel) rfl rfl)) 8 45 64 49 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 49) 2 (.base 5 (.d8 0))) from (mov_m64_r64_effect_step_of_readable (p + 49) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.base 5 (.d8 0)) (by decide +kernel) rfl rfl)) 0 49 64 53 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline224Effect]
  · x86_norm [inline224Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external, BitVec.setWidth_setWidth_of_le]
  · intro i; cases i <;> x86_norm [inline224Effect]
  · x86_norm [inline224Effect, hsp, hout]

def inline256Effect (p base out : BitVec 64) (s : RamState) : Effect where
  rip := p + 56
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩]


def inline256PrefixEffect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 40
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 64) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 56) : Operand 64).read s⟩]

attribute [local x86_compose] inline256PrefixEffect

set_option maxHeartbeats 2400000 in
theorem inline256_prefix_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha256)) :
    AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha256)
      Extracted.programImage (Effect.post (inline256PrefixEffect p base out)) := by
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR64M64Effect p 0 (.sib 4 none 0 (.d8 80))) from (mov_r64_m64_effect_step p 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (himage x ((codeRange_mem_of_take (by decide +kernel)) x hx)).2
  case pre =>
    intro s hp
    have hsp := hp.rsp
    x86_norm at hsp
    refine ⟨by simpa only [BitVec.add_zero] using hp.rip, ?_⟩
    x86_norm [hsp]
    exact hp.stackRead 80 8 (by decide +kernel)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm
    exact hp.boundary 5 (by decide +kernel)
  case' k => x86_norm
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 5) 0 (.sib 4 none 0 (.d8 48))) from (mov_m64_r64_effect_step_of_readable (p + 5) 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)) 48 5 64 10 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 10) 1 (.sib 4 none 0 (.d8 72))) from (mov_r64_m64_effect_step (p + 10) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)) 72 10 64 15
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 15) 1 (.sib 4 none 0 (.d8 40))) from (mov_m64_r64_effect_step_of_readable (p + 15) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)) 40 15 64 20 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 20) 2 (.sib 4 none 0 (.d8 56))) from (mov_r64_m64_effect_step (p + 20) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)) 56 20 64 25
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 25) 6 (.sib 4 none 0 (.d8 64))) from (mov_r64_m64_effect_step (p + 25) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)) 64 25 64 30
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 30) 6 (.sib 4 none 0 (.d8 32))) from (mov_m64_r64_effect_step_of_readable (p + 30) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)) 32 30 64 35 stackRead stack_tables stack_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 35) 2 (.sib 4 none 0 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 35) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)) 24 35 64 40 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline256PrefixEffect]
  · x86_norm [inline256PrefixEffect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external, BitVec.setWidth_setWidth_of_le]
  · intro i; cases i <;> x86_norm [inline256PrefixEffect]
  · x86_norm [inline256PrefixEffect, hsp, hout]

set_option maxHeartbeats 2400000 in
theorem inline256_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha256)) :
    AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha256)
      Extracted.programImage (Effect.post (inline256Effect p base out)) := by
  have hprefix := inline256_prefix_block boundary p base out himage
  suffices h : AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha256)
      Extracted.programImage (Effect.post (inline256PrefixEffect p base out)) →
      AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha256)
        Extracted.programImage (Effect.post (inline256Effect p base out)) from h hprefix
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 40) 0 (.base 5 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 40) 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.base 5 (.d8 24)) (by decide +kernel) rfl rfl)) 24 40 64 44 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 44) 1 (.base 5 (.d8 16))) from (mov_m64_r64_effect_step_of_readable (p + 44) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.base 5 (.d8 16)) (by decide +kernel) rfl rfl)) 16 44 64 48 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 48) 6 (.base 5 (.d8 8))) from (mov_m64_r64_effect_step_of_readable (p + 48) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.base 5 (.d8 8)) (by decide +kernel) rfl rfl)) 8 48 64 52 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 52) 2 (.base 5 (.d8 0))) from (mov_m64_r64_effect_step_of_readable (p + 52) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.base 5 (.d8 0)) (by decide +kernel) rfl rfl)) 0 52 64 56 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline256Effect]
  · x86_norm [inline256Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external, BitVec.setWidth_setWidth_of_le]
  · intro i; cases i <;> x86_norm [inline256Effect]
  · x86_norm [inline256Effect, hsp, hout]

def inline384Effect (p base out : BitVec 64) (s : RamState) : Effect where
  rip := p + 84
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩]

def inline512Effect (p base out : BitVec 64) (s : RamState) : Effect where
  rip := p + 121
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 80) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 72) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 9 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.reg 10 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 56) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 48) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩]


namespace InlineCopyPre

variable {boundary : ReturnBoundary} {p base out : BitVec 64} {v : Variant} {s : RamState}
    (h : InlineCopyPre boundary p base out v s)

include h

theorem byte_of_load_eq {t : RamState}
    (hgrows : ∀ address : BitVec 64, (s.external[address]?).isSome → (t.external[address]?).isSome)
    (offset width : Nat) (hr : offset + width / 8 ≤ v.digestBytes)
    (hload : memLoad t.external (out + BitVec.ofNat 64 offset) width =
      memLoad s.external (base + BitVec.ofNat 64 (tempOffset v + offset)) width)
    (i : Nat) (hi : i < width / 8) :
    t.external[out + BitVec.ofNat 64 (offset + i)]? =
      s.external[base + BitVec.ofNat 64 (tempOffset v + offset + i)]? := by
  have hall := h.outputRead 0 v.digestBytes (by omega)
  simp only [BitVec.add_zero] at hall
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (hgrows _ (hall.mem (offset + i) (by omega)))
  have hsrc := h.stackRead 0 (tempOffset v + v.digestBytes) (by omega)
  simp only [BitVec.add_zero] at hsrc
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
    (hsrc.mem (tempOffset v + offset + i) (by omega))
  have hh := memByte_of_memLoad_eq hload i hi
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at hh
  change (t.external[out + BitVec.ofNat 64 (offset + i)]?).getD 0 =
    (s.external[base + BitVec.ofNat 64 (tempOffset v + offset + i)]?).getD 0 at hh
  rw [hb, hc] at hh
  rw [hb, hc]
  exact congrArg some hh

end InlineCopyPre

theorem inline224_output {boundary : ReturnBoundary} {p base out : BitVec 64} {s t : RamState}
    (hp : InlineCopyPre boundary p base out .sha224 s)
    (he : (inline224Effect p base out s).Holds s t) :
    ∀ i < Variant.sha224.digestBytes,
      t.external[out + BitVec.ofNat 64 i]? =
        s.external[base + BitVec.ofNat 64 (tempOffset .sha224 + i)]? := by
  have hall := Write.allHold_iff.mp he.writes
  have hword0 : memLoad t.external (out + 0) 64 =
      memLoad s.external (base + 56) 64 := by
    have hh := hall ⟨(Operand.mem (out + 0) : Operand 64),
      (Operand.mem (base + 56) : Operand 64).read s⟩ (by simp [inline224Effect])
    exact hh
  have hword8 : memLoad t.external (out + 8) 64 =
      memLoad s.external (base + 64) 64 := by
    have hh := hall ⟨(Operand.mem (out + 8) : Operand 64),
      (Operand.mem (base + 64) : Operand 64).read s⟩ (by simp [inline224Effect])
    exact hh
  have hword16 : memLoad t.external (out + 16) 64 =
      memLoad s.external (base + 72) 64 := by
    have hh := hall ⟨(Operand.mem (out + 16) : Operand 64),
      (Operand.mem (base + 72) : Operand 64).read s⟩ (by simp [inline224Effect])
    exact hh
  have hword24 : memLoad t.external (out + 24) 32 =
      memLoad s.external (base + 80) 32 := by
    have hh := hall ⟨(Operand.mem (out + 24) : Operand 32),
      (Operand.mem (base + 80) : Operand 32).read s⟩ (by simp [inline224Effect])
    exact hh
  intro i hi
  by_cases hcut0 : i < 8
  · have hh := hp.byte_of_load_eq he.agrees.grow 0 64 (by decide +kernel)
      hword0 (i - 0) (by change i < 28 at hi; omega)
    simpa only [show 0 + (i - 0) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut1 : i < 16
  · have hh := hp.byte_of_load_eq he.agrees.grow 8 64 (by decide +kernel)
      hword8 (i - 8) (by change i < 28 at hi; omega)
    simpa only [show 8 + (i - 8) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut2 : i < 24
  · have hh := hp.byte_of_load_eq he.agrees.grow 16 64 (by decide +kernel)
      hword16 (i - 16) (by change i < 28 at hi; omega)
    simpa only [show 16 + (i - 16) = i by omega,
      Nat.add_assoc] using hh
  have hh := hp.byte_of_load_eq he.agrees.grow 24 32 (by decide +kernel)
      hword24 (i - 24) (by change i < 28 at hi; omega)
  simpa only [show 24 + (i - 24) = i by omega,
      Nat.add_assoc] using hh

theorem inline256_output {boundary : ReturnBoundary} {p base out : BitVec 64} {s t : RamState}
    (hp : InlineCopyPre boundary p base out .sha256 s)
    (he : (inline256Effect p base out s).Holds s t) :
    ∀ i < Variant.sha256.digestBytes,
      t.external[out + BitVec.ofNat 64 i]? =
        s.external[base + BitVec.ofNat 64 (tempOffset .sha256 + i)]? := by
  have hall := Write.allHold_iff.mp he.writes
  have hword0 : memLoad t.external (out + 0) 64 =
      memLoad s.external (base + 56) 64 := by
    have hh := hall ⟨(Operand.mem (out + 0) : Operand 64),
      (Operand.mem (base + 56) : Operand 64).read s⟩ (by simp [inline256Effect])
    exact hh
  have hword8 : memLoad t.external (out + 8) 64 =
      memLoad s.external (base + 64) 64 := by
    have hh := hall ⟨(Operand.mem (out + 8) : Operand 64),
      (Operand.mem (base + 64) : Operand 64).read s⟩ (by simp [inline256Effect])
    exact hh
  have hword16 : memLoad t.external (out + 16) 64 =
      memLoad s.external (base + 72) 64 := by
    have hh := hall ⟨(Operand.mem (out + 16) : Operand 64),
      (Operand.mem (base + 72) : Operand 64).read s⟩ (by simp [inline256Effect])
    exact hh
  have hword24 : memLoad t.external (out + 24) 64 =
      memLoad s.external (base + 80) 64 := by
    have hh := hall ⟨(Operand.mem (out + 24) : Operand 64),
      (Operand.mem (base + 80) : Operand 64).read s⟩ (by simp [inline256Effect])
    exact hh
  intro i hi
  by_cases hcut0 : i < 8
  · have hh := hp.byte_of_load_eq he.agrees.grow 0 64 (by decide +kernel)
      hword0 (i - 0) (by change i < 32 at hi; omega)
    simpa only [show 0 + (i - 0) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut1 : i < 16
  · have hh := hp.byte_of_load_eq he.agrees.grow 8 64 (by decide +kernel)
      hword8 (i - 8) (by change i < 32 at hi; omega)
    simpa only [show 8 + (i - 8) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut2 : i < 24
  · have hh := hp.byte_of_load_eq he.agrees.grow 16 64 (by decide +kernel)
      hword16 (i - 16) (by change i < 32 at hi; omega)
    simpa only [show 16 + (i - 16) = i by omega,
      Nat.add_assoc] using hh
  have hh := hp.byte_of_load_eq he.agrees.grow 24 64 (by decide +kernel)
      hword24 (i - 24) (by change i < 32 at hi; omega)
  simpa only [show 24 + (i - 24) = i by omega,
      Nat.add_assoc] using hh

theorem inline384_output {boundary : ReturnBoundary} {p base out : BitVec 64} {s t : RamState}
    (hp : InlineCopyPre boundary p base out .sha384 s)
    (he : (inline384Effect p base out s).Holds s t) :
    ∀ i < Variant.sha384.digestBytes,
      t.external[out + BitVec.ofNat 64 i]? =
        s.external[base + BitVec.ofNat 64 (tempOffset .sha384 + i)]? := by
  have hall := Write.allHold_iff.mp he.writes
  have hword0 : memLoad t.external (out + 0) 64 =
      memLoad s.external (base + 72) 64 := by
    have hh := hall ⟨(Operand.mem (out + 0) : Operand 64),
      (Operand.mem (base + 72) : Operand 64).read s⟩ (by simp [inline384Effect])
    exact hh
  have hword8 : memLoad t.external (out + 8) 64 =
      memLoad s.external (base + 80) 64 := by
    have hh := hall ⟨(Operand.mem (out + 8) : Operand 64),
      (Operand.mem (base + 80) : Operand 64).read s⟩ (by simp [inline384Effect])
    exact hh
  have hword16 : memLoad t.external (out + 16) 64 =
      memLoad s.external (base + 88) 64 := by
    have hh := hall ⟨(Operand.mem (out + 16) : Operand 64),
      (Operand.mem (base + 88) : Operand 64).read s⟩ (by simp [inline384Effect])
    exact hh
  have hword24 : memLoad t.external (out + 24) 64 =
      memLoad s.external (base + 96) 64 := by
    have hh := hall ⟨(Operand.mem (out + 24) : Operand 64),
      (Operand.mem (base + 96) : Operand 64).read s⟩ (by simp [inline384Effect])
    exact hh
  have hword32 : memLoad t.external (out + 32) 64 =
      memLoad s.external (base + 104) 64 := by
    have hh := hall ⟨(Operand.mem (out + 32) : Operand 64),
      (Operand.mem (base + 104) : Operand 64).read s⟩ (by simp [inline384Effect])
    exact hh
  have hword40 : memLoad t.external (out + 40) 64 =
      memLoad s.external (base + 112) 64 := by
    have hh := hall ⟨(Operand.mem (out + 40) : Operand 64),
      (Operand.mem (base + 112) : Operand 64).read s⟩ (by simp [inline384Effect])
    exact hh
  intro i hi
  by_cases hcut0 : i < 8
  · have hh := hp.byte_of_load_eq he.agrees.grow 0 64 (by decide +kernel)
      hword0 (i - 0) (by change i < 48 at hi; omega)
    simpa only [show 0 + (i - 0) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut1 : i < 16
  · have hh := hp.byte_of_load_eq he.agrees.grow 8 64 (by decide +kernel)
      hword8 (i - 8) (by change i < 48 at hi; omega)
    simpa only [show 8 + (i - 8) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut2 : i < 24
  · have hh := hp.byte_of_load_eq he.agrees.grow 16 64 (by decide +kernel)
      hword16 (i - 16) (by change i < 48 at hi; omega)
    simpa only [show 16 + (i - 16) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut3 : i < 32
  · have hh := hp.byte_of_load_eq he.agrees.grow 24 64 (by decide +kernel)
      hword24 (i - 24) (by change i < 48 at hi; omega)
    simpa only [show 24 + (i - 24) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut4 : i < 40
  · have hh := hp.byte_of_load_eq he.agrees.grow 32 64 (by decide +kernel)
      hword32 (i - 32) (by change i < 48 at hi; omega)
    simpa only [show 32 + (i - 32) = i by omega,
      Nat.add_assoc] using hh
  have hh := hp.byte_of_load_eq he.agrees.grow 40 64 (by decide +kernel)
      hword40 (i - 40) (by change i < 48 at hi; omega)
  simpa only [show 40 + (i - 40) = i by omega,
      Nat.add_assoc] using hh

theorem inline512_output {boundary : ReturnBoundary} {p base out : BitVec 64} {s t : RamState}
    (hp : InlineCopyPre boundary p base out .sha512 s)
    (he : (inline512Effect p base out s).Holds s t) :
    ∀ i < Variant.sha512.digestBytes,
      t.external[out + BitVec.ofNat 64 i]? =
        s.external[base + BitVec.ofNat 64 (tempOffset .sha512 + i)]? := by
  have hall := Write.allHold_iff.mp he.writes
  have hword0 : memLoad t.external (out + 0) 64 =
      memLoad s.external (base + 88) 64 := by
    have hh := hall ⟨(Operand.mem (out + 0) : Operand 64),
      (Operand.mem (base + 88) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword8 : memLoad t.external (out + 8) 64 =
      memLoad s.external (base + 96) 64 := by
    have hh := hall ⟨(Operand.mem (out + 8) : Operand 64),
      (Operand.mem (base + 96) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword16 : memLoad t.external (out + 16) 64 =
      memLoad s.external (base + 104) 64 := by
    have hh := hall ⟨(Operand.mem (out + 16) : Operand 64),
      (Operand.mem (base + 104) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword24 : memLoad t.external (out + 24) 64 =
      memLoad s.external (base + 112) 64 := by
    have hh := hall ⟨(Operand.mem (out + 24) : Operand 64),
      (Operand.mem (base + 112) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword32 : memLoad t.external (out + 32) 64 =
      memLoad s.external (base + 120) 64 := by
    have hh := hall ⟨(Operand.mem (out + 32) : Operand 64),
      (Operand.mem (base + 120) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword40 : memLoad t.external (out + 40) 64 =
      memLoad s.external (base + 128) 64 := by
    have hh := hall ⟨(Operand.mem (out + 40) : Operand 64),
      (Operand.mem (base + 128) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword48 : memLoad t.external (out + 48) 64 =
      memLoad s.external (base + 136) 64 := by
    have hh := hall ⟨(Operand.mem (out + 48) : Operand 64),
      (Operand.mem (base + 136) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  have hword56 : memLoad t.external (out + 56) 64 =
      memLoad s.external (base + 144) 64 := by
    have hh := hall ⟨(Operand.mem (out + 56) : Operand 64),
      (Operand.mem (base + 144) : Operand 64).read s⟩ (by simp [inline512Effect])
    exact hh
  intro i hi
  by_cases hcut0 : i < 8
  · have hh := hp.byte_of_load_eq he.agrees.grow 0 64 (by decide +kernel)
      hword0 (i - 0) (by change i < 64 at hi; omega)
    simpa only [show 0 + (i - 0) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut1 : i < 16
  · have hh := hp.byte_of_load_eq he.agrees.grow 8 64 (by decide +kernel)
      hword8 (i - 8) (by change i < 64 at hi; omega)
    simpa only [show 8 + (i - 8) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut2 : i < 24
  · have hh := hp.byte_of_load_eq he.agrees.grow 16 64 (by decide +kernel)
      hword16 (i - 16) (by change i < 64 at hi; omega)
    simpa only [show 16 + (i - 16) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut3 : i < 32
  · have hh := hp.byte_of_load_eq he.agrees.grow 24 64 (by decide +kernel)
      hword24 (i - 24) (by change i < 64 at hi; omega)
    simpa only [show 24 + (i - 24) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut4 : i < 40
  · have hh := hp.byte_of_load_eq he.agrees.grow 32 64 (by decide +kernel)
      hword32 (i - 32) (by change i < 64 at hi; omega)
    simpa only [show 32 + (i - 32) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut5 : i < 48
  · have hh := hp.byte_of_load_eq he.agrees.grow 40 64 (by decide +kernel)
      hword40 (i - 40) (by change i < 64 at hi; omega)
    simpa only [show 40 + (i - 40) = i by omega,
      Nat.add_assoc] using hh
  by_cases hcut6 : i < 56
  · have hh := hp.byte_of_load_eq he.agrees.grow 48 64 (by decide +kernel)
      hword48 (i - 48) (by change i < 64 at hi; omega)
    simpa only [show 48 + (i - 48) = i by omega,
      Nat.add_assoc] using hh
  have hh := hp.byte_of_load_eq he.agrees.grow 56 64 (by decide +kernel)
      hword56 (i - 56) (by change i < 64 at hi; omega)
  simpa only [show 56 + (i - 56) = i by omega,
      Nat.add_assoc] using hh

def inlineSteps (v : Variant) : Nat :=
  match v with | .sha224 | .sha256 => 12 | .sha384 => 18 | .sha512 => 24

def inlineEffect (v : Variant) (p base out : BitVec 64) : RamState → Effect :=
  match v with
  | .sha224 => inline224Effect p base out
  | .sha256 => inline256Effect p base out
  | .sha384 => inline384Effect p base out
  | .sha512 => inline512Effect p base out

theorem inline_output {boundary : ReturnBoundary} {p base out : BitVec 64} {v : Variant}
    {s t : RamState} (hp : InlineCopyPre boundary p base out v s)
    (he : (inlineEffect v p base out s).Holds s t) :
    ∀ i < v.digestBytes, t.external[out + BitVec.ofNat 64 i]? =
      s.external[base + BitVec.ofNat 64 (tempOffset v + i)]? := by
  cases v with
  | sha224 => exact inline224_output hp he
  | sha256 => exact inline256_output hp he
  | sha384 => exact inline384_output hp he
  | sha512 => exact inline512_output hp he

def inlineChanges (base out : BitVec 64) (v : Variant) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .rip,
    .mem (base + 24) v.digestBytes, .mem out v.digestBytes]

theorem inline_stack_cover {base address : BitVec 64} {offset count total : Nat}
    (hl : 24 ≤ offset) (hh : offset + count ≤ 24 + total)
    (h : (Component.mem (base + BitVec.ofNat 64 offset) count).Covers address) :
    (Component.mem (base + 24) total).Covers address := by
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨offset - 24 + i, by omega, ?_⟩
  change base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
    base + BitVec.ofNat 64 24 + BitVec.ofNat 64 (offset - 24 + i)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show offset + i = 24 + (offset - 24 + i) by omega]

theorem inline_output_cover {out address : BitVec 64} {offset count total : Nat}
    (hh : offset + count ≤ total)
    (h : (Component.mem (out + BitVec.ofNat 64 offset) count).Covers address) :
    (Component.mem out total).Covers address := by
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨offset + i, by omega, ?_⟩
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem inline_agrees {v : Variant} {p base out : BitVec 64} {s t : RamState}
    (he : (inlineEffect v p base out s).Holds s t) :
    AgreesExcept (inlineChanges base out v) s t := by
  apply he.agrees.widen
  · intro c hc hn
    cases v with
    | sha224 =>
      simp only [inlineEffect, inline224Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Component.isMem, Bool.true_eq_false] at hn
      all_goals simp [inlineChanges]
    | sha256 =>
      simp only [inlineEffect, inline256Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Component.isMem, Bool.true_eq_false] at hn
      all_goals simp [inlineChanges]
    | sha384 =>
      simp only [inlineEffect, inline384Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Component.isMem, Bool.true_eq_false] at hn
      all_goals simp [inlineChanges]
    | sha512 =>
      simp only [inlineEffect, inline512Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Component.isMem, Bool.true_eq_false] at hn
      all_goals simp [inlineChanges]
  · intro x c hc hx
    cases v with
    | sha224 =>
      simp only [inlineEffect, inline224Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 48) (count := 4) (total := Variant.sha224.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 40) (count := 8) (total := Variant.sha224.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 32) (count := 8) (total := Variant.sha224.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem (base + 24) Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 24) (count := 8) (total := Variant.sha224.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 24) (count := 4) (total := Variant.sha224.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 16) (count := 8) (total := Variant.sha224.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 8) (count := 8) (total := Variant.sha224.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha224.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 0) (count := 8) (total := Variant.sha224.digestBytes)
          (by decide +kernel) hx
      · exact hx.elim
    | sha256 =>
      simp only [inlineEffect, inline256Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 48) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 40) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 32) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem (base + 24) Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 24) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 24) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 16) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 8) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha256.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 0) (count := 8) (total := Variant.sha256.digestBytes)
          (by decide +kernel) hx
      · exact hx.elim
    | sha384 =>
      simp only [inlineEffect, inline384Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 64) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 56) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 48) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 40) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 32) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem (base + 24) Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 24) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 40) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 32) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 24) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 16) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 8) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha384.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 0) (count := 8) (total := Variant.sha384.digestBytes)
          (by decide +kernel) hx
      · exact hx.elim
    | sha512 =>
      simp only [inlineEffect, inline512Effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 80) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 72) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 64) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 56) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 48) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 40) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · exact hx.elim
      · exact hx.elim
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 32) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem (base + 24) Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_stack_cover (offset := 24) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 56) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 48) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 40) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 32) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 24) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 16) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 8) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · refine ⟨.mem out Variant.sha512.digestBytes, by simp [inlineChanges], ?_⟩
        exact inline_output_cover (offset := 0) (count := 8) (total := Variant.sha512.digestBytes)
          (by decide +kernel) hx
      · exact hx.elim

def inline384Prefix4Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 20
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩]

attribute [local x86_compose] inline384Prefix4Effect

set_option maxHeartbeats 1000000 in
theorem inline384_prefix4_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha384)) :
    AdvanceTriple boundary 4 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix4Effect p base out)) := by
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR64M64Effect p 0 (.sib 4 none 0 (.d8 112))) from (mov_r64_m64_effect_step p 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (himage x ((codeRange_mem_of_take (by decide +kernel)) x hx)).2
  case pre =>
    intro s hp
    have hsp := hp.rsp
    x86_norm at hsp
    refine ⟨by simpa only [BitVec.add_zero] using hp.rip, ?_⟩
    x86_norm [hsp]
    exact hp.stackRead 112 8 (by decide +kernel)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm
    exact hp.boundary 5 (by decide +kernel)
  case' k => x86_norm
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 5) 0 (.sib 4 none 0 (.d8 64))) from (mov_m64_r64_effect_step_of_readable (p + 5) 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)) 64 5 64 10 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 10) 1 (.sib 4 none 0 (.d8 104))) from (mov_r64_m64_effect_step (p + 10) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)) 104 10 64 15
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 15) 1 (.sib 4 none 0 (.d8 56))) from (mov_m64_r64_effect_step_of_readable (p + 15) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)) 56 15 64 20 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline384Prefix4Effect]
  · x86_norm [inline384Prefix4Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline384Prefix4Effect]
  · x86_norm [inline384Prefix4Effect, hsp, hout]

def inline384Prefix8Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 40
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩]

attribute [local x86_compose] inline384Prefix8Effect

set_option maxHeartbeats 1000000 in
theorem inline384_prefix8_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha384)) :
    AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix8Effect p base out)) := by
  have hprefix := inline384_prefix4_block boundary p base out himage
  suffices h : AdvanceTriple boundary 4 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix4Effect p base out)) →
      AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha384)
        Extracted.programImage (Effect.post (inline384Prefix8Effect p base out)) from h hprefix
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 20) 2 (.sib 4 none 0 (.d8 96))) from (mov_r64_m64_effect_step (p + 20) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)) 96 20 64 25
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 25) 2 (.sib 4 none 0 (.d8 48))) from (mov_m64_r64_effect_step_of_readable (p + 25) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)) 48 25 64 30 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 30) 6 (.sib 4 none 0 (.d8 88))) from (mov_r64_m64_effect_step (p + 30) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)) 88 30 64 35
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 35) 6 (.sib 4 none 0 (.d8 40))) from (mov_m64_r64_effect_step_of_readable (p + 35) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)) 40 35 64 40 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline384Prefix8Effect]
  · x86_norm [inline384Prefix8Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline384Prefix8Effect]
  · x86_norm [inline384Prefix8Effect, hsp, hout]

def inline384Prefix12Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 60
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩]

attribute [local x86_compose] inline384Prefix12Effect

set_option maxHeartbeats 1000000 in
theorem inline384_prefix12_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha384)) :
    AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix12Effect p base out)) := by
  have hprefix := inline384_prefix8_block boundary p base out himage
  suffices h : AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix8Effect p base out)) →
      AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha384)
        Extracted.programImage (Effect.post (inline384Prefix12Effect p base out)) from h hprefix
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 40) 7 (.sib 4 none 0 (.d8 72))) from (mov_r64_m64_effect_step (p + 40) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)) 72 40 64 45
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 45) 8 (.sib 4 none 0 (.d8 80))) from (mov_r64_m64_effect_step (p + 45) 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)) 80 45 64 50
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 50) 8 (.sib 4 none 0 (.d8 32))) from (mov_m64_r64_effect_step_of_readable (p + 50) 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)) 32 50 64 55 stackRead stack_tables stack_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 55) 7 (.sib 4 none 0 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 55) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)) 24 55 64 60 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline384Prefix12Effect]
  · x86_norm [inline384Prefix12Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline384Prefix12Effect]
  · x86_norm [inline384Prefix12Effect, hsp, hout]

def inline384Prefix16Effect (p base out : BitVec 64) (s : RamState) : Effect where
  rip := p + 76
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 80) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 72) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩]

attribute [local x86_compose] inline384Prefix16Effect

set_option maxHeartbeats 1000000 in
theorem inline384_prefix16_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha384)) :
    AdvanceTriple boundary 16 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix16Effect p base out)) := by
  have hprefix := inline384_prefix12_block boundary p base out himage
  suffices h : AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix12Effect p base out)) →
      AdvanceTriple boundary 16 (InlineCopyPre boundary p base out .sha384)
        Extracted.programImage (Effect.post (inline384Prefix16Effect p base out)) from h hprefix
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 60) 0 (.base 5 (.d8 40))) from (mov_m64_r64_effect_step_of_readable (p + 60) 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.base 5 (.d8 40)) (by decide +kernel) rfl rfl)) 40 60 64 64 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 64) 1 (.base 5 (.d8 32))) from (mov_m64_r64_effect_step_of_readable (p + 64) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.base 5 (.d8 32)) (by decide +kernel) rfl rfl)) 32 64 64 68 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 68) 2 (.base 5 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 68) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.base 5 (.d8 24)) (by decide +kernel) rfl rfl)) 24 68 64 72 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 72) 6 (.base 5 (.d8 16))) from (mov_m64_r64_effect_step_of_readable (p + 72) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.base 5 (.d8 16)) (by decide +kernel) rfl rfl)) 16 72 64 76 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline384Prefix16Effect]
  · x86_norm [inline384Prefix16Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline384Prefix16Effect]
  · x86_norm [inline384Prefix16Effect, hsp, hout]

attribute [local x86_compose] inline384Effect

set_option maxHeartbeats 1000000 in
theorem inline384_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha384)) :
    AdvanceTriple boundary 18 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Effect p base out)) := by
  have hprefix := inline384_prefix16_block boundary p base out himage
  suffices h : AdvanceTriple boundary 16 (InlineCopyPre boundary p base out .sha384)
      Extracted.programImage (Effect.post (inline384Prefix16Effect p base out)) →
      AdvanceTriple boundary 18 (InlineCopyPre boundary p base out .sha384)
        Extracted.programImage (Effect.post (inline384Effect p base out)) from h hprefix
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 76) 8 (.base 5 (.d8 8))) from (mov_m64_r64_effect_step_of_readable (p + 76) 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.base 5 (.d8 8)) (by decide +kernel) rfl rfl)) 8 76 64 80 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 80) 7 (.base 5 (.d8 0))) from (mov_m64_r64_effect_step_of_readable (p + 80) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.base 5 (.d8 0)) (by decide +kernel) rfl rfl)) 0 80 64 84 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline384Effect]
  · x86_norm [inline384Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline384Effect]
  · x86_norm [inline384Effect, hsp, hout]

def inline512Prefix4Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 26
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 80) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 72) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩]

attribute [local x86_compose] inline512Prefix4Effect

set_option maxHeartbeats 1000000 in
theorem inline512_prefix4_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha512)) :
    AdvanceTriple boundary 4 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix4Effect p base out)) := by
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR64M64Effect p 0 (.sib 4 none 0 (.d32 144))) from (mov_r64_m64_effect_step p 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (himage x ((codeRange_mem_of_take (by decide +kernel)) x hx)).2
  case pre =>
    intro s hp
    have hsp := hp.rsp
    x86_norm at hsp
    refine ⟨by simpa only [BitVec.add_zero] using hp.rip, ?_⟩
    x86_norm [hsp]
    exact hp.stackRead 144 8 (by decide +kernel)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm
    exact hp.boundary 8 (by decide +kernel)
  case' k => x86_norm
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 8) 0 (.sib 4 none 0 (.d8 80))) from (mov_m64_r64_effect_step_of_readable (p + 8) 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)) 80 8 64 13 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 13) 1 (.sib 4 none 0 (.d32 136))) from (mov_r64_m64_effect_step (p + 13) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)) 136 13 64 21
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 21) 1 (.sib 4 none 0 (.d8 72))) from (mov_m64_r64_effect_step_of_readable (p + 21) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)) 72 21 64 26 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline512Prefix4Effect]
  · x86_norm [inline512Prefix4Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline512Prefix4Effect]
  · x86_norm [inline512Prefix4Effect, hsp, hout]

def inline512Prefix8Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 49
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 80) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 72) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩]

attribute [local x86_compose] inline512Prefix8Effect

set_option maxHeartbeats 1000000 in
theorem inline512_prefix8_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha512)) :
    AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix8Effect p base out)) := by
  have hprefix := inline512_prefix4_block boundary p base out himage
  suffices h : AdvanceTriple boundary 4 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix4Effect p base out)) →
      AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha512)
        Extracted.programImage (Effect.post (inline512Prefix8Effect p base out)) from h hprefix
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 26) 2 (.sib 4 none 0 (.d32 128))) from (mov_r64_m64_effect_step (p + 26) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)) 128 26 64 34
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 34) 2 (.sib 4 none 0 (.d8 64))) from (mov_m64_r64_effect_step_of_readable (p + 34) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)) 64 34 64 39 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 39) 6 (.sib 4 none 0 (.d8 120))) from (mov_r64_m64_effect_step (p + 39) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)) 120 39 64 44
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 44) 6 (.sib 4 none 0 (.d8 56))) from (mov_m64_r64_effect_step_of_readable (p + 44) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)) 56 44 64 49 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline512Prefix8Effect]
  · x86_norm [inline512Prefix8Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline512Prefix8Effect]
  · x86_norm [inline512Prefix8Effect, hsp, hout]

def inline512Prefix12Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 69
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 80) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 72) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩]

attribute [local x86_compose] inline512Prefix12Effect

set_option maxHeartbeats 1000000 in
theorem inline512_prefix12_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha512)) :
    AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix12Effect p base out)) := by
  have hprefix := inline512_prefix8_block boundary p base out himage
  suffices h : AdvanceTriple boundary 8 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix8Effect p base out)) →
      AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha512)
        Extracted.programImage (Effect.post (inline512Prefix12Effect p base out)) from h hprefix
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 49) 7 (.sib 4 none 0 (.d8 112))) from (mov_r64_m64_effect_step (p + 49) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)) 112 49 64 54
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 54) 7 (.sib 4 none 0 (.d8 48))) from (mov_m64_r64_effect_step_of_readable (p + 54) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)) 48 54 64 59 stackRead stack_tables stack_store_avoids
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 59) 8 (.sib 4 none 0 (.d8 104))) from (mov_r64_m64_effect_step (p + 59) 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)) 104 59 64 64
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 64) 8 (.sib 4 none 0 (.d8 40))) from (mov_m64_r64_effect_step_of_readable (p + 64) 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)) 40 64 64 69 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline512Prefix12Effect]
  · x86_norm [inline512Prefix12Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline512Prefix12Effect]
  · x86_norm [inline512Prefix12Effect, hsp, hout]

def inline512Prefix16Effect (p base _out : BitVec 64) (s : RamState) : Effect where
  rip := p + 89
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 80) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 72) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 9 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.reg 10 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩]

attribute [local x86_compose] inline512Prefix16Effect

set_option maxHeartbeats 1000000 in
theorem inline512_prefix16_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha512)) :
    AdvanceTriple boundary 16 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix16Effect p base out)) := by
  have hprefix := inline512_prefix12_block boundary p base out himage
  suffices h : AdvanceTriple boundary 12 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix12Effect p base out)) →
      AdvanceTriple boundary 16 (InlineCopyPre boundary p base out .sha512)
        Extracted.programImage (Effect.post (inline512Prefix16Effect p base out)) from h hprefix
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 69) 9 (.sib 4 none 0 (.d8 88))) from (mov_r64_m64_effect_step (p + 69) 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)) 88 69 64 74
  inline_load himage (show StepEffect _ _ (movR64M64Effect (p + 74) 10 (.sib 4 none 0 (.d8 96))) from (mov_r64_m64_effect_step (p + 74) 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)) 96 74 64 79
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 79) 10 (.sib 4 none 0 (.d8 32))) from (mov_m64_r64_effect_step_of_readable (p + 79) 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)) 32 79 64 84 stackRead stack_tables stack_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 84) 9 (.sib 4 none 0 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 84) 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)) 24 84 64 89 stackRead stack_tables stack_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline512Prefix16Effect]
  · x86_norm [inline512Prefix16Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline512Prefix16Effect]
  · x86_norm [inline512Prefix16Effect, hsp, hout]

def inline512Prefix20Effect (p base out : BitVec 64) (s : RamState) : Effect where
  rip := p + 105
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 80) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 72) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + 112) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + 104) : Operand 64).read s⟩,
    ⟨(Operand.reg 9 : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.reg 10 : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 32) : Operand 64), (Operand.mem (base + 96) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 24) : Operand 64), (Operand.mem (base + 88) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 56) : Operand 64), (Operand.mem (base + 144) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 48) : Operand 64), (Operand.mem (base + 136) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (base + 128) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (base + 120) : Operand 64).read s⟩]

attribute [local x86_compose] inline512Prefix20Effect

set_option maxHeartbeats 1000000 in
theorem inline512_prefix20_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha512)) :
    AdvanceTriple boundary 20 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix20Effect p base out)) := by
  have hprefix := inline512_prefix16_block boundary p base out himage
  suffices h : AdvanceTriple boundary 16 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix16Effect p base out)) →
      AdvanceTriple boundary 20 (InlineCopyPre boundary p base out .sha512)
        Extracted.programImage (Effect.post (inline512Prefix20Effect p base out)) from h hprefix
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 89) 0 (.base 5 (.d8 56))) from (mov_m64_r64_effect_step_of_readable (p + 89) 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.base 5 (.d8 56)) (by decide +kernel) rfl rfl)) 56 89 64 93 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 93) 1 (.base 5 (.d8 48))) from (mov_m64_r64_effect_step_of_readable (p + 93) 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.base 5 (.d8 48)) (by decide +kernel) rfl rfl)) 48 93 64 97 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 97) 2 (.base 5 (.d8 40))) from (mov_m64_r64_effect_step_of_readable (p + 97) 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.base 5 (.d8 40)) (by decide +kernel) rfl rfl)) 40 97 64 101 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 101) 6 (.base 5 (.d8 32))) from (mov_m64_r64_effect_step_of_readable (p + 101) 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.base 5 (.d8 32)) (by decide +kernel) rfl rfl)) 32 101 64 105 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline512Prefix20Effect]
  · x86_norm [inline512Prefix20Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline512Prefix20Effect]
  · x86_norm [inline512Prefix20Effect, hsp, hout]

attribute [local x86_compose] inline512Effect

set_option maxHeartbeats 1000000 in
theorem inline512_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (himage : ImageAt p (copyBytes .sha512)) :
    AdvanceTriple boundary 24 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Effect p base out)) := by
  have hprefix := inline512_prefix20_block boundary p base out himage
  suffices h : AdvanceTriple boundary 20 (InlineCopyPre boundary p base out .sha512)
      Extracted.programImage (Effect.post (inline512Prefix20Effect p base out)) →
      AdvanceTriple boundary 24 (InlineCopyPre boundary p base out .sha512)
        Extracted.programImage (Effect.post (inline512Effect p base out)) from h hprefix
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 105) 7 (.base 5 (.d8 24))) from (mov_m64_r64_effect_step_of_readable (p + 105) 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.base 5 (.d8 24)) (by decide +kernel) rfl rfl)) 24 105 64 109 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 109) 8 (.base 5 (.d8 16))) from (mov_m64_r64_effect_step_of_readable (p + 109) 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.base 5 (.d8 16)) (by decide +kernel) rfl rfl)) 16 109 64 113 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 113) 10 (.base 5 (.d8 8))) from (mov_m64_r64_effect_step_of_readable (p + 113) 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.base 5 (.d8 8)) (by decide +kernel) rfl rfl)) 8 113 64 117 outputRead output_tables output_store_avoids
  inline_store himage (show StepEffect _ _ (movM64R64Effect (p + 117) 9 (.base 5 (.d8 0))) from (mov_m64_r64_effect_step_of_readable (p + 117) 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.base 5 (.d8 0)) (by decide +kernel) rfl rfl)) 0 117 64 121 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp := hp.rsp
  have hout := hp.output
  x86_norm at hsp hout
  apply he.weaken
  · x86_norm [inline512Effect]
  · x86_norm [inline512Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [inline512Effect]
  · x86_norm [inline512Effect, hsp, hout]


theorem inline_block [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (v : Variant) (himage : ImageAt p (copyBytes v)) :
    AdvanceTriple boundary (inlineSteps v) (InlineCopyPre boundary p base out v)
      Extracted.programImage (Effect.post (inlineEffect v p base out)) := by
  cases v with
  | sha224 => exact inline224_block boundary p base out himage
  | sha256 => exact inline256_block boundary p base out himage
  | sha384 => exact inline384_block boundary p base out himage
  | sha512 => exact inline512_block boundary p base out himage


theorem inline_copy_steps [Bindings] (boundary : ReturnBoundary) (p base out : BitVec 64)
    (v : Variant) (himage : ImageAt p (copyBytes v)) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hp : InlineCopyPre boundary p base out v s) :
    ∃ t, Advances boundary (inlineSteps v) s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = p + BitVec.ofNat 64 (copyBytes v).length ∧
      (∀ i < v.digestBytes, t.external[out + BitVec.ofNat 64 i]? =
        s.external[base + BitVec.ofNat 64 (tempOffset v + i)]?) ∧
      AgreesExcept (inlineChanges base out v) s t ∧ CalleeSavedRegistersUnchanged s t := by
  obtain ⟨t, ht, hr, hc, he⟩ := inline_block boundary p base out v himage s hready hcode hp
  have ag := inline_agrees he
  refine ⟨t, ht, hr, hc, he.rip.trans ?_, inline_output hp he, ag, ?_⟩
  · cases v <;> rfl
  · apply calleeSavedRegistersUnchanged_of_agreesExcept ag
    intro r hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [inlineChanges] <;> decide +kernel

theorem inline_pre [bindings : Bindings] (v : Variant) (mode : Mode)
    {keccak : Bool} {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak false)
    (inv : Invariant initial v mode s keccak false)
    (hp : s.RIP = callPC v mode keccak false + (5 : BitVec 64))
    (hs : stackPtr s = frameBase initial v mode keccak false)
    (ho : s.regValue .rbp = out)
    (hOut : ValidOutput initial ⟨out.toNat, v.digestBytes⟩)
    (hMember : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak false)
    (hApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak false).minStackBytes)) :
    InlineCopyPre (returnBoundary initial) (callPC v mode keccak false + 5)
      (frameBase initial v mode keccak false) out v s := by
  have budget : mode.frameSize v keccak false ≤ (mode.entry v keccak false).minStackBytes := by
    rw [Mode.stackBudget mode v keccak false]; omega
  have hSize : tempOffset v + v.digestBytes ≤ mode.frameSize v keccak false + 8 := by
    rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
  have outNat (offset : Nat) (hb : offset ≤ v.digestBytes) :
      (out + BitVec.ofNat 64 offset).toNat = out.toNat + offset := by
    have hlo := hOut.2.1
    change out.toNat + v.digestBytes < 2^32 at hlo
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨hp, hs, ho, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro offset n hn
    exact inv.frameReadable hCall.stackAvailable (by omega)
  · intro offset n hn
    apply memReadable_of_region hOut.2.1
    · intro address ha
      exact Option.isSome_iff_exists.mp
        (inv.grows address (Option.isSome_iff_exists.mpr (hOut.2.2 address ha)))
    · rw [outNat offset (by omega)]; dsimp only [MemoryRegion.start, MemoryRegion.size]; omega
    · rw [outNat offset (by omega)]; dsimp only [MemoryRegion.start, MemoryRegion.size]; omega
  · intro offset hn
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak false) _
      (frameAddress_contains hCall.stackAvailable budget (by omega))
  · intro offset hn
    apply writeRegions_avoid hCall _ hMember
    exact Memcpy.range_contains (Nat.le_of_lt hOut.2.1) hn
  · intro i hi j hj he
    apply hApart (out + BitVec.ofNat 64 i).toNat (Memcpy.range_contains (Nat.le_of_lt hOut.2.1) hi)
    rw [he]
    exact frameAddress_contains hCall.stackAvailable budget (by omega)
  · intro offset hn he
    obtain ⟨address, hw, _, hOutside⟩ := hCall.returnAddress
    have hret := returnBoundary_rip_of_word64At hw
    have hprogram : InProgram (callPC v mode keccak false + 5 + BitVec.ofNat 64 offset) := by
      apply Permutation.inProgram_permutation_address
      · have h : ∀ i : Fin ((copyBytes v).length + 1),
            0x100000 ≤ (callPC v mode keccak false + 5 + BitVec.ofNat 64 i.val).toNat := by
          rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
        exact h ⟨offset, by omega⟩
      · have h : ∀ i : Fin ((copyBytes v).length + 1),
            (callPC v mode keccak false + 5 + BitVec.ofNat 64 i.val).toNat ≤ 0x106222 := by
          rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
        exact h ⟨offset, by omega⟩
    exact hOutside ((he.trans hret) ▸ hprogram)

theorem inline_writes {initial : RamState} {mode : Mode} {v : Variant} {keccak : Bool} {out : BitVec 64}
    {regions : Vector MemoryRegion n}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hStack : Stack.Valid initial (mode.entry v keccak false).minStackBytes)
    (hOut : out.toNat + v.digestBytes < 2^32)
    (hStackMember : Stack.region initial (mode.entry v keccak false).minStackBytes ∈ regions)
    (hMember : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion) ∈ regions) :
    WritesWithin (inlineChanges (frameBase initial v mode keccak false) out v)
      regions := by
  intro c hc address hcov
  simp only [inlineChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcov.elim
  · obtain ⟨i, hi, rfl⟩ := hcov
    refine ⟨_, hStackMember, ?_⟩
    rw [BitVec.add_assoc, show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
    apply frameAddress_contains hStack (by rw [Mode.stackBudget mode v keccak false]; omega)
    have hb : 24 + v.digestBytes ≤ mode.frameSize v keccak false + 8 := by
      rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
    omega
  · obtain ⟨i, hi, rfl⟩ := hcov
    exact ⟨_, hMember, Memcpy.range_contains (Nat.le_of_lt hOut) hi⟩

theorem inline_byte {initial s t : RamState} {mode : Mode} {v : Variant} {keccak : Bool}
    {offset : Nat} {out : BitVec 64}
    (hStack : Stack.Valid initial (mode.entry v keccak false).minStackBytes)
    (hOut : out.toNat + v.digestBytes < 2^32)
    (hApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak false).minStackBytes))
    (ha : AgreesExcept (inlineChanges (frameBase initial v mode keccak false) out v) s t)
    (ho : offset < mode.frameSize v keccak false + 8)
    (haway : offset < 24 ∨ 24 + v.digestBytes ≤ offset) :
    t.external[frameBase initial v mode keccak false + BitVec.ofNat 64 offset]? =
      s.external[frameBase initial v mode keccak false + BitVec.ofNat 64 offset]? := by
  apply ha.byte
  intro c hc hcov
  simp only [inlineChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    have hb : mode.frameSize v keccak false + 8 < 2^64 := by
      cases mode <;> cases v <;> cases keccak <;> decide +kernel
    have hd : 24 + v.digestBytes < 2^64 := by cases v <;> decide +kernel
    have hr := RangeApart.offsets (frameBase initial v mode keccak false)
      (a := offset) (b := 24) (len := 1) (count := v.digestBytes)
      (by omega) (by omega) (by omega) 0 (by decide) j hj
    simp only [BitVec.add_zero] at hr
    exact hr he
  · obtain ⟨j, hj, he⟩ := hcov
    apply hApart (out + BitVec.ofNat 64 j).toNat (Memcpy.range_contains (Nat.le_of_lt hOut) hj)
    rw [← he]
    exact frameAddress_contains hStack (by rw [Mode.stackBudget mode v keccak false]; omega) ho


theorem saved_of_frame_bytes {initial s t : RamState} {v : Variant} {mode : Mode}
    {keccak fullState : Bool}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (saved : SavedFrame initial s mode fullState)
    (hbytes : ∀ offset, mode.frameSize v keccak fullState - 48 ≤ offset →
      offset < mode.frameSize v keccak fullState + 8 →
      t.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset]? =
        s.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset]?) :
    SavedFrame initial t mode fullState := by
  have hn : mode.pushCount fullState = 6 := by rcases hm with rfl | rfl <;> rfl
  have hb : frameBase initial v mode keccak fullState +
      BitVec.ofNat 64 (mode.frameSize v keccak fullState - 48) = initial.regValue .rsp - 48 := by
    unfold frameBase
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    congr 1
    rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  have hsize : 48 ≤ mode.frameSize v keccak fullState := by
    rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  have keep (i : Fin 7) :
      (Operand.mem (initial.regValue .rsp - 48 + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read t =
        (Operand.mem (initial.regValue .rsp - 48 + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s := by
    apply memLoad_congr
    intro j hj
    simp only [memByte, PhysicalMemory.read]
    have h := hbytes (mode.frameSize v keccak fullState - 48 + 8 * i.val + j)
      (by omega) (by have := i.isLt; omega)
    rw [BitVec.ofNat_add, BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc, hb] at h
    rw [h]
  refine ⟨?_, ?_⟩
  · intro i
    have hi : i.val < 6 := by have := i.isLt; omega
    have he := keep ⟨i.val, by omega⟩
    have hs := saved.saved i
    simp only [Mode.savedBytes, hn] at hs ⊢
    exact he.trans hs
  · have he := keep ⟨6, by decide⟩
    simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel] at he
    exact he.trans saved.returnSlot


theorem inline_wrapper_steps [bindings : Bindings] (v : Variant) (mode : Mode)
    {keccak : Bool} {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak false)
    (inv : Invariant initial v mode s keccak false)
    (hp : s.RIP = callPC v mode keccak false + (5 : BitVec 64))
    (ho : s.regValue .rbp = out)
    (hs : stackPtr s = frameBase initial v mode keccak false)
    (saved : SavedFrame initial s mode false)
    (hOut : ValidOutput initial ⟨out.toNat, v.digestBytes⟩)
    (hMember : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak false)
    (hApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak false).minStackBytes)) :
    ∃ t, Advances (returnBoundary initial) (inlineSteps v) s t ∧
      Invariant initial v mode t keccak false ∧ SavedFrame initial t mode false ∧
      t.RIP = comparePC v mode keccak false ∧ stackPtr t = frameBase initial v mode keccak false ∧
      (∀ i < v.digestBytes, t.external[out + BitVec.ofNat 64 i]? =
        s.external[tempPointer initial v mode keccak false + BitVec.ofNat 64 i]?) ∧
      (∀ offset < mode.frameSize v keccak false + 8, offset < 24 ∨ 24 + v.digestBytes ≤ offset →
        t.external[frameBase initial v mode keccak false + BitVec.ofNat 64 offset]? =
          s.external[frameBase initial v mode keccak false + BitVec.ofNat 64 offset]?) ∧
      AgreesExcept (inlineChanges (frameBase initial v mode keccak false) out v) s t ∧
      CalleeSavedRegistersUnchanged s t := by
  have pre := inline_pre v mode hm hCall inv hp hs ho hOut hMember hApart
  obtain ⟨t, ht, hr, _, hip, hbytes, ag, callee⟩ := inline_copy_steps (returnBoundary initial)
    (callPC v mode keccak false + 5) (frameBase initial v mode keccak false) out v
    (copy_image v mode keccak hm) s inv.ready inv.code pre
  have it := inv.of_agreesExcept hCall hr ag (hd := by simp [inlineChanges]) (inline_writes hm hCall.stackAvailable hOut.2.1
    (stack_mem_writeRegions initial v mode keccak false) hMember)
  have keep (offset : Nat) := inline_byte (offset := offset) hCall.stackAvailable hOut.2.1 hApart ag
  have st : SavedFrame initial t mode false := by
    apply saved_of_frame_bytes (v := v) (keccak := keccak) hm saved
    intro offset hlo hhi
    apply keep offset hhi
    right
    have hb : 24 + v.digestBytes ≤ mode.frameSize v keccak false - 48 := by
      rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
    omega
  refine ⟨t, ht, it, st, hip.trans ?_, ?_, ?_, fun offset hb ha ↦ keep offset hb ha, ag, callee⟩
  · rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
  · exact (ag.read (r := 4) (n := 64) (by simp [inlineChanges])).trans hs
  · intro i hi
    simpa only [tempPointer, BitVec.ofNat_add, BitVec.add_assoc] using hbytes i hi


theorem full_copy_writes {initial : RamState} {mode : Mode} {out : BitVec 64}
    {regions : Vector MemoryRegion n}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hStack : Stack.Valid initial (mode.entry .sha256 true true).minStackBytes)
    (hOut : out.toNat + 200 < 2^32)
    (hStackMember : Stack.region initial (mode.entry .sha256 true true).minStackBytes ∈ regions)
    (hMember : (⟨out.toNat, 200⟩ : MemoryRegion) ∈ regions) :
    WritesWithin (fullFirstCopyChanges initial mode ++ fullSecondCopyChanges initial mode out) regions := by
  have hf : mode.frameSize .sha256 true true = 696 := by
    rcases hm with rfl | rfl <;> rfl
  have hframe : frameBase initial .sha256 mode true true - 8 = initial.regValue .rsp - 704 := by
    rw [frameBase, hf, BitVec.sub_sub]
    rfl
  have pushCover (i : Nat) (hi : i < 8) :
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).Contains
        (frameBase initial .sha256 mode true true - 8 + BitVec.ofNat 64 i).toNat := by
    rw [hframe]
    exact stack_sub_contains hStack (by
      rw [Mode.stackBudget mode .sha256 true true, hf]; decide +kernel) (by change i < (704 : Nat); omega)
  intro c hc address hcov
  simp only [fullFirstCopyChanges, fullSecondCopyChanges, fullCopyChanges, Memcpy.clobbers,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
    (((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) <;>
    try exact hcov.elim
  · obtain ⟨i, hi, rfl⟩ := hcov
    exact ⟨_, hStackMember, pushCover i hi⟩
  · obtain ⟨i, hi, rfl⟩ := hcov
    refine ⟨_, hStackMember, ?_⟩
    rw [BitVec.add_assoc, show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl, ← BitVec.ofNat_add]
    apply frameAddress_contains hStack (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    rw [hf]
    omega
  · obtain ⟨i, hi, rfl⟩ := hcov
    exact ⟨_, hStackMember, pushCover i hi⟩
  · obtain ⟨i, hi, rfl⟩ := hcov
    exact ⟨_, hMember, Memcpy.range_contains (Nat.le_of_lt hOut) hi⟩

end Sha3.Proofs.Wrapper.Reset.Output
