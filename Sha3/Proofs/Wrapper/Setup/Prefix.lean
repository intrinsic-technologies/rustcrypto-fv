import Sha3.Proofs.Wrapper.Setup.Basic
import Sha3.Proofs.Stores.Frame
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def setupChanges (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) : List Component :=
  [.reg 3, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15, .reg 7, .reg 2, .reg 6,
    .flags, .rip, .mem (outputSlot initial v mode keccak fullState) 8,
    .mem (frameBase initial v mode keccak fullState + 16) 8]

theorem outputSlot_sub (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) (firstOutput : Bool := false) :
    (if firstOutput then frameBase initial v mode keccak fullState + 16
      else outputSlot initial v mode keccak fullState) = initial.regValue .rsp -
      BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState)) := by
  have hle : (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState) ≤ mode.frameSize v keccak fullState := by
    cases firstOutput <;> cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  have hlt : (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState) < 2^64 := by
    cases firstOutput <;> cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  have heq : (if firstOutput then frameBase initial v mode keccak fullState + 16
      else outputSlot initial v mode keccak fullState) = frameBase initial v mode keccak fullState +
      BitVec.ofNat 64 (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState) := by cases firstOutput <;> rfl
  rw [heq]
  unfold frameBase
  rw [← BitVec.ofNat_sub_ofNat_of_le _ _ hlt hle]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem setupChanges_writes {initial : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes) :
    WritesWithin (setupChanges initial v mode keccak fullState) (writeRegions initial v mode keccak fullState) := by
  have slotWrites (firstOutput : Bool) : WritesWithin
      [.mem (if firstOutput then frameBase initial v mode keccak fullState + 16
        else outputSlot initial v mode keccak fullState) 8]
      (writeRegions initial v mode keccak fullState) := by
    intro c hc address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨Stack.region initial (mode.entry v keccak fullState).minStackBytes,
      stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
    rw [outputSlot_sub initial v mode keccak fullState firstOutput]
    apply stack_sub_contains hStack
    · rw [Mode.stackBudget mode v keccak fullState]; omega
    · have hmin : 8 ≤ (mode.frameSize v keccak fullState) - (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState) := by cases firstOutput <;> cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide
      omega
  intro c hc address hcover
  simp only [setupChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · exact slotWrites false _ (by simp) address hcover
  · exact slotWrites true _ (by simp) address hcover

theorem setupAdvance [bindings : Bindings] {initial s model : RamState}
    {v : Variant} {keccak fullState : Bool} {mode : Mode} {inputs : Array Input} {split : Nat}
    {boundary : ReturnBoundary} {p : BitVec 64} {bytes : List UInt8}
    {pre : RamState → Prop} {effect : RamState → Effect}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (full : ∀ t, ∀ w ∈ (effect t).writes, w.Full)
    (localWrites : ∀ a b, Obs a b → (effect a).writes = (effect b).writes)
    (frame : ∀ c ∈ (effect s).components, c ∈ setupChanges initial v mode keccak fullState)
    (inv : Invariant initial v mode s keccak fullState) (sp : s.GPR[4] ≠ boundary.rsp)
    (hp : pre s) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧ (effect s).Holds s t ∧
      Obs (applyWrites model (effect model).writes) t ∧
      AgreesExcept (setupChanges initial v mode keccak fullState) s t := by
  obtain ⟨t, ht, hr, he⟩ := step s inv.ready (image.code inv.loaded) hp
  have ha := he.agrees.mono frame
  have hsp : t.GPR[4] = s.GPR[4] := ha.agree (.reg 4) (by simp [setupChanges]) rfl
  refine ⟨t, Advances.of_step ht (.inr (hsp ▸ sp)),
    inv.of_agreesExcept hCall hr ha (setupChanges_writes hCall.stackAvailable) (by simp [setupChanges]),
    hsp ▸ sp, he, ?_, ha⟩
  rw [localWrites model s obs]
  exact he.obs obs (full s)

theorem setupStorePre [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak fullState : Bool}
    {mode : Mode} {inputs : Array Input} {split : Nat} {p : BitVec 64}
    {address : RamState → BitVec 64}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState) (hp : s.RIP = p)
    (firstOutput : Bool := false)
    (ha : address s = (if firstOutput then frameBase initial v mode keccak fullState + 16
      else outputSlot initial v mode keccak fullState)) : StorePreReadable p address 8 s := by
  have hbudget : (mode.frameSize v keccak fullState) - (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]; omega
  have hmin : 8 ≤ (mode.frameSize v keccak fullState) - (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState) := by cases firstOutput <;> cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide
  have hread : MemReadable s (if firstOutput then frameBase initial v mode keccak fullState + 16
      else outputSlot initial v mode keccak fullState) 8 := by
    rw [outputSlot_sub initial v mode keccak fullState firstOutput]
    refine ⟨?_, ?_⟩
    · have hlow := stack_sub_low hCall.stackAvailable hbudget
      change (initial.regValue .rsp -
        BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState))).toNat +
          ((mode.frameSize v keccak fullState) - (if firstOutput then 16 else mode.outputSlotOffset v keccak fullState)) < 2^32 at hlow
      omega
    · intro i hi
      exact inv.grows _ (Option.isSome_iff_exists.mpr
        (stack_sub_allocated hCall.stackAvailable hbudget (by omega)))
  refine ⟨⟨hp, ha ▸ hread⟩, ?_⟩
  intro i hi addressTable
  rw [ha] at addressTable
  apply writeRegions_avoid hCall (Stack.region initial (mode.entry v keccak fullState).minStackBytes)
    (stack_mem_writeRegions initial v mode keccak fullState) _ _ (.inr addressTable)
  rw [outputSlot_sub initial v mode keccak fullState firstOutput]
  exact stack_sub_contains hCall.stackAvailable hbudget (by omega)

def plainStateAddr (v : Variant) (_keccak : Bool := false) (fullState : Bool := false) : AddrMode :=
  match fullState with
  | true => .sib 4 none 0 (.d8 8)
  | false => .sib 4 none 0 (match v with
      | .sha224 | .sha256 => .d8 72
      | .sha384 => .d8 104
      | .sha512 => .d32 136)

def plainSetupTail (v : Variant) (fullState : Bool := false) : Nat :=
  if fullState then 18 else match v with
  | .sha512 => 22
  | _ => 19

def resetSetupBytes : List UInt8 :=
  [0x4d, 0x89, 0xc5, 0x48, 0x89, 0xc, 0x24, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc, 0x48, 0x8d, 0x7c, 0x24, 0x8, 0x31, 0xdb, 0xba, 0xc9, 0x0, 0x0, 0x0, 0x31, 0xf6]

def finalizeResetStored (mode : Mode) (fullState : Bool) : Bool :=
  match mode with
  | .finalizeFixedReset | .digestFinalizeReset => fullState
  | _ => false

def finalizeResetSwapped (v : Variant) (mode : Mode) (fullState : Bool := false) : Bool :=
  if finalizeResetStored mode fullState then true else
  match mode, v with
  | .finalizeFixedReset, .sha384 | .finalizeFixedReset, .sha512
  | .digestFinalizeReset, .sha384 | .digestFinalizeReset, .sha512 => true
  | _, _ => false

def finalizeResetSetupBytes (stateAddr : AddrMode := .sib 4 none 0 (.d8 24))
    (swapped : Bool := false) (stored : Bool := false) : List UInt8 :=
  [0x4c, 0x89, 0x4c, 0x24, (if stored then 0x18 else 0x10), (if swapped then 0x4d else 0x4c), 0x89, (if swapped then 0xc5 else 0xc3)] ++
    (if stored then [0x48, 0x89, 0x4c, 0x24, 0x10] else [0x48, 0x89, 0xcd]) ++
    [0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc] ++
    encodeLeaR64M 7 stateAddr ++
    (if swapped then [0x31, 0xdb] else [0x45, 0x31, 0xed]) ++
    [0xba, 0xc9, 0x0, 0x0, 0x0, 0x31, 0xf6]

def plainSetupBytes (v : Variant) (fullState : Bool := false) : List UInt8 :=
  if fullState then [0x48, 0x89, 0x0c, 0x24, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc, 0x48, 0x8d, 0x7c, 0x24, 8, 0xba, 0xc9, 0, 0, 0, 0x31, 0xf6]
  else match v with
  | .sha224 => [0x48, 0x89, 0x4c, 0x24, 0x20, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc, 0x48, 0x8d, 0x7c, 0x24, 0x48, 0xba, 0xc9, 0x0, 0x0, 0x0, 0x31, 0xf6]
  | .sha256 => [0x48, 0x89, 0x4c, 0x24, 0x20, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc, 0x48, 0x8d, 0x7c, 0x24, 0x48, 0xba, 0xc9, 0x0, 0x0, 0x0, 0x31, 0xf6]
  | .sha384 => [0x48, 0x89, 0x4c, 0x24, 0x30, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc, 0x48, 0x8d, 0x7c, 0x24, 0x68, 0xba, 0xc9, 0x0, 0x0, 0x0, 0x31, 0xf6]
  | .sha512 => [0x48, 0x89, 0x4c, 0x24, 0x40, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xf7, 0x49, 0x89, 0xfc, 0x48, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0xba, 0xc9, 0x0, 0x0, 0x0, 0x31, 0xf6]

theorem plain_setup_steps [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary) (p : BitVec 64)
    (hCall : ValidInvocation bindings v .plain initial inputs split keccak fullState)
    (image : ImageAt p (plainSetupBytes v fullState)) (inv : Invariant initial v .plain s keccak fullState)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial v .plain keccak fullState)
    (inside : s.GPR[4] ≠ boundary.rsp)
    (args : ∀ r ∈ [Syntax.Reg.rcx, .rdx, .rsi, .rdi, .r8, .r9],
      s.regValue r = initial.regValue r) :
    ∃ t, Advances boundary 7 s t ∧ Invariant initial v .plain t keccak fullState ∧
      t.RIP = p + BitVec.ofNat 64 (plainSetupTail v fullState + 7) ∧ SetupRegisters initial v .plain t keccak fullState ∧
      SetupArguments initial v .plain t keccak fullState ∧ AgreesExcept (setupChanges initial v .plain keccak fullState) s t := by
  have stack1 : (Operand.reg 4 : Operand 64).read s = frameBase initial v .plain keccak fullState := by
    exact sp
  simp only [BitVec.ofNat_eq_ofNat] at stack1
  obtain ⟨s1, h1, i1, sp1, e1, o1, a1⟩ := setupAdvance
    (effect := movM64R64Effect (p + BitVec.ofNat 64 (0)) 1 (.sib 4 none 0 (if fullState then .none else .d8 (BitVec.ofNat 8 (Mode.outputSlotOffset .plain v))))) hCall
    (mov_m64_r64_effect_step_of_readable (p + BitVec.ofNat 64 (0)) 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (if fullState then .none else .d8 (BitVec.ofNat 8 (Mode.outputSlotOffset .plain v)))) (by cases fullState <;> cases v <;> decide) (by cases fullState <;> cases v <;> decide) (by cases fullState <;> cases v <;> decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (0) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movM64R64Effect, storeEffect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movM64R64Effect, storeEffect, h.read_reg, AddrMode.addr_obs h])
    (by
      intro c hc
      x86_norm [movM64R64Effect] at hc
      rw [stack1] at hc
      rcases hc with rfl | rfl <;> cases fullState <;> cases v <;> simp [setupChanges, outputSlot, Mode.outputSlotOffset])
    inv inside (setupStorePre (firstOutput := false) hCall inv (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ip) (by
      x86_norm [storeAddrAt]
      rw [stack1]
      cases fullState <;> cases v <;> rfl)) (Obs.refl s)
  obtain ⟨s2, h2, i2, sp2, e2, o2, a2⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (5 - if fullState then 1 else 0)) 14 2) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (5 - if fullState then 1 else 0)) 0x49 0xd6 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (5 - if fullState then 1 else 0) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i1 sp1 (by cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e1.rip) o1
  obtain ⟨s3, h3, i3, sp3, e3, o3, a3⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (8 - if fullState then 1 else 0)) 15 6) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (8 - if fullState then 1 else 0)) 0x49 0xf7 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (8 - if fullState then 1 else 0) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i2 sp2 (by cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e2.rip) o2
  obtain ⟨s4, h4, i4, sp4, e4, o4, a4⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (11 - if fullState then 1 else 0)) 12 7) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (11 - if fullState then 1 else 0)) 0x49 0xfc (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (11 - if fullState then 1 else 0) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i3 sp3 (by cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e3.rip) o3
  obtain ⟨s5, h5, i5, sp5, e5, o5, a5⟩ := setupAdvance
    (effect := leaR64Effect (p + BitVec.ofNat 64 (14 - if fullState then 1 else 0)) 7 (plainStateAddr v false fullState)) hCall
    (lea_r64_effect_step (p + BitVec.ofNat 64 (14 - if fullState then 1 else 0)) 0x48 (by unfold RexWPrefix; decide) 7 (plainStateAddr v false fullState) (by cases fullState <;> cases v <;> decide) (by cases fullState <;> cases v <;> decide) (by cases fullState <;> cases v <;> decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (14 - if fullState then 1 else 0) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by
      intro c hc
      simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i4 sp4 (by cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e4.rip) o4
  obtain ⟨s6, h6, i6, sp6, e6, o6, a6⟩ := setupAdvance
    (effect := movR32Imm32Effect (p + BitVec.ofNat 64 (plainSetupTail v fullState)) 5 2 201) hCall
    (mov_r32_imm32_effect_step (p + BitVec.ofNat 64 (plainSetupTail v fullState)) 0xba (by decide) 201)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (plainSetupTail v fullState) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR32Imm32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32Imm32Effect])
    (by
      intro c hc
      simp only [movR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i5 sp5 (by cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e5.rip) o5
  obtain ⟨s7, h7, i7, sp7, e7, o7, a7⟩ := setupAdvance
    (effect := xorR32R32Effect (p + BitVec.ofNat 64 (plainSetupTail v fullState + 5)) 2 6 6) hCall
    (xor_r32_r32_effect_step (p + BitVec.ofNat 64 (plainSetupTail v fullState + 5)) 0xf6 (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (plainSetupTail v fullState + 5) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by
      intro c hc
      simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [setupChanges])
    i6 sp6 (by cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e6.rip) o6
  have hs := (o7.read (Operand.reg 4 : Operand 64) trivial).symm
  have hd := (o7.read (Operand.reg 7 : Operand 64) trivial).symm
  have hl := (o7.read (Operand.reg 2 : Operand 64) trivial).symm
  have hv := (o7.read (Operand.reg 6 : Operand 64) trivial).symm
  have hp := (o7.read (Operand.reg 12 : Operand 64) trivial).symm
  have hn := (o7.read (Operand.reg 14 : Operand 64) trivial).symm
  have hc := (o7.read (Operand.reg 15 : Operand 64) trivial).symm
  have hb := (o7.read (Operand.reg 3 : Operand 64) trivial).symm
  have h13 := (o7.read (Operand.reg 13 : Operand 64) trivial).symm
  have hz := (o7.read (Operand.reg 5 : Operand 64) trivial).symm
  have ho := (o7.read (Operand.mem (outputSlot initial v .plain keccak fullState) : Operand 64) trivial).symm
  x86_norm [movM64R64Effect, movR64R64Effect, leaR64Effect,
    movR32Imm32Effect, xorR32R32Effect, BitVec.xor_self, plainStateAddr] at hs hd hl hv hp hn hc hb h13 hz ho
  change (Operand.reg 4 : Operand 64).read s = frameBase initial v .plain keccak fullState at sp
  simp only [BitVec.ofNat_eq_ofNat] at sp
  rw [sp] at hs ho
  have hout : (Operand.mem (outputSlot initial v .plain keccak fullState) : Operand 64).read s7 = initial.regValue .rcx := by
    cases fullState <;> cases v <;> simp only [outputSlot, Mode.outputSlotOffset, BitVec.reduceSignExtend, Bool.false_eq_true, reduceIte, BitVec.add_zero] at ho ⊢ <;>
      rw [memLoad_memStore _ _ (by decide) (by decide)] at ho <;>
      exact ho.trans (args .rcx (by simp))
  refine ⟨s7, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7)))))), i7, ?_, ⟨hs, ?_, hl, hv⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · cases fullState <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, Bool.false_eq_true, reduceIte, Nat.reduceSub] using e7.rip
  · cases fullState <;> cases v <;> x86_norm at hd <;> rw [sp] at hd <;> exact hd
  · exact hp.trans (args .rdi (by simp))
  · exact hn.trans (args .rdx (by simp))
  · exact hc.trans (args .rsi (by simp))
  · exact hout
  · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7))))))).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

theorem reset_setup_steps [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary) (p : BitVec 64)
    (hCall : ValidInvocation bindings v .reset initial inputs split keccak fullState)
    (image : ImageAt p (resetSetupBytes)) (inv : Invariant initial v .reset s keccak fullState)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial v .reset keccak fullState)
    (inside : s.GPR[4] ≠ boundary.rsp)
    (args : ∀ r ∈ [Syntax.Reg.rcx, .rdx, .rsi, .rdi, .r8, .r9],
      s.regValue r = initial.regValue r) :
    ∃ t, Advances boundary 9 s t ∧ Invariant initial v .reset t keccak fullState ∧
      t.RIP = p + (30 : BitVec 64) ∧ SetupRegisters initial v .reset t keccak fullState ∧
      SetupArguments initial v .reset t keccak fullState ∧ AgreesExcept (setupChanges initial v .reset keccak fullState) s t := by
  obtain ⟨s1, h1, i1, sp1, e1, o1, a1⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (0)) 13 8) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (0)) 0x4d 0xc5 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (0) (by cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    inv inside (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ip) (Obs.refl s)
  have stack2 : (Operand.reg 4 : Operand 64).read s1 = frameBase initial v .reset keccak fullState := by
    have he := (o1.read (Operand.reg 4 : Operand 64) trivial).symm
    x86_norm [movR64R64Effect] at he
    exact he.trans sp
  simp only [BitVec.ofNat_eq_ofNat] at stack2
  obtain ⟨s2, h2, i2, sp2, e2, o2, a2⟩ := setupAdvance
    (effect := movM64R64Effect (p + BitVec.ofNat 64 (3)) 1 (.sib 4 none 0 .none)) hCall
    (mov_m64_r64_effect_step_of_readable (p + BitVec.ofNat 64 (3)) 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (3) (by cases v <;> decide +kernel))
    (by intro t; simp [movM64R64Effect, storeEffect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movM64R64Effect, storeEffect, h.read_reg, AddrMode.addr_obs h])
    (by
      intro c hc
      x86_norm [movM64R64Effect] at hc
      rw [stack2] at hc
      rcases hc with rfl | rfl <;> cases v <;> simp [setupChanges, outputSlot, Mode.outputSlotOffset])
    i1 sp1 (setupStorePre (firstOutput := false) hCall i1 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e1.rip) (by
      x86_norm [storeAddrAt]
      rw [stack2]
      cases v <;> rfl)) o1
  obtain ⟨s3, h3, i3, sp3, e3, o3, a3⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (7)) 14 2) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (7)) 0x49 0xd6 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (7) (by cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i2 sp2 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e2.rip) o2
  obtain ⟨s4, h4, i4, sp4, e4, o4, a4⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (10)) 15 6) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (10)) 0x49 0xf7 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (10) (by cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i3 sp3 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e3.rip) o3
  obtain ⟨s5, h5, i5, sp5, e5, o5, a5⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (13)) 12 7) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (13)) 0x49 0xfc (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (13) (by cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i4 sp4 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e4.rip) o4
  obtain ⟨s6, h6, i6, sp6, e6, o6, a6⟩ := setupAdvance
    (effect := leaR64Effect (p + BitVec.ofNat 64 (16)) 7 (.sib 4 none 0 (.d8 8))) hCall
    (lea_r64_effect_step (p + BitVec.ofNat 64 (16)) 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (16) (by cases v <;> decide +kernel))
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by
      intro c hc
      simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i5 sp5 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e5.rip) o5
  obtain ⟨s7, h7, i7, sp7, e7, o7, a7⟩ := setupAdvance
    (effect := xorR32R32Effect (p + BitVec.ofNat 64 (21)) 2 3 3) hCall
    (xor_r32_r32_effect_step (p + BitVec.ofNat 64 (21)) 0xdb (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (21) (by cases v <;> decide +kernel))
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by
      intro c hc
      simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [setupChanges])
    i6 sp6 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e6.rip) o6
  obtain ⟨s8, h8, i8, sp8, e8, o8, a8⟩ := setupAdvance
    (effect := movR32Imm32Effect (p + BitVec.ofNat 64 (23)) 5 2 201) hCall
    (mov_r32_imm32_effect_step (p + BitVec.ofNat 64 (23)) 0xba (by decide) 201)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (23) (by cases v <;> decide +kernel))
    (by intro t; simp [movR32Imm32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32Imm32Effect])
    (by
      intro c hc
      simp only [movR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i7 sp7 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e7.rip) o7
  obtain ⟨s9, h9, i9, sp9, e9, o9, a9⟩ := setupAdvance
    (effect := xorR32R32Effect (p + BitVec.ofNat 64 (28)) 2 6 6) hCall
    (xor_r32_r32_effect_step (p + BitVec.ofNat 64 (28)) 0xf6 (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (28) (by cases v <;> decide +kernel))
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by
      intro c hc
      simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [setupChanges])
    i8 sp8 (by cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e8.rip) o8
  have hs := (o9.read (Operand.reg 4 : Operand 64) trivial).symm
  have hd := (o9.read (Operand.reg 7 : Operand 64) trivial).symm
  have hl := (o9.read (Operand.reg 2 : Operand 64) trivial).symm
  have hv := (o9.read (Operand.reg 6 : Operand 64) trivial).symm
  have hp := (o9.read (Operand.reg 12 : Operand 64) trivial).symm
  have hn := (o9.read (Operand.reg 14 : Operand 64) trivial).symm
  have hc := (o9.read (Operand.reg 15 : Operand 64) trivial).symm
  have hb := (o9.read (Operand.reg 3 : Operand 64) trivial).symm
  have h13 := (o9.read (Operand.reg 13 : Operand 64) trivial).symm
  have hz := (o9.read (Operand.reg 5 : Operand 64) trivial).symm
  have ho := (o9.read (Operand.mem (outputSlot initial v .reset keccak fullState) : Operand 64) trivial).symm
  x86_norm [movM64R64Effect, movR64R64Effect, leaR64Effect,
    movR32Imm32Effect, xorR32R32Effect, BitVec.xor_self, plainStateAddr] at hs hd hl hv hp hn hc hb h13 hz ho
  change (Operand.reg 4 : Operand 64).read s = frameBase initial v .reset keccak fullState at sp
  simp only [BitVec.ofNat_eq_ofNat] at sp
  rw [sp] at hs hd ho
  have hout : (Operand.mem (outputSlot initial v .reset keccak fullState) : Operand 64).read s9 = initial.regValue .rcx := by
    cases v <;> simp only [outputSlot, Mode.outputSlotOffset, BitVec.add_zero] at ho ⊢ <;>
      rw [memLoad_memStore _ _ (by decide) (by decide)] at ho <;>
      exact ho.trans (args .rcx (by simp))
  refine ⟨s9, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))), i9, ?_, ⟨hs, ?_, hl, hv⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr] using e9.rip
  · cases v <;> exact hd
  · exact hp.trans (args .rdi (by simp))
  · exact hn.trans (args .rdx (by simp))
  · exact hc.trans (args .rsi (by simp))
  · exact ⟨h13.trans (args .r8 (by simp)), hb, hout⟩
  · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans (a9))))))))).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

def finalizeResetStateAddr (v : Variant) (mode : Mode) (fullState : Bool := false) : AddrMode :=
  .sib 4 none 0 (match mode with
    | .finalizeFixedReset | .digestFinalizeReset => if fullState then .d8 32 else .d32 (BitVec.ofNat 32 (mode.stateOffset v))
    | _ => .d8 24)

def finalizeResetSetupTail (v : Variant) (mode : Mode) (fullState : Bool := false) : Nat :=
  20 + (if finalizeResetStored mode fullState then 2 else 0) + leaLen (finalizeResetStateAddr v mode fullState)

set_option maxHeartbeats 800000 in
theorem finalizeReset_setup_steps [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary) (p : BitVec 64)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (image : ImageAt p (finalizeResetSetupBytes (finalizeResetStateAddr v mode fullState) (finalizeResetSwapped v mode fullState) (finalizeResetStored mode fullState))) (inv : Invariant initial v mode s keccak fullState)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial v mode keccak fullState)
    (inside : s.GPR[4] ≠ boundary.rsp)
    (args : ∀ r ∈ [Syntax.Reg.rcx, .rdx, .rsi, .rdi, .r8, .r9],
      s.regValue r = initial.regValue r)
    (hmode : mode = .finalizeReset ∨ mode = .digestFinalizeIntoReset ∨
      mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset := by simp) :
    ∃ t, Advances boundary 10 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + BitVec.ofNat 64 (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3) + 7) ∧ SetupRegisters initial v mode t keccak fullState ∧
      SetupArguments initial v mode t keccak fullState ∧ AgreesExcept (setupChanges initial v mode keccak fullState) s t := by
  have stack1 : (Operand.reg 4 : Operand 64).read s = frameBase initial v mode keccak fullState := by
    exact sp
  simp only [BitVec.ofNat_eq_ofNat] at stack1
  obtain ⟨s1, h1, i1, sp1, e1, o1, a1⟩ := setupAdvance
    (effect := movM64R64Effect (p + BitVec.ofNat 64 (0)) 9 (.sib 4 none 0 (.d8 (if finalizeResetStored mode fullState then 24 else 16)))) hCall
    (mov_m64_r64_effect_step_of_readable (p + BitVec.ofNat 64 (0)) 0x4c (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 (if finalizeResetStored mode fullState then 24 else 16))) (by cases hs : finalizeResetStored mode fullState <;> decide) (by cases hs : finalizeResetStored mode fullState <;> decide) (by cases hs : finalizeResetStored mode fullState <;> decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (0) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [movM64R64Effect, storeEffect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movM64R64Effect, storeEffect, h.read_reg, AddrMode.addr_obs h])
    (by
      intro c hc
      x86_norm [movM64R64Effect] at hc
      rw [stack1] at hc
      rcases hc with rfl | rfl <;> cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simp [setupChanges, outputSlot, Mode.outputSlotOffset, finalizeResetStored])
    inv inside (setupStorePre (firstOutput := false) hCall inv (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ip) (by
      x86_norm [storeAddrAt]
      rw [stack1]
      cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> rfl)) (Obs.refl s)
  obtain ⟨s2, h2, i2, sp2, e2, o2, a2⟩ := setupAdvance
    (bytes := if finalizeResetSwapped v mode fullState then [0x4d,0x89,0xc5] else [0x4c,0x89,0xc3])
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (5)) (if finalizeResetSwapped v mode fullState then 13 else 3) 8) hCall
    (by
      cases hswap : finalizeResetSwapped v mode fullState
      · exact mov_r64_r64_effect_step _ 0x4c 0xc3 (by unfold RexWPrefix; decide) (by decide)
      · exact mov_r64_r64_effect_step _ 0x4d 0xc5 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (5) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i1 sp1 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e1.rip) o1
  have stack3 : (Operand.reg 4 : Operand 64).read s2 = frameBase initial v mode keccak fullState := by
    have h := (o2.read (Operand.reg 4 : Operand 64) trivial).symm
    cases hswap : finalizeResetSwapped v mode fullState <;>
      x86_norm [movM64R64Effect, movR64R64Effect, hswap] at h <;> exact h.trans stack1
  simp only [BitVec.ofNat_eq_ofNat] at stack3
  obtain ⟨s3, h3, i3, sp3, e3, o3, a3⟩ := setupAdvance
    (bytes := if finalizeResetStored mode fullState then [0x48,0x89,0x4c,0x24,0x10] else [0x48,0x89,0xcd])
    (pre := if finalizeResetStored mode fullState then StorePreReadable (p + BitVec.ofNat 64 8) (storeAddrAt (p + BitVec.ofNat 64 8) (.sib 4 none 0 (.d8 16)) 5) 8 else fun t => t.RIP = p + BitVec.ofNat 64 8)
    (effect := if finalizeResetStored mode fullState then movM64R64Effect (p + BitVec.ofNat 64 8) 1 (.sib 4 none 0 (.d8 16)) else movR64R64Effect (p + BitVec.ofNat 64 8) 5 1) hCall
    (by
      cases hstored : finalizeResetStored mode fullState
      · exact mov_r64_r64_effect_step _ 0x48 0xcd (by unfold RexWPrefix; decide) (by decide)
      · exact mov_m64_r64_effect_step_of_readable _ 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 16)) (by decide) (by decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat] using image.slice 8 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; cases h : finalizeResetStored mode fullState <;> simp [movM64R64Effect, movR64R64Effect, storeEffect, Write.Full, Operand.Full])
    (by intro a b h; cases hs : finalizeResetStored mode fullState <;> simp only [Bool.false_eq_true, reduceIte, movM64R64Effect, movR64R64Effect, storeEffect, h.read_reg, AddrMode.addr_obs h])
    (by
      intro c hc
      cases hs : finalizeResetStored mode fullState <;> simp only [hs, reduceIte, Bool.false_eq_true] at hc
      · simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges]
      · x86_norm [movM64R64Effect] at hc
        rw [stack3] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
    i2 sp2 (by
      have rip3 : s2.RIP = p + BitVec.ofNat 64 8 := by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e2.rip
      cases hs : finalizeResetStored mode fullState
      · exact rip3
      · exact setupStorePre hCall i2 rip3 (firstOutput := true) (by x86_norm [storeAddrAt]; exact congrArg (· + 16) stack3)) o2
  obtain ⟨s4, h4, i4, sp4, e4, o4, a4⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (11 + if finalizeResetStored mode fullState then 2 else 0)) 14 2) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (11 + if finalizeResetStored mode fullState then 2 else 0)) 0x49 0xd6 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (11 + if finalizeResetStored mode fullState then 2 else 0) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i3 sp3 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e3.rip) o3
  obtain ⟨s5, h5, i5, sp5, e5, o5, a5⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (14 + if finalizeResetStored mode fullState then 2 else 0)) 15 6) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (14 + if finalizeResetStored mode fullState then 2 else 0)) 0x49 0xf7 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (14 + if finalizeResetStored mode fullState then 2 else 0) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i4 sp4 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e4.rip) o4
  obtain ⟨s6, h6, i6, sp6, e6, o6, a6⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (17 + if finalizeResetStored mode fullState then 2 else 0)) 12 7) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (17 + if finalizeResetStored mode fullState then 2 else 0)) 0x49 0xfc (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (17 + if finalizeResetStored mode fullState then 2 else 0) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i5 sp5 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e5.rip) o5
  obtain ⟨s7, h7, i7, sp7, e7, o7, a7⟩ := setupAdvance
    (effect := leaR64Effect (p + BitVec.ofNat 64 (20 + if finalizeResetStored mode fullState then 2 else 0)) 7 (finalizeResetStateAddr v mode fullState)) hCall
    (lea_r64_effect_step (p + BitVec.ofNat 64 (20 + if finalizeResetStored mode fullState then 2 else 0)) 0x48 (by unfold RexWPrefix; decide) 7 (finalizeResetStateAddr v mode fullState) (by cases fullState <;> cases mode <;> cases v <;> decide) (by cases fullState <;> cases mode <;> cases v <;> decide) (by cases fullState <;> cases mode <;> cases v <;> decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (20 + if finalizeResetStored mode fullState then 2 else 0) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by
      intro c hc
      simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i6 sp6 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e6.rip) o6
  obtain ⟨s8, h8, i8, sp8, e8, o8, a8⟩ := setupAdvance
    (bytes := if finalizeResetSwapped v mode fullState then [0x31,0xdb] else [0x45,0x31,0xed])
    (effect := xorR32R32Effect (p + BitVec.ofNat 64 (finalizeResetSetupTail v mode fullState)) (if finalizeResetSwapped v mode fullState then 2 else 3) (if finalizeResetSwapped v mode fullState then 3 else 13) (if finalizeResetSwapped v mode fullState then 3 else 13)) hCall
    (by
      cases hswap : finalizeResetSwapped v mode fullState
      · exact xor_r32_r32_rex_effect_step _ 0x45 0xed (by unfold RexNoWPrefix; decide) (by decide)
      · exact xor_r32_r32_effect_step _ 0xdb (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (finalizeResetSetupTail v mode fullState) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by
      intro c hc
      simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i7 sp7 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e7.rip) o7
  obtain ⟨s9, h9, i9, sp9, e9, o9, a9⟩ := setupAdvance
    (effect := movR32Imm32Effect (p + BitVec.ofNat 64 (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3))) 5 2 201) hCall
    (mov_r32_imm32_effect_step (p + BitVec.ofNat 64 (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3))) 0xba (by decide) 201)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3)) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [movR32Imm32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32Imm32Effect])
    (by
      intro c hc
      simp only [movR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i8 sp8 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e8.rip) o8
  obtain ⟨s10, h10, i10, sp10, e10, o10, a10⟩ := setupAdvance
    (effect := xorR32R32Effect (p + BitVec.ofNat 64 (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3) + 5)) 2 6 6) hCall
    (xor_r32_r32_effect_step (p + BitVec.ofNat 64 (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3) + 5)) 0xf6 (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (finalizeResetSetupTail v mode fullState + (if finalizeResetSwapped v mode fullState then 2 else 3) + 5) (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel))
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by
      intro c hc
      simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> first | solve | simp [setupChanges] | (cases hswap : finalizeResetSwapped v mode fullState <;> simp [setupChanges]))
    i9 sp9 (by cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v <;> simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e9.rip) o9
  have hs := (o10.read (Operand.reg 4 : Operand 64) trivial).symm
  have hd := (o10.read (Operand.reg 7 : Operand 64) trivial).symm
  have hl := (o10.read (Operand.reg 2 : Operand 64) trivial).symm
  have hv := (o10.read (Operand.reg 6 : Operand 64) trivial).symm
  have hp := (o10.read (Operand.reg 12 : Operand 64) trivial).symm
  have hn := (o10.read (Operand.reg 14 : Operand 64) trivial).symm
  have hc := (o10.read (Operand.reg 15 : Operand 64) trivial).symm
  have hb := (o10.read (Operand.reg 3 : Operand 64) trivial).symm
  have h13 := (o10.read (Operand.reg 13 : Operand 64) trivial).symm
  have hz := (o10.read (Operand.reg 5 : Operand 64) trivial).symm
  have hfirst := (o10.read (Operand.mem (frameBase initial v mode keccak fullState + 16) : Operand 64) trivial).symm
  have ho := (o10.read (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64) trivial).symm
  cases fullState <;> rcases hmode with rfl | rfl | rfl | rfl <;> cases v
  all_goals try (have hvalid := (hCall.fullState_valid rfl).1; cases hvalid)
  all_goals
    simp only [finalizeResetSwapped, finalizeResetStored, Bool.false_eq_true, reduceIte] at *
    x86_norm [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte,
      movR32Imm32Effect, xorR32R32Effect, BitVec.xor_self, plainStateAddr, finalizeResetStateAddr] at hs hd hl hv hp hn hc hb h13 hz ho hfirst
    change (Operand.reg 4 : Operand 64).read s = frameBase initial _ _ keccak _ at sp
    simp only [BitVec.ofNat_eq_ofNat] at sp
    rw [sp] at hs hd ho hfirst
    simp only [outputSlot, Mode.outputSlotOffset] at ho
    x86_norm at ho hfirst
    have hout := ho.trans (args .r9 (by simp))
    refine ⟨s10, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10))))))))), i10, ?_, ⟨hs, ?_, hl, hv⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa only [movM64R64Effect, movR64R64Effect, leaR64Effect, finalizeResetStored, Bool.false_eq_true, reduceIte, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, storeEffect, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, plainSetupTail, plainStateAddr, finalizeResetSetupTail, finalizeResetStateAddr, finalizeResetStored, Mode.stateOffset, finalizeResetSwapped, Bool.false_eq_true, reduceIte] using e10.rip
    · exact hd
    · exact hp.trans (args .rdi (by simp))
    · exact hn.trans (args .rdx (by simp))
    · exact hc.trans (args .rsi (by simp))
    · first | exact ⟨hb.trans (args .r8 (by simp)), hz.trans (args .rcx (by simp)), h13, hout⟩ | exact ⟨h13.trans (args .r8 (by simp)), hz.trans (args .rcx (by simp)), hb, hout⟩ | exact ⟨h13.trans (args .r8 (by simp)), hfirst.trans (args .rcx (by simp)), hb, hout⟩
    · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans (a9.trans (a10)))))))))).mono
      intro c hc
      simpa only [List.mem_append, or_self] using hc

end Sha3.Proofs.Wrapper
