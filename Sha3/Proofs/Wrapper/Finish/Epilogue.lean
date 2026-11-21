import Sha3.Proofs.Wrapper.Layout
import Sha3.Proofs.Run
import Sha3.Proofs.X86.Instructions.Add.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def allocation (v : Variant) (mode : Mode) (keccak fullState : Bool := false) : BitVec 32 :=
  BitVec.ofNat 32 (mode.frameSize v keccak fullState - (8 * mode.pushCount fullState))

def epiloguePopReg (mode : Mode) (fullState : Bool) (i : Fin (mode.pushCount fullState)) : BitVec 4 :=
  BitVec.ofNat 4 (mode.savedRegisters fullState)[i].fin.val

def epilogueBytes (v : Variant) (mode : Mode) (keccak fullState : Bool := false) : List UInt8 :=
  [0x48, 0x81, 0xc4] ++ immBytes 32 (allocation v mode keccak fullState) ++
    ((List.finRange (mode.pushCount fullState)).flatMap
      (fun i ↦ encodePopR64 (epiloguePopReg mode fullState i))) ++ [0xc3]

def epilogueCode (v : Variant) (mode : Mode) (p : BitVec 64)
    (keccak fullState : Bool := false) : CodeMap :=
  codeRange p (epilogueBytes v mode keccak fullState)

def epiloguePopOffset (k : Nat) (mode : Mode := .plain) (fullState : Bool := false) : Nat :=
  7 + (((List.finRange (mode.pushCount fullState)).take k).flatMap
    (fun i ↦ encodePopR64 (epiloguePopReg mode fullState i))).length

def epiloguePopPC (p : BitVec 64) (k : Nat)
    (mode : Mode := .plain) (fullState : Bool := false) : BitVec 64 :=
  p + BitVec.ofNat 64 (epiloguePopOffset k mode fullState)

def epilogueSlot (initial : RamState) (k : Nat)
    (mode : Mode := .plain) (fullState : Bool := false) : BitVec 64 :=
  initial.regValue .rsp - BitVec.ofNat 64 ((8 * mode.pushCount fullState)) + BitVec.ofNat 64 (8 * k)

def epilogueChanges : List Component :=
  [.reg 3, .reg 12, .reg 13, .reg 14, .reg 15, .reg 5, .reg 4, .flags, .rip]

structure EpiloguePre (v : Variant) (p : BitVec 64) (initial : RamState) (mode : Mode) (s : RamState)
    (keccak fullState : Bool := false) : Prop where
  rip : s.RIP = p
  stack : stackPtr s = frameBase initial v mode keccak fullState
  saved : SavedFrame initial s mode fullState
  readable : ∀ i : Fin (mode.pushCount fullState + 1), MemReadable s (epilogueSlot initial i.val mode fullState) 8
  target : (stackTop initial).toNat < 2^32
  preserved : ∀ j : Fin 6,
    (∀ i : Fin (mode.pushCount fullState),
      (epiloguePopReg mode fullState i).setWidth 5 ≠ (epiloguePopReg .plain false j).setWidth 5) →
    (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
      initial.regValue savedRegisters[j]

structure EpilogueProgress (p : BitVec 64) (initial start : RamState)
    (k : Nat) (s : RamState) (mode : Mode := .plain) (fullState : Bool := false) : Prop where
  rip : s.RIP = epiloguePopPC p k mode fullState
  stack : stackPtr s = epilogueSlot initial k mode fullState
  memory : s.external = start.external
  agrees : AgreesExcept epilogueChanges start s
  saved : ∀ i : Fin (mode.pushCount fullState), i.val < k →
    (Operand.reg ((epiloguePopReg mode fullState i).setWidth 5) : Operand 64).read s =
      initial.regValue (mode.savedRegisters fullState)[i]

  preserved : ∀ j : Fin 6,
    (∀ i : Fin (mode.pushCount fullState),
      (epiloguePopReg mode fullState i).setWidth 5 ≠ (epiloguePopReg .plain false j).setWidth 5) →
    (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
      initial.regValue savedRegisters[j]

structure EpilogueResult (initial start final : RamState) : Prop where
  rip : final.RIP = stackTop initial
  stack : stackPtr final = stackPtr initial + 8
  memory : final.external = start.external
  agrees : AgreesExcept epilogueChanges start final
  saved : CalleeSavedRegistersUnchanged initial final

theorem epilogueSlot_six (initial : RamState) (mode : Mode := .plain) (fullState : Bool := false) :
    epilogueSlot initial (mode.pushCount fullState) mode fullState = stackPtr initial := by
  cases mode <;> cases fullState <;> exact BitVec.sub_add_cancel _ _

theorem epilogueSlot_succ (initial : RamState) (k : Nat) (mode : Mode := .plain) (fullState : Bool := false) :
    epilogueSlot initial k mode fullState + 8 = epilogueSlot initial (k + 1) mode fullState := by
  simp only [epilogueSlot, Nat.mul_add, Nat.mul_one,
    BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem epiloguePopReg_read (mode : Mode) (fullState : Bool) (s : RamState) (i : Fin (mode.pushCount fullState)) :
    (Operand.reg ((epiloguePopReg mode fullState i).setWidth 5) : Operand 64).read s =
      s.regValue (mode.savedRegisters fullState)[i] := by
  cases mode <;> cases fullState <;> (first | change Fin 6 at i | change Fin 5 at i | change Fin 4 at i) <;> finite_cases i <;> rfl

theorem epiloguePopReg_injective (mode : Mode) (fullState : Bool) :
    Function.Injective (fun i : Fin (mode.pushCount fullState) ↦ (epiloguePopReg mode fullState i).setWidth 5) := by
  unfold Function.Injective
  cases mode <;> cases fullState <;> decide +kernel

theorem epiloguePopReg_ne_rsp (mode : Mode) (fullState : Bool) (i : Fin (mode.pushCount fullState)) : (epiloguePopReg mode fullState i).setWidth 5 ≠ 4 := by
  revert i
  cases mode <;> cases fullState <;> decide +kernel

theorem epiloguePop_next (mode : Mode) (fullState : Bool) (p : BitVec 64) (i : Fin (mode.pushCount fullState)) :
    epiloguePopPC p i.val mode fullState + BitVec.ofNat 64 (encodePopR64 (epiloguePopReg mode fullState i)).length =
      epiloguePopPC p (i.val + 1) mode fullState := by
  unfold epiloguePopPC
  rw [BitVec.add_assoc]
  congr 1
  revert i
  cases mode <;> cases fullState <;> decide +kernel

theorem epiloguePop_step [Bindings] (mode : Mode) (fullState : Bool) (p : BitVec 64) (i : Fin (mode.pushCount fullState)) :
    StepEffect (PopPre (epiloguePopPC p i.val mode fullState))
      (codeRange (epiloguePopPC p i.val mode fullState) (encodePopR64 (epiloguePopReg mode fullState i)))
      (popR64Effect (epiloguePopPC p i.val mode fullState) (encodePopR64 (epiloguePopReg mode fullState i)).length
        ((epiloguePopReg mode fullState i).setWidth 5)) := by
  cases mode <;> cases fullState <;> (first | change Fin 6 at i | change Fin 5 at i | change Fin 4 at i) <;> finite_cases i <;> first
  | exact pop_r64_effect_step _ _ (by decide +kernel) (by decide +kernel)
  | exact pop_r64_rex_effect_step _ _ _ (by unfold RexPrefix; decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem epiloguePop_code (v : Variant) (mode : Mode) (p : BitVec 64) (keccak fullState : Bool) (i : Fin (mode.pushCount fullState)) :
    ∀ x ∈ codeRange (epiloguePopPC p i.val mode fullState) (encodePopR64 (epiloguePopReg mode fullState i)),
      x ∈ epilogueCode v mode p keccak fullState := by
  exact codeRange_mem_of_drop (epiloguePopOffset i.val mode fullState) (by cases mode <;> cases v <;> cases keccak <;> cases fullState <;> (first | change Fin 6 at i | change Fin 5 at i | change Fin 4 at i) <;> finite_cases i <;> decide +kernel)

theorem epiloguePop_changes (mode : Mode) (fullState : Bool) (p : BitVec 64) (i : Fin (mode.pushCount fullState)) (s : RamState) :
    ∀ c ∈ (popR64Effect (epiloguePopPC p i.val mode fullState)
      (encodePopR64 (epiloguePopReg mode fullState i)).length ((epiloguePopReg mode fullState i).setWidth 5) s).components,
      c ∈ epilogueChanges := by
  have h : ∀ i : Fin (mode.pushCount fullState), Component.reg ((epiloguePopReg mode fullState i).setWidth 5) ∈
      epilogueChanges := by cases mode <;> cases fullState <;> decide +kernel
  simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl)
  · exact h i
  · decide +kernel
  · decide +kernel

theorem epilogueProgress_pop {v : Variant} {mode : Mode} {keccak fullState : Bool} {p : BitVec 64} {initial start s t : RamState} (i : Fin (mode.pushCount fullState))
    (hp : EpiloguePre v p initial mode start keccak fullState) (hs : EpilogueProgress p initial start i.val s mode fullState)
    (he : (popR64Effect (epiloguePopPC p i.val mode fullState) (encodePopR64 (epiloguePopReg mode fullState i)).length
      ((epiloguePopReg mode fullState i).setWidth 5) s).Holds s t) :
    EpilogueProgress p initial start (i.val + 1) t mode fullState := by
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact id)
  refine ⟨he.rip.trans (epiloguePop_next mode fullState p i), ?_, hmem.trans hs.memory, ?_, ?_, ?_⟩
  · exact he.writes.2.trans ((congrArg (· + 8) hs.stack).trans (epilogueSlot_succ _ _ mode fullState))
  · exact (hs.agrees.trans (he.agrees.mono (epiloguePop_changes mode fullState p i s))).mono
      (fun c hc ↦ (List.mem_append.mp hc).elim id id)
  · intro j hj
    by_cases hji : j = i
    · subst j
      rw [he.writes.1, hs.stack]
      change memLoad s.external (epilogueSlot initial i.val mode fullState) 64 = _
      rw [hs.memory]
      exact hp.saved.saved i
    · have hreg : (epiloguePopReg mode fullState j).setWidth 5 ≠ (epiloguePopReg mode fullState i).setWidth 5 :=
        fun h ↦ hji (epiloguePopReg_injective mode fullState h)
      have hold := he.agrees.read (n := 64) (r := (epiloguePopReg mode fullState j).setWidth 5) (by
        simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil,
          Component.reg.injEq, reduceCtorEq, or_false, not_or]
        exact ⟨hreg, epiloguePopReg_ne_rsp mode fullState j⟩)
      exact hold.trans (hs.saved j (by have := i.isLt; have := j.isLt; omega))
  · intro j hj
    apply Eq.trans (he.agrees.read ?_) (hs.preserved j hj)
    simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil,
      Component.reg.injEq, reduceCtorEq, or_false, not_or]
    exact ⟨Ne.symm (hj i), epiloguePopReg_ne_rsp .plain false j⟩

theorem epiloguePop_advance [Bindings] {v : Variant} {mode : Mode} {keccak fullState : Bool} {p : BitVec 64} {code : CodeMap}
    {initial start : RamState} (hp : EpiloguePre v p initial mode start keccak fullState)
    (hcode : ∀ x ∈ epilogueCode v mode p keccak fullState, x ∈ code)
    (hboundary : ∀ k ≤ mode.pushCount fullState, epiloguePopPC p k mode fullState ≠ (returnBoundary initial).rip) (i : Fin (mode.pushCount fullState)) :
    AdvanceTriple (returnBoundary initial) 1 (fun s ↦ EpilogueProgress p initial start i.val s mode fullState) code
      (fun _ t ↦ EpilogueProgress p initial start (i.val + 1) t mode fullState) := by
  intro s hready hc hs
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hs.stack]
    exact (hp.readable ⟨i.val, by omega⟩).of_external_eq hs.memory
  obtain ⟨t, hrun, ht, he⟩ := (epiloguePop_step mode fullState p i).advances hready
    (hc.mono (fun x hx ↦ hcode x (epiloguePop_code v mode p keccak fullState i x hx))) ⟨hs.rip, hread⟩
    (by exact (epiloguePop_next mode fullState p i) ▸ hboundary (i.val + 1) (by omega))
  exact ⟨t, hrun, ht, he.codeIn (popR64Effect_avoids _ _ _ _ _) hc,
    epilogueProgress_pop i hp hs he⟩

set_option maxRecDepth 2048 in
theorem epilogueStart_advance [Bindings] (v : Variant) (mode : Mode) (p : BitVec 64) (initial : RamState) (keccak fullState : Bool := false)
    {code : CodeMap} (hcode : ∀ x ∈ epilogueCode v mode p keccak fullState, x ∈ code)
    (hboundary : epiloguePopPC p 0 mode fullState ≠ (returnBoundary initial).rip) :
    AdvanceTriple (returnBoundary initial) 1 (fun s ↦ EpiloguePre v p initial mode s keccak fullState) code
      (fun s t ↦ EpilogueProgress p initial s 0 t mode fullState) := by
  intro s hready hc hp
  have hsub : ∀ x ∈ codeRange p (0x48 :: 0x81 :: 0xc4 :: immBytes 32 (allocation v mode keccak fullState)),
      x ∈ epilogueCode v mode p keccak fullState := by
    simpa only [BitVec.add_zero, epilogueCode] using
      (codeRange_mem_of_drop (p := p) (all := epilogueBytes v mode keccak fullState)
        (bytes := 0x48 :: 0x81 :: 0xc4 :: immBytes 32 (allocation v mode keccak fullState)) 0 (by cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel))
  have hstep := add_r64_imm32_effect_step p 0x48 0xc4 (allocation v mode keccak fullState)
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hc.mono (fun x hx ↦ hcode x (hsub x hx))) hp.rip hboundary
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [addR64Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact id)
  refine ⟨t, hrun, ht, he.codeIn (addR64Imm32Effect_avoids _ _ _ _ _) hc,
    ?_, ?_, hmem, ?_, ?_, ?_⟩
  · simp only [epiloguePopPC, epiloguePopOffset, List.take_zero, List.flatMap_nil,
      List.length_nil, Nat.add_zero]
    exact he.rip
  · have hw : stackPtr t = stackPtr s + (allocation v mode keccak fullState).signExtend 64 := he.writes
    rw [hw, hp.stack]
    change frameBase initial v mode keccak fullState + (allocation v mode keccak fullState).signExtend 64 = epilogueSlot initial 0 mode fullState
    simp only [epilogueSlot, Nat.mul_zero, BitVec.add_zero]
    cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
      simp only [frameBase, Mode.frameSize, allocation, Mode.pushCount] <;>
      simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · exact he.agrees.mono (by
      change ∀ c ∈ [Component.reg 4, .flags, .rip], c ∈ epilogueChanges
      simp [epilogueChanges])
  · intro i hi
    omega
  · intro j hj
    apply Eq.trans (he.agrees.read ?_) (hp.preserved j hj)
    simp only [addR64Imm32Effect_components, List.mem_cons, List.not_mem_nil,
      Component.reg.injEq, reduceCtorEq, or_false]
    exact epiloguePopReg_ne_rsp .plain false j

theorem epilogueFinish_returns [Bindings] {v : Variant} {mode : Mode} {keccak fullState : Bool} {p : BitVec 64} {code : CodeMap}
    {initial start : RamState} (hp : EpiloguePre v p initial mode start keccak fullState)
    (hcode : ∀ x ∈ epilogueCode v mode p keccak fullState, x ∈ code) :
    ReturnTriple (returnBoundary initial) 1 (fun s ↦ EpilogueProgress p initial start (mode.pushCount fullState) s mode fullState) code
      (fun _ t ↦ ReadyToStep t ∧ EpilogueResult initial start t) := by
  intro s hready hc hs
  have hsp : stackPtr s = stackPtr initial := hs.stack.trans (epilogueSlot_six _ mode fullState)
  have htop : stackTop s = stackTop initial := by
    change memLoad s.external (stackPtr s) 64 = _
    rw [hsp, hs.memory]
    exact hp.saved.returnSlot
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hs.stack]
    exact (hp.readable ⟨mode.pushCount fullState, by omega⟩).of_external_eq hs.memory
  have hsub : ∀ x ∈ codeRange (epiloguePopPC p (mode.pushCount fullState) mode fullState) [0xc3], x ∈ epilogueCode v mode p keccak fullState :=
    codeRange_mem_of_drop (epiloguePopOffset (mode.pushCount fullState) mode fullState) (by cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel)
  obtain ⟨t, hstep, ht, he⟩ := ret_effect_step (epiloguePopPC p (mode.pushCount fullState) mode fullState) s hready
    (hc.mono (fun x hx ↦ hcode x (hsub x hx)))
    ⟨⟨hs.rip, hread⟩, htop ▸ hp.target⟩
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl) x <;> exact id)
  have hstack : stackPtr t = stackPtr initial + 8 :=
    he.writes.trans (congrArg (· + 8) hsp)
  have hrip : t.RIP = stackTop initial := he.rip.trans htop
  have hsaved : ∀ j : Fin 6, t.regValue savedRegisters[j] = initial.regValue savedRegisters[j] := by
    intro j
    have hjread := epiloguePopReg_read .plain false t j
    change (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read t = t.regValue savedRegisters[j] at hjread
    rw [← hjread]
    apply Eq.trans (he.agrees.read ?_)
    · by_cases h : ∃ i : Fin (mode.pushCount fullState),
          (epiloguePopReg mode fullState i).setWidth 5 = (epiloguePopReg .plain false j).setWidth 5
      · obtain ⟨i, hi⟩ := h
        have hr := epiloguePopReg_read mode fullState initial i
        rw [hi] at hr
        have hsaved := hs.saved i i.isLt
        rw [hi] at hsaved
        exact hsaved.trans (hr.symm.trans (epiloguePopReg_read .plain false initial j))
      · exact hs.preserved j (by simpa only [not_exists] using h)
    · simp only [retEffect_components, List.mem_cons, List.not_mem_nil,
        Component.reg.injEq, reduceCtorEq, or_false]
      exact epiloguePopReg_ne_rsp .plain false j
  refine ⟨t, Returns.of_step hstep hrip hstack, ht,
    ⟨hrip, hstack, hmem.trans hs.memory, ?_, ?_⟩⟩
  · exact (hs.agrees.trans (he.agrees.mono (by
      simp [retEffect_components, epilogueChanges]))).mono
      (fun c hc ↦ (List.mem_append.mp hc).elim id id)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved ⟨0, by decide⟩
    · exact hsaved ⟨5, by decide⟩
    · exact hsaved ⟨1, by decide⟩
    · exact hsaved ⟨2, by decide⟩
    · exact hsaved ⟨3, by decide⟩
    · exact hsaved ⟨4, by decide⟩

theorem epilogue_returns [Bindings] (v : Variant) (mode : Mode) (p : BitVec 64) (initial : RamState) (keccak fullState : Bool := false)
    {code : CodeMap} (hcode : ∀ x ∈ epilogueCode v mode p keccak fullState, x ∈ code)
    (hboundary : ∀ k ≤ mode.pushCount fullState, epiloguePopPC p k mode fullState ≠ (returnBoundary initial).rip) :
    ReturnTriple (returnBoundary initial) (mode.pushCount fullState + 2) (fun s ↦ EpiloguePre v p initial mode s keccak fullState) code
      (fun s t ↦ ReadyToStep t ∧ EpilogueResult initial s t) := by
  intro s hready hc hp
  obtain ⟨s₁, hrun₁, hr₁, hc₁, hp₁⟩ :=
    epilogueStart_advance v mode p initial keccak fullState hcode (hboundary 0 (by omega)) s hready hc hp
  have hpop := AdvanceTriple.iterate (boundary := returnBoundary initial)
    (invariant := fun k t ↦ EpilogueProgress p initial s k t mode fullState) (mode.pushCount fullState) 1 (fun i hi ↦
      epiloguePop_advance hp hcode hboundary ⟨i, hi⟩)
  obtain ⟨s₂, hrun₂, hr₂, hc₂, hp₂⟩ := hpop s₁ hr₁ hc₁ hp₁
  obtain ⟨t, hrun₃, ht, hresult⟩ :=
    epilogueFinish_returns hp hcode s₂ hr₂ hc₂ hp₂
  refine ⟨t, ?_, ht, hresult⟩
  have h := (hrun₁.trans hrun₂).returns hrun₃
  have hcount : 1 + mode.pushCount fullState * 1 + 1 = mode.pushCount fullState + 2 := by omega
  rw [hcount] at h
  exact h

end Sha3.Proofs.Wrapper.Finish
