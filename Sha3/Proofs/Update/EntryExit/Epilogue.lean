import Sha3.Proofs.Update.EntryExit.Code
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def epiloguePopOffset : Nat → Nat
  | 0 => 4
  | 1 => 5
  | 2 => 7
  | 3 => 9
  | 4 => 11
  | 5 => 13
  | _ => 14

def epiloguePopPC (p : BitVec 64) (k : Nat) : BitVec 64 :=
  p + BitVec.ofNat 64 (epiloguePopOffset k)

def epiloguePopReg (i : Fin 6) : BitVec 4 := #v[3, 12, 13, 14, 15, 5][i]

def epilogueSlot (initial : RamState) (k : Nat) : BitVec 64 :=
  frameBase initial + BitVec.ofNat 64 (8 + 8 * k)

def epilogueChanges : List Component :=
  [.reg 3, .reg 12, .reg 13, .reg 14, .reg 15, .reg 5, .reg 4, .flags, .rip]

structure EpiloguePre (p : BitVec 64) (initial s : RamState) : Prop where
  rip : s.RIP = p
  stack : stackPtr s = frameBase initial
  saved : SavedFrame initial s
  readable : ∀ i : Fin 7, MemReadable s (epilogueSlot initial i.val) 8
  target : (stackTop initial).toNat < 2^32

structure EpilogueProgress (p : BitVec 64) (initial start : RamState)
    (k : Nat) (s : RamState) : Prop where
  rip : s.RIP = epiloguePopPC p k
  stack : stackPtr s = epilogueSlot initial k
  memory : s.external = start.external
  agrees : AgreesExcept epilogueChanges start s
  saved : ∀ i : Fin 6, i.val < k →
    (Operand.reg ((epiloguePopReg i).setWidth 5) : Operand 64).read s =
      initial.regValue savedRegisters[i]

structure EpilogueResult (initial start final : RamState) : Prop where
  rip : final.RIP = stackTop initial
  stack : stackPtr final = stackPtr initial + 8
  memory : final.external = start.external
  agrees : AgreesExcept epilogueChanges start final
  saved : CalleeSavedRegistersUnchanged initial final

theorem epilogueSlot_six (initial : RamState) :
    epilogueSlot initial 6 = stackPtr initial := by
  change initial.regValue .rsp - 56 + 56 = initial.regValue .rsp
  exact BitVec.sub_add_cancel _ _

theorem epilogueSlot_succ (initial : RamState) (k : Nat) :
    epilogueSlot initial k + 8 = epilogueSlot initial (k + 1) := by
  simp only [epilogueSlot, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc,
    BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem epiloguePopReg_read (s : RamState) (i : Fin 6) :
    (Operand.reg ((epiloguePopReg i).setWidth 5) : Operand 64).read s =
      s.regValue savedRegisters[i] := by
  finite_cases i <;> rfl

theorem epiloguePopReg_injective :
    Function.Injective (fun i : Fin 6 ↦ (epiloguePopReg i).setWidth 5) := by
  unfold Function.Injective
  decide +kernel

theorem epiloguePopReg_ne_rsp (i : Fin 6) : (epiloguePopReg i).setWidth 5 ≠ 4 := by
  revert i
  decide +kernel

theorem epiloguePop_next (p : BitVec 64) (i : Fin 6) :
    epiloguePopPC p i.val + BitVec.ofNat 64 (encodePopR64 (epiloguePopReg i)).length =
      epiloguePopPC p (i.val + 1) := by
  unfold epiloguePopPC
  rw [BitVec.add_assoc]
  congr 1
  revert i
  decide +kernel

theorem epiloguePop_step [Bindings] (p : BitVec 64) (i : Fin 6) :
    StepEffect (PopPre (epiloguePopPC p i.val))
      (codeRange (epiloguePopPC p i.val) (encodePopR64 (epiloguePopReg i)))
      (popR64Effect (epiloguePopPC p i.val) (encodePopR64 (epiloguePopReg i)).length
        ((epiloguePopReg i).setWidth 5)) := by
  finite_cases i <;> first
  | exact pop_r64_effect_step _ _ (by decide +kernel) (by decide +kernel)
  | exact pop_r64_rex_effect_step _ _ _ (by unfold RexPrefix; decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem epiloguePop_code (p : BitVec 64) (i : Fin 6) :
    ∀ x ∈ codeRange (epiloguePopPC p i.val) (encodePopR64 (epiloguePopReg i)),
      x ∈ epilogueCode p := by
  exact codeRange_mem_of_drop (epiloguePopOffset i.val) (by finite_cases i <;> decide +kernel)

theorem epiloguePop_changes (p : BitVec 64) (i : Fin 6) (s : RamState) :
    ∀ c ∈ (popR64Effect (epiloguePopPC p i.val)
      (encodePopR64 (epiloguePopReg i)).length ((epiloguePopReg i).setWidth 5) s).components,
      c ∈ epilogueChanges := by
  have h : ∀ i : Fin 6, Component.reg ((epiloguePopReg i).setWidth 5) ∈
      epilogueChanges := by decide +kernel
  simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl)
  · exact h i
  · decide +kernel
  · decide +kernel

theorem epilogueProgress_pop {p : BitVec 64} {initial start s t : RamState} (i : Fin 6)
    (hp : EpiloguePre p initial start) (hs : EpilogueProgress p initial start i.val s)
    (he : (popR64Effect (epiloguePopPC p i.val) (encodePopR64 (epiloguePopReg i)).length
      ((epiloguePopReg i).setWidth 5) s).Holds s t) :
    EpilogueProgress p initial start (i.val + 1) t := by
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact id)
  refine ⟨he.rip.trans (epiloguePop_next p i), ?_, hmem.trans hs.memory, ?_, ?_⟩
  · exact he.writes.2.trans ((congrArg (· + 8) hs.stack).trans (epilogueSlot_succ _ _))
  · exact (hs.agrees.trans (he.agrees.mono (epiloguePop_changes p i s))).mono
      (fun c hc ↦ (List.mem_append.mp hc).elim id id)
  · intro j hj
    by_cases hji : j = i
    · subst j
      rw [he.writes.1, hs.stack]
      change memLoad s.external (epilogueSlot initial i.val) 64 = _
      rw [hs.memory]
      exact hp.saved.saved i
    · have hreg : (epiloguePopReg j).setWidth 5 ≠ (epiloguePopReg i).setWidth 5 :=
        fun h ↦ hji (epiloguePopReg_injective h)
      have hold := he.agrees.read (n := 64) (r := (epiloguePopReg j).setWidth 5) (by
        simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil,
          Component.reg.injEq, reduceCtorEq, or_false, not_or]
        exact ⟨hreg, epiloguePopReg_ne_rsp j⟩)
      exact hold.trans (hs.saved j (by have := i.isLt; have := j.isLt; omega))

theorem epiloguePop_advance [Bindings] {boundary : ReturnBoundary} {p : BitVec 64} {code : CodeMap}
    {initial start : RamState} (hp : EpiloguePre p initial start)
    (hcode : ∀ x ∈ epilogueCode p, x ∈ code)
    (hboundary : ∀ k ≤ 6, epiloguePopPC p k ≠ boundary.rip) (i : Fin 6) :
    AdvanceTriple boundary 1 (EpilogueProgress p initial start i.val) code
      (fun _ t ↦ EpilogueProgress p initial start (i.val + 1) t) := by
  intro s hready hc hs
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hs.stack]
    exact (hp.readable ⟨i.val, by omega⟩).of_external_eq hs.memory
  obtain ⟨t, hrun, ht, he⟩ := (epiloguePop_step p i).advances hready
    (hc.mono (fun x hx ↦ hcode x (epiloguePop_code p i x hx))) ⟨hs.rip, hread⟩
    (by exact (epiloguePop_next p i) ▸ hboundary (i.val + 1) (by omega))
  exact ⟨t, hrun, ht, he.codeIn (popR64Effect_avoids _ _ _ _ _) hc,
    epilogueProgress_pop i hp hs he⟩

theorem epilogueStart_advance [Bindings] {boundary : ReturnBoundary}
    (p : BitVec 64) (initial : RamState)
    {code : CodeMap} (hcode : ∀ x ∈ epilogueCode p, x ∈ code)
    (hboundary : epiloguePopPC p 0 ≠ boundary.rip) :
    AdvanceTriple boundary 1 (EpiloguePre p initial) code
      (fun s t ↦ EpilogueProgress p initial s 0 t) := by
  intro s hready hc hp
  have hsub : ∀ x ∈ codeRange p (0x48 :: 0x83 :: 0xc4 :: immBytes 8 8),
      x ∈ epilogueCode p := by
    simpa only [BitVec.add_zero, epilogueCode] using
      (codeRange_mem_of_drop (p := p) (all := epilogueBytes)
        (bytes := 0x48 :: 0x83 :: 0xc4 :: immBytes 8 8) 0 (by decide +kernel))
  have hstep := add_r64_imm8_effect_step p 0x48 0xc4 8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hc.mono (fun x hx ↦ hcode x (hsub x hx))) hp.rip hboundary
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [addR64Imm8Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact id)
  refine ⟨t, hrun, ht, he.codeIn (addR64Imm8Effect_avoids _ _ _ _ _) hc,
    he.rip, ?_, hmem, ?_, ?_⟩
  · exact he.writes.trans (congrArg (· + 8) hp.stack)
  · exact he.agrees.mono (by
      change ∀ c ∈ [Component.reg 4, .flags, .rip], c ∈ epilogueChanges
      simp [epilogueChanges])
  · intro i hi
    omega

theorem epilogueFinish_advance [Bindings] {boundary : ReturnBoundary}
    {p : BitVec 64} {code : CodeMap}
    {initial start : RamState} (hp : EpiloguePre p initial start)
    (hcode : ∀ x ∈ epilogueCode p, x ∈ code)
    (htarget : stackTop initial ≠ boundary.rip) :
    AdvanceTriple boundary 1 (EpilogueProgress p initial start 6) code
      (fun _ t ↦ EpilogueResult initial start t) := by
  intro s hready hc hs
  have hsp : stackPtr s = stackPtr initial := hs.stack.trans (epilogueSlot_six _)
  have htop : stackTop s = stackTop initial := by
    change memLoad s.external (stackPtr s) 64 = _
    rw [hsp, hs.memory]
    exact hp.saved.returnSlot
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hs.stack]
    exact (hp.readable ⟨6, by decide⟩).of_external_eq hs.memory
  have hsub : ∀ x ∈ codeRange (epiloguePopPC p 6) [0xc3], x ∈ epilogueCode p :=
    codeRange_mem_of_drop 14 (by decide +kernel)
  obtain ⟨t, hstep, ht, he⟩ := ret_effect_step (epiloguePopPC p 6) s hready
    (hc.mono (fun x hx ↦ hcode x (hsub x hx)))
    ⟨⟨hs.rip, hread⟩, htop ▸ hp.target⟩
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl) x <;> exact id)
  have hstack : stackPtr t = stackPtr initial + 8 :=
    he.writes.trans (congrArg (· + 8) hsp)
  have hrip : t.RIP = stackTop initial := he.rip.trans htop
  have hsaved : ∀ i : Fin 6, t.regValue savedRegisters[i] =
      initial.regValue savedRegisters[i] := by
    intro i
    rw [← epiloguePopReg_read]
    apply Eq.trans (he.agrees.read ?_) (hs.saved i i.isLt)
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil,
      Component.reg.injEq, reduceCtorEq, or_false]
    exact epiloguePopReg_ne_rsp i
  refine ⟨t, Advances.of_step hstep (.inl (hrip ▸ htarget)), ht,
    he.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components _) _) hc,
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

theorem epilogue_advance [Bindings] {boundary : ReturnBoundary} (p : BitVec 64) (initial : RamState)
    {code : CodeMap} (hcode : ∀ x ∈ epilogueCode p, x ∈ code)
    (hboundary : ∀ k ≤ 6, epiloguePopPC p k ≠ boundary.rip)
    (htarget : stackTop initial ≠ boundary.rip) :
    AdvanceTriple boundary 8 (EpiloguePre p initial) code
      (fun s t ↦ EpilogueResult initial s t) := by
  intro s hready hc hp
  obtain ⟨s₁, hrun₁, hr₁, hc₁, hp₁⟩ :=
    epilogueStart_advance p initial hcode (hboundary 0 (by decide)) s hready hc hp
  have hpop := AdvanceTriple.iterate (boundary := boundary)
    (invariant := EpilogueProgress p initial s) 6 1 (fun i hi ↦
      epiloguePop_advance hp hcode hboundary ⟨i, hi⟩)
  obtain ⟨s₂, hrun₂, hr₂, hc₂, hp₂⟩ := hpop s₁ hr₁ hc₁ hp₁
  obtain ⟨t, hrun₃, ht, hc₃, hresult⟩ :=
    epilogueFinish_advance hp hcode htarget s₂ hr₂ hc₂ hp₂
  exact ⟨t, (hrun₁.trans hrun₂).trans hrun₃, ht, hc₃, hresult⟩

end Sha3.Proofs.Update
