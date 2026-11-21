import Sha3.Proofs.Permutation.LoadStore.Store.Basic
import Sha3.Proofs.Run
import Sha3.Proofs.X86.Instructions.Add.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Sha3.Proofs.Permutation.Store

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program Keccak

def restoreBytes : List UInt8 :=
  [0x48, 0x81, 0xc4, 0xd8, 0, 0, 0, 0x5b, 0x41, 0x5c, 0x41, 0x5d,
    0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3]

def restoreCode (copy : Copy) : CodeMap := codeRange (restoreAddress copy) restoreBytes

def restorePopPC (copy : Copy) (k : Nat) : BitVec 64 :=
  entryAddress copy + match k with
  | 0 => 0x5e8
  | 1 => 0x5e9
  | 2 => 0x5eb
  | 3 => 0x5ed
  | 4 => 0x5ef
  | 5 => 0x5f1
  | _ => 0x5f2

def restorePopReg (i : Fin 6) : BitVec 4 := #v[3, 12, 13, 14, 15, 5][i]

def restoreSlot (initial : RamState) (k : Nat) : BitVec 64 :=
  frameBase initial + BitVec.ofNat 64 (216 + 8 * k)

structure RestorePre (copy : Copy) (initial : RamState) (a : Lanes) (s : RamState) : Prop where
  frame : CallFrame initial s
  rip : s.RIP = (restoreAddress copy)
  lanes : memoryLanes (initial.regValue .rdi) s = a
  readable : ∀ i : Fin 7, MemReadable s (restoreSlot initial i.val) 8
  target : (stackTop initial).toNat < 2^32

structure RestoreProgress (copy : Copy) (initial start : RamState) (k : Nat) (s : RamState) : Prop where
  rip : s.RIP = restorePopPC copy k
  stack : stackPtr s = restoreSlot initial k
  memory : s.external = start.external
  rest : scalarFrame s = scalarFrame start
  saved : ∀ i : Fin 6, i.val < k →
    (Operand.reg ((restorePopReg i).setWidth 5) : Operand 64).read s =
      initial.regValue savedRegisters[i]

theorem restoreSlot_six (initial : RamState) :
    restoreSlot initial 6 = initial.regValue .rsp := by
  exact BitVec.sub_add_cancel _ _

theorem restoreSlot_succ (initial : RamState) (k : Nat) :
    restoreSlot initial k + 8 = restoreSlot initial (k + 1) := by
  simp only [restoreSlot, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc,
    BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem restorePopReg_read (s : RamState) (i : Fin 6) :
    (Operand.reg ((restorePopReg i).setWidth 5) : Operand 64).read s =
      s.regValue savedRegisters[i] := by
  finite_cases i <;> rfl

theorem restorePopReg_injective :
    Function.Injective (fun i : Fin 6 ↦ (restorePopReg i).setWidth 5) := by
  unfold Function.Injective
  decide +kernel

theorem restorePopReg_ne_rsp (i : Fin 6) : (restorePopReg i).setWidth 5 ≠ 4 := by
  revert i
  decide +kernel

theorem restorePop_next (copy : Copy) (i : Fin 6) :
    restorePopPC copy i.val + BitVec.ofNat 64 (encodePopR64 (restorePopReg i)).length =
      restorePopPC copy (i.val + 1) := by
  cases copy <;> finite_cases i <;> rfl

theorem restorePop_step [Bindings] (copy : Copy) (i : Fin 6) :
    StepEffect (PopPre (restorePopPC copy i.val))
      (codeRange (restorePopPC copy i.val) (encodePopR64 (restorePopReg i)))
      (popR64Effect (restorePopPC copy i.val) (encodePopR64 (restorePopReg i)).length
        ((restorePopReg i).setWidth 5)) := by
  cases copy <;> finite_cases i <;> first
  | exact pop_r64_effect_step _ _ (by decide +kernel) (by decide +kernel)
  | exact pop_r64_rex_effect_step _ _ _ (by unfold RexPrefix; decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem restorePop_code (copy : Copy) (i : Fin 6) :
    ∀ x ∈ codeRange (restorePopPC copy i.val) (encodePopR64 (restorePopReg i)),
      x ∈ restoreCode copy := by
  cases copy <;> finite_cases i <;> decide +kernel

theorem restoreProgress_pop {copy : Copy} {initial start s t : RamState} {a : Lanes} (i : Fin 6)
    (hp : RestorePre copy initial a start) (hs : RestoreProgress copy initial start i.val s)
    (he : (popR64Effect (restorePopPC copy i.val) (encodePopR64 (restorePopReg i)).length
      ((restorePopReg i).setWidth 5) s).Holds s t) :
    RestoreProgress copy initial start (i.val + 1) t := by
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact id)
  refine ⟨he.rip.trans (restorePop_next copy i), ?_, hmem.trans hs.memory,
    (he.agrees.scalarFrame_eq (by simp [Effect.components, x86_compose])).trans hs.rest, ?_⟩
  · exact he.writes.2.trans ((congrArg (· + 8) hs.stack).trans (restoreSlot_succ _ _))
  · intro j hj
    by_cases hji : j = i
    · subst j
      rw [he.writes.1, hs.stack]
      change memLoad s.external (restoreSlot initial i.val) 64 = _
      rw [hs.memory]
      exact hp.frame.saved i
    · have hreg : (restorePopReg j).setWidth 5 ≠ (restorePopReg i).setWidth 5 :=
        fun h ↦ hji (restorePopReg_injective h)
      have hold := he.agrees.read (n := 64) (r := (restorePopReg j).setWidth 5) (by
        simp only [popR64Effect_components, List.mem_cons, List.not_mem_nil,
          Component.reg.injEq, reduceCtorEq, or_false, not_or]
        exact ⟨hreg, restorePopReg_ne_rsp j⟩)
      exact hold.trans (hs.saved j (by have := i.isLt; have := j.isLt; omega))

theorem restorePop_advance [Bindings] {copy : Copy} {boundary : ReturnBoundary} {code : CodeMap}
    {initial start : RamState} {a : Lanes} (hp : RestorePre copy initial a start)
    (hcode : ∀ x ∈ restoreCode copy, x ∈ code)
    (hboundary : ∀ k ≤ 6, restorePopPC copy k ≠ boundary.rip) (i : Fin 6) :
    AdvanceTriple boundary 1 (RestoreProgress copy initial start i.val) code
      (fun _ t ↦ RestoreProgress copy initial start (i.val + 1) t) := by
  intro s hready hc hs
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hs.stack]
    exact (hp.readable ⟨i.val, by omega⟩).of_external_eq hs.memory
  obtain ⟨t, hrun, ht, he⟩ := (restorePop_step copy i).advances hready
    (hc.mono (fun x hx ↦ hcode x (restorePop_code copy i x hx))) ⟨hs.rip, hread⟩
    (by exact (restorePop_next copy i) ▸ hboundary (i.val + 1) (by omega))
  exact ⟨t, hrun, ht, he.codeIn (popR64Effect_avoids _ _ _ _ _) hc,
    restoreProgress_pop i hp hs he⟩

theorem restoreStart_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {code : CodeMap}
    (initial : RamState) (a : Lanes) (hcode : ∀ x ∈ restoreCode copy, x ∈ code)
    (hboundary : restorePopPC copy 0 ≠ boundary.rip) :
    AdvanceTriple boundary 1 (RestorePre copy initial a) code
      (fun s t ↦ RestoreProgress copy initial s 0 t) := by
  intro s hready hc hp
  have hsub : ∀ x ∈ codeRange (restoreAddress copy)
      (0x48 :: 0x81 :: 0xc4 :: immBytes 32 216), x ∈ restoreCode copy := by
    cases copy <;> decide +kernel
  have hstep := add_r64_imm32_effect_step (restoreAddress copy) 0x48 0xc4 216
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  have hnext : restoreAddress copy + 7 = restorePopPC copy 0 := by
    cases copy <;> rfl
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hc.mono (fun x hx ↦ hcode x (hsub x hx))) hp.rip (hnext ▸ hboundary)
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [addR64Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact id)
  refine ⟨t, hrun, ht, he.codeIn (addR64Imm32Effect_avoids _ _ _ _ _) hc,
    he.rip.trans hnext, ?_, hmem, he.agrees.scalarFrame_eq (by simp [Effect.components, x86_compose]), ?_⟩
  · change stackPtr t = frameBase initial + 216
    exact he.writes.trans (congrArg (· + 216) hp.frame.stack)
  · intro i hi
    omega

theorem restoreFinish_advance [Bindings] {copy : Copy} {boundary : ReturnBoundary} {code : CodeMap}
    {initial start : RamState} {a : Lanes} (hp : RestorePre copy initial a start)
    (hcode : ∀ x ∈ restoreCode copy, x ∈ code)
    (hboundary : stackTop initial ≠ boundary.rip ∨
      initial.regValue .rsp + 8 ≠ boundary.rsp) :
    AdvanceTriple boundary 1 (RestoreProgress copy initial start 6) code
      (fun s t ↦ CallResult initial t a ∧ t.external = s.external) := by
  intro s hready hc hs
  have hsp : stackPtr s = initial.regValue .rsp := hs.stack.trans (restoreSlot_six _)
  have htop : stackTop s = stackTop initial := by
    change memLoad s.external (stackPtr s) 64 = _
    rw [hsp, hs.memory]
    exact hp.frame.returnSlot
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hs.stack]
    exact (hp.readable ⟨6, by decide⟩).of_external_eq hs.memory
  have hsub : ∀ x ∈ codeRange (returnAddress copy) [0xc3], x ∈ restoreCode copy := by
    cases copy <;> decide +kernel
  obtain ⟨t, hstep, ht, he⟩ := ret_effect_step (returnAddress copy) s hready
    (hc.mono (fun x hx ↦ hcode x (hsub x hx)))
    ⟨⟨hs.rip, hread⟩, htop ▸ hp.target⟩
  have hmem : t.external = s.external := he.agrees.external (by
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl) x <;> exact id)
  have hstack : t.regValue .rsp = initial.regValue .rsp + 8 :=
    he.writes.trans (congrArg (· + 8) hsp)
  have hrip : t.RIP = stackTop initial := he.rip.trans htop
  have hsaved : ∀ i : Fin 6, t.regValue savedRegisters[i] =
      initial.regValue savedRegisters[i] := by
    intro i
    rw [← restorePopReg_read]
    apply Eq.trans (he.agrees.read ?_) (hs.saved i i.isLt)
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil,
      Component.reg.injEq, reduceCtorEq, or_false]
    exact restorePopReg_ne_rsp i
  refine ⟨t, Advances.of_step hstep ?_, ht,
    hc.of_external_eq hmem, ⟨hrip, hstack, ?_, ?_, ?_, ?_,
      (he.agrees.scalarFrame_eq (by simp [Effect.components, x86_compose])).trans (hs.rest.trans hp.frame.rest)⟩, hmem⟩
  · rcases hboundary with hip | hsp'
    · exact .inl (hrip ▸ hip)
    · apply Or.inr
      change t.regValue .rsp ≠ boundary.rsp
      rw [hstack]
      exact hsp'
  · change (fun i ↦ memLoad t.external _ 64) = a
    rw [hmem, hs.memory]
    exact hp.lanes
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved ⟨0, by decide⟩
    · exact hsaved ⟨5, by decide⟩
    · exact hsaved ⟨1, by decide⟩
    · exact hsaved ⟨2, by decide⟩
    · exact hsaved ⟨3, by decide⟩
    · exact hsaved ⟨4, by decide⟩
  · intro address ha
    rw [hmem, hs.memory]
    exact hp.frame.memory address ha
  · intro address ha
    rw [hmem, hs.memory]
    exact hp.frame.grows address ha

theorem restore_advance [Bindings] (copy : Copy) (boundary : ReturnBoundary) (code : CodeMap)
    (initial : RamState) (a : Lanes) (hcode : ∀ x ∈ restoreCode copy, x ∈ code)
    (hboundary : ∀ k ≤ 6, restorePopPC copy k ≠ boundary.rip)
    (hreturn : stackTop initial ≠ boundary.rip ∨
      initial.regValue .rsp + 8 ≠ boundary.rsp) :
    AdvanceTriple boundary 8 (RestorePre copy initial a) code
      (fun s t ↦ CallResult initial t a ∧ t.external = s.external) := by
  intro s hready hc hp
  obtain ⟨s₁, hrun₁, hr₁, hc₁, hp₁⟩ :=
    restoreStart_advance copy initial a hcode (hboundary 0 (by decide)) s hready hc hp
  have hpop := AdvanceTriple.iterate (boundary := boundary)
    (invariant := RestoreProgress copy initial s) 6 1 (fun i hi ↦
      restorePop_advance hp hcode hboundary ⟨i, hi⟩)
  obtain ⟨s₂, hrun₂, hr₂, hc₂, hp₂⟩ := hpop s₁ hr₁ hc₁ hp₁
  obtain ⟨t, hrun₃, ht, hct, hresult, hmem⟩ :=
    restoreFinish_advance hp hcode hreturn s₂ hr₂ hc₂ hp₂
  exact ⟨t, (hrun₁.trans hrun₂).trans hrun₃, ht, hct, hresult,
    hmem.trans hp₂.memory⟩

end Sha3.Proofs.Permutation.Store
