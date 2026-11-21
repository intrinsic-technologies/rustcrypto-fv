import Sha3.Proofs.Update.EntryExit.Code
import Sha3.Proofs.Machine

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def pushSource : Nat → BitVec 4
  | 0 => 5 | 1 => 15 | 2 => 14 | 3 => 13 | 4 => 12 | 5 => 3 | _ => 0

def pushOffset : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 7 | 5 => 9 | 6 => 10 | _ => 11

def pushedState (initial : RamState) : Nat → RamState
  | 0 => initial
  | n + 1 => pushAfter (pushedState initial n) (pushSource n)

def pushChanges (initial : RamState) : List Component :=
  [.reg 4, .rip, .mem (stackBase initial) 328]

theorem pushOffset_succ {n : Nat} (h : n < 7) :
    pushOffset (n + 1) = pushOffset n + (encodePushR64 (pushSource n)).length := by
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem pushSource_length {n : Nat} (h : n < 7) :
    0 < (encodePushR64 (pushSource n)).length ∧
      (encodePushR64 (pushSource n)).length < 2^32 := by
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem pushedState_rsp (initial : RamState) (n : Nat) :
    stackPtr (pushedState initial n) = initial.regValue .rsp - BitVec.ofNat 64 (8 * n) := by
  induction n with
  | zero => exact (BitVec.sub_zero _).symm
  | succ n ih =>
    change stackPtr (pushAfter (pushedState initial n) (pushSource n)) = _
    rw [pushAfter_rsp, pushAddr, ih, Nat.mul_succ, BitVec.ofNat_add, ← BitVec.sub_sub]
    rfl

theorem pushAddress_stackBase (initial : RamState) {n : Nat} (hn : n < 7) :
    pushAddr (pushedState initial n) =
      stackBase initial + BitVec.ofNat 64 (328 - 8 * (n + 1)) := by
  rw [pushAddr, pushedState_rsp, stackBase, BitVec.sub_sub]
  have he : (328 : BitVec 64) = BitVec.ofNat 64 (8 * n) + 8 +
      BitVec.ofNat 64 (328 - 8 * (n + 1)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64)
      (show 328 = 8 * n + 8 + (328 - 8 * (n + 1)) by omega)
  rw [he]
  simp only [← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem pushedState_agrees (initial : RamState) {n : Nat} (hn : n ≤ 7) :
    AgreesExcept (pushChanges initial) initial (pushedState initial n) := by
  induction n with
  | zero => exact .refl _ _
  | succ n ih =>
    have ha := AgreesExcept.afterStep_push (pushedState initial n)
      (encodePushR64 (pushSource n)).length
      ((Operand.reg ((pushSource n).setWidth 5) : Operand 64).read (pushedState initial n))
      (BitVec.add (pushedState initial n).RIP
        (BitVec.ofNat 64 (encodePushR64 (pushSource n)).length))
    have hw : AgreesExcept (pushChanges initial) (pushedState initial n)
        (pushedState initial (n + 1)) := ha.widen (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl) hc
      · simp [pushChanges]
      · cases hc
      · simp [pushChanges]) (by
      intro address c hc hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hcover.elim
      · obtain ⟨j, hj, rfl⟩ := hcover
        refine ⟨.mem (stackBase initial) 328, by simp [pushChanges],
          328 - 8 * (n + 1) + j, by omega, ?_⟩
        rw [pushAddress_stackBase _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
      · exact hcover.elim)
    exact ((ih (by omega)).trans hw).mono
      (fun c hc ↦ (List.mem_append.mp hc).elim id id)

theorem pushChanges_writesWithin {initial : RamState} (hs : Stack.Valid initial stackBytes) :
    WritesWithin (pushChanges initial) (writeRegions initial) := by
  intro c hc address hcover
  simp only [pushChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover.elim
  · exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨⟨(stackBase initial).toNat, stackBytes⟩, by simp [writeRegions], ?_⟩
    have hlow := stack_sub_low hs (Nat.le_refl stackBytes)
    change (stackBase initial).toNat + 328 < 2^32 at hlow
    simp only [MemoryRegion.Contains, stackBytes, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩

theorem pushedState_ready [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {n : Nat} (hn : n ≤ 7) : ReadyToStep (pushedState initial n) := by
  have ha := pushedState_agrees initial hn
  apply h.ready.of_agreesExcept ha
  have hf := ha.memoryWriteFrame (pushChanges_writesWithin h.stack)
  exact (identityMappedMemory_of_memoryWriteFrame hf (fun r hr a hc ht ↦
    h.avoids r hr a hc (.inr ht))
    (congrArg (·.CR3) ha.rest) h.ready.memory).tables

theorem pushedState_code [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {n : Nat} (hn : n ≤ 7) : CodeIn Extracted.programImage (pushedState initial n) := by
  have hf := (pushedState_agrees initial hn).memoryWriteFrame (pushChanges_writesWithin h.stack)
  exact CodeIn.of_loaded (programLoaded_of_memoryWriteFrame hf
    (fun r hr a hc hp ↦ h.avoids r hr a hc (.inl hp)) h.loaded)
      (SectionsLow.codeLow programSections_low)

theorem pushedState_rip [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {n : Nat} (hn : n ≤ 7) :
    (pushedState initial n).RIP = v.updateAddress + BitVec.ofNat 64 (pushOffset n) := by
  induction n with
  | zero => simpa only [pushedState, pushOffset, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.rip
  | succ n ih =>
    change (pushAfter (pushedState initial n) (pushSource n)).RIP = _
    rw [show (pushAfter (pushedState initial n) (pushSource n)).RIP =
      BitVec.add (pushedState initial n).RIP
        (BitVec.ofNat 64 (encodePushR64 (pushSource n)).length) from
      afterStep_push_rip (pushedState_ready h (by omega)) _ _ _]
    rw [ih (by omega), pushOffset_succ (by omega), BitVec.ofNat_add]
    exact BitVec.add_assoc _ _ _

theorem pushedState_register (initial : RamState) (n : Nat) (r : BitVec 5) (hr : r ≠ 4) :
    (Operand.reg r : Operand 64).read (pushedState initial n) =
      (Operand.reg r : Operand 64).read initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ha := AgreesExcept.afterStep_push (pushedState initial n)
      (encodePushR64 (pushSource n)).length
      ((Operand.reg ((pushSource n).setWidth 5) : Operand 64).read (pushedState initial n))
      (BitVec.add (pushedState initial n).RIP
        (BitVec.ofNat 64 (encodePushR64 (pushSource n)).length))
    exact (ha.read (by simpa only [List.mem_cons, Component.reg.injEq,
      List.not_mem_nil, or_false, reduceCtorEq, or_false] using hr)).trans ih


theorem pushedState_advances [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {boundary : ReturnBoundary} (hb : ¬ InProgram boundary.rip)
    {n : Nat} (hn : n ≤ 7) : Advances boundary n initial (pushedState initial n) := by
  induction n with
  | zero => exact (advances_zero _ _ _).mpr rfl
  | succ n ih =>
    have hready := pushedState_ready h (by omega : n ≤ 7)
    have hcode := pushedState_code h (by omega : n ≤ 7)
    have hrip := pushedState_rip h (by omega : n ≤ 7)
    have hc : ∀ x ∈ codeRange (v.updateAddress + BitVec.ofNat 64 (pushOffset n))
        (encodePushR64 (pushSource n)), x ∈ Extracted.programImage := by
      intro x hx
      apply prologueCode_subset v x
      apply codeRange_mem_of_drop (pushOffset n) _ x hx
      have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
      rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have he : pushAddr (pushedState initial n) =
        initial.regValue .rsp - BitVec.ofNat 64 (8 * (n + 1)) := by
      rw [pushAddr, pushedState_rsp, Nat.mul_succ, BitVec.ofNat_add, ← BitVec.sub_sub]
      rfl
    have hread : MemReadable (pushedState initial n) (pushAddr (pushedState initial n)) 8 := by
      rw [he]
      refine ⟨?_, fun i hi ↦ ?_⟩
      · have hl := stack_sub_low h.stack (show 8 * (n + 1) ≤ 328 by omega)
        change _ < 2^32 at hl
        omega
      · exact (pushedState_agrees initial (by omega : n ≤ 7)).grow _
          (Option.isSome_iff_exists.mpr (stack_sub_allocated h.stack
            (show 8 * (n + 1) ≤ 328 by omega) (by omega)))
    have hpage : (pushAddr (pushedState initial n)).toNat % 4096 + 8 ≤ 4096 := by
      rw [he, stack_sub_toNat h.stack.2.2.1 (show 8 * (n + 1) ≤ 328 by omega)]
      have ha := h.stack.2.2.2
      change (initial.regValue .rsp).toNat % 16 = 8 at ha
      have hu := h.stack.2.2.1
      change 328 ≤ (initial.regValue .rsp).toNat at hu
      omega
    have hc' := hcode.mono hc
    have hstep := push_r64_step_of_register_readable _ hready (pushSource n)
      (hrip ▸ hc'.bytesAt)
      (hrip ▸ hc'.low (pushSource_length (by omega)).1 (pushSource_length (by omega)).2)
      hread hpage
    apply (ih (by omega)).trans (Advances.of_step hstep (.inl ?_))
    rw [show pushAfter (pushedState initial n) (pushSource n) = pushedState initial (n + 1)
      from rfl, pushedState_rip h (by omega)]
    intro heq
    apply hb (heq ▸ prologuePC_inProgram v ?_)
    have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
    rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem stack_return_readable {initial : RamState} {budget : Nat}
    (hStack : Stack.Valid initial budget) : MemReadable initial (stackPtr initial) 8 := by
  apply memReadable_of_region hStack.1 hStack.2.1
  · change (initial.regValue .rsp).toNat - budget ≤ (initial.regValue .rsp).toNat
    omega
  · have hu := hStack.2.2.1
    change budget ≤ (initial.regValue .rsp).toNat at hu
    change (initial.regValue .rsp).toNat + 8 ≤
      (initial.regValue .rsp).toNat - budget +
        ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - budget))
    omega

def pushedBytes (initial : RamState) : Nat → Nat → UInt8
  | 0, i => memByte initial.external (stackPtr initial + BitVec.ofNat 64 i)
  | n + 1, i => if i < 8 then
      storedByte ((Operand.reg ((pushSource n).setWidth 5) : Operand 64).read initial) i
    else pushedBytes initial n (i - 8)

theorem pushSource_ne_rsp (n : Nat) : (pushSource n).setWidth 5 ≠ 4 := by
  unfold pushSource
  split <;> decide +kernel

theorem pushedState_bytes {initial : RamState} {budget n : Nat}
    (hStack : Stack.Valid initial budget) (hn : n ≤ 7) :
    Bytes (pushedState initial n).external (stackPtr (pushedState initial n)) (8 * n + 8)
      (pushedBytes initial n) := by
  induction n with
  | zero => exact Bytes.of_isSome (stack_return_readable hStack).mem
  | succ n ih =>
    have hp := (ih (by omega)).pushAfter (pushSource n) (by omega)
    rw [show 8 + (8 * n + 8) = 8 * (n + 1) + 8 by omega] at hp
    apply hp.congr
    intro i hi
    change (if i < 8 then _ else _) = (if i < 8 then _ else _)
    rw [pushedState_register initial n _ (pushSource_ne_rsp n)]

theorem pushedBytes_saved (initial : RamState) (i : Fin 6) (j : Nat) (hj : j < 8) :
    pushedBytes initial 7 (8 + 8 * i.val + j) =
      storedByte (initial.regValue savedRegisters[i]) j := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> finite_cases i <;> rfl

theorem pushedState_savedFrame {initial : RamState} {budget : Nat}
    (hStack : Stack.Valid initial budget) : SavedFrame initial (pushedState initial 7) := by
  have hb := pushedState_bytes hStack (by decide : 7 ≤ 7)
  constructor
  · intro i
    change memLoad (pushedState initial 7).external _ 64 = _
    have hf : frameBase initial = stackPtr (pushedState initial 7) :=
      (pushedState_rsp initial 7).symm
    rw [hf]
    apply Bytes.memLoad (hn := by decide) (h128 := by decide)
    exact ((hb.sub (8 + 8 * i.val) 8 (by have := i.isLt; omega)).congr
      (fun j hj ↦ pushedBytes_saved initial i j hj))
  · change memLoad (pushedState initial 7).external (stackPtr initial) 64 =
      memLoad initial.external (stackPtr initial) 64
    have he : stackPtr (pushedState initial 7) + 56 = stackPtr initial := by
      rw [pushedState_rsp]
      exact BitVec.sub_add_cancel _ _
    have ht := hb.sub 56 8 (by decide)
    rw [show BitVec.ofNat 64 56 = 56 from rfl, he] at ht
    apply memLoad_congr
    intro i hi
    have hbi := ht i hi
    have hv : pushedBytes initial 7 (56 + i) =
        memByte initial.external (stackPtr initial + BitVec.ofNat 64 i) := by
      simp +arith [pushedBytes]
    dsimp only at hbi
    rw [hv] at hbi
    change ((pushedState initial 7).external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0 = _
    rw [hbi]
    rfl

end Sha3.Proofs.Update
