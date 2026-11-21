import P256.Proofs.Signing.Core.NextNonce.Call

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.NextNonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Nonce (State)

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}
  {state final : State} {nonce : Nat}
  (pre : SignPre s boundary) (input : Loop s t state)
  (source : t.regValue .rsi = frameBase s + 40)
  (destination : t.regValue .rdi = frameBase s + 2160)
  (effect : (callEffect (fun _ => 0x107330) 0x10cad9 t).Holds t u)
  (result : Nonce.Fill.Result u v boundary (frameBase s + 272) nonce final)

include pre input effect result in
theorem fill_memory : MemoryWriteFrame t v (Nonce.Fill.regions u) := by
  have sp : stackPtr u = stackPtr s - 2288 := effect.writes.1.trans (push_address input.frame)
  have spNat : (stackPtr u).toNat = (stackPtr s).toNat - 2288 := by
    rw [sp]
    exact stack_sub_toNat pre.stack (by decide)
  have bounded : (Stack.region u 2096).Bounded := by
    have bounds := stack_bounds pre.stack
    change (Stack.region u 2096).start + (Stack.region u 2096).size < 2^32
    rw [stack_region_end, spNat]
    change 4584 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at bounds
    omega
  apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame _) result.frame
  intro c member address cover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> try exact cover.elim
  obtain ⟨i, bound, rfl⟩ := cover
  rw [show pushAddr t = stackPtr u from effect.writes.1.symm]
  refine ⟨Stack.region u 2096, by simp [Nonce.Fill.regions], ?_⟩
  apply memoryRegion_contains_add bounded (len := 8) _ _ bound
  · exact Nat.sub_le _ _
  · rw [stack_region_end]
    exact Nat.le_refl _

include pre input source destination effect result in
theorem fill_outer_frame :
    MemoryWriteFrame t v #v[registerRegion s .rdi 65, Stack.region s 4584] := by
  have si : u.regValue .rsi = frameBase s + 40 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have di : u.regValue .rdi = frameBase s + 2160 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have sp : stackPtr u = stackPtr s - 2288 := effect.writes.1.trans (push_address input.frame)
  have within := layout.regions_within pre.stack sp
    (si.trans (base_add s (offset := 40) (by decide)))
    (di.trans (base_add s (offset := 2160) (by decide)))
  intro a outside
  apply fill_memory pre input effect result a
  intro region member contained
  apply outside (Stack.region s 4584) (by simp)
  have members : region = registerRegion u .rdi 72 ∨ region = registerRegion u .rsi 32 ∨
      region = Stack.region u 2096 := by
    simpa [Nonce.Fill.regions] using member
  rcases members with rfl | rfl | rfl
  · exact within _ (by simp) _ contained
  · exact within _ (by simp) _ contained
  · exact within _ (by simp) _ contained

include pre input source destination effect result in
theorem fill_byte {offset : Nat} (bound : offset < 2288)
    (nonceApart : offset < 40 ∨ 72 ≤ offset) (stateApart : offset < 2160 ∨ 2232 ≤ offset) :
    v.external[frameBase s + BitVec.ofNat 64 offset]? =
      t.external[frameBase s + BitVec.ofNat 64 offset]? := by
  have bounds := stack_bounds pre.stack
  change 4584 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at bounds
  have si : u.regValue .rsi = frameBase s + 40 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have di : u.regValue .rdi = frameBase s + 2160 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have siNat : (u.regValue .rsi).toNat = (stackPtr s).toNat - 2280 + 40 := by
    rw [si]
    exact base_nat pre (by decide)
  have diNat : (u.regValue .rdi).toNat = (stackPtr s).toNat - 2280 + 2160 := by
    rw [di]
    exact base_nat pre (by decide)
  have baseNat : (frameBase s).toNat = (stackPtr s).toNat - 2280 :=
    stack_sub_toNat pre.stack (by decide)
  have offsetNat : (frameBase s + BitVec.ofNat 64 offset).toNat =
      (stackPtr s).toNat - 2280 + offset := by
    rw [BitVec.toNat_add, baseNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : offset < 2^64)]
    exact Nat.mod_eq_of_lt (by omega)
  have sp : stackPtr u = stackPtr s - 2288 := effect.writes.1.trans (push_address input.frame)
  have spNat : (stackPtr u).toNat = (stackPtr s).toNat - 2288 := by
    rw [sp]
    exact stack_sub_toNat pre.stack (by decide)
  apply fill_memory pre input effect result
  intro region member contained
  have members : region = registerRegion u .rdi 72 ∨ region = registerRegion u .rsi 32 ∨
      region = Stack.region u 2096 := by
    simpa [Nonce.Fill.regions] using member
  rcases members with rfl | rfl | rfl
  · change (u.regValue .rdi).toNat ≤ _ ∧ _ < (u.regValue .rdi).toNat + 72 at contained
    rw [diNat, offsetNat] at contained
    omega
  · change (u.regValue .rsi).toNat ≤ _ ∧ _ < (u.regValue .rsi).toNat + 32 at contained
    rw [siNat, offsetNat] at contained
    omega
  · change (Stack.region u 2096).start ≤ _ ∧
      _ < (Stack.region u 2096).start + (Stack.region u 2096).size at contained
    rw [stack_region_end, spNat, offsetNat] at contained
    omega

include pre input source destination effect result in
theorem fill_word {offset : Nat} (bound : offset + 8 ≤ 2288)
    (nonceApart : offset + 8 ≤ 40 ∨ 72 ≤ offset)
    (stateApart : offset + 8 ≤ 2160 ∨ 2232 ≤ offset) :
    (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read v =
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read t := by
  apply memLoad_congr
  intro i hi
  change (v.external[_]?).getD 0 = (t.external[_]?).getD 0
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    fill_byte pre input source destination effect result (by omega) (by omega) (by omega)]

include pre input source destination effect result in
theorem fill_frame : Frame s v := by
  refine {
    machine := result.machine
    bindingsSupported := result.bindingsSupported
    loaded := result.loaded
    directionFlag := result.directionFlag
    allocated := fun a present => result.allocated a
      (effect.agrees.grow a (input.frame.allocated a present))
    frame := memoryWriteFrame_trans input.frame.frame (fill_outer_frame pre input source destination effect result)
    rsp := ?_
    saved := ?_
    returnAddress := ?_
    mxcsr := result.mxcsr.trans
      ((effect.agrees.mxcsr (by simp)).trans input.frame.mxcsr)
    fp87 := result.fp87.trans
      ((effect.agrees.fcw (by simp)).trans input.frame.fp87)
  }
  · have sp : v.regValue .rsp = stackPtr u + 8 := result.rsp
    exact sp.trans ((callEffect_stack effect).2.trans input.frame.rsp)
  · intro entry member
    have upper : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    apply Eq.trans _ (input.frame.saved entry member)
    have address : stackPtr s - BitVec.ofNat 64 entry.2 =
        frameBase s + BitVec.ofNat 64 (2280-entry.2) := by
      rw [base_add s (by omega), Nat.sub_sub_self (by omega : entry.2 ≤ 2280)]
    rw [address]
    exact fill_word pre input source destination effect result (by omega) (.inr (by omega)) (.inr (by omega))
  · have address : stackPtr s = frameBase s + BitVec.ofNat 64 2280 :=
      (BitVec.sub_add_cancel _ _).symm
    apply Eq.trans _ input.frame.returnAddress
    rw [address]
    exact fill_word pre input source destination effect result (by decide) (.inr (by decide)) (.inr (by decide))

include pre input source destination effect result in
theorem fill_candidate (positive : 0 < nonce) (canonical : nonce < Operations.domain.n) :
    Candidate s v final nonce := by
  have si : u.regValue .rsi = frameBase s + 40 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have di : u.regValue .rdi = frameBase s + 2160 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  refine {
    frame := fill_frame pre input source destination effect result
    arguments := arguments_copy input.arguments (fun offset live =>
      fill_byte pre input source destination effect result (by omega) (by omega) (.inl (by omega)))
    generator := ?_
    bytes := ?_
    positive := positive
    canonical := canonical
    rbp := ?_
    rbx := ?_
    r13 := ?_
    r14 := ?_
    r15 := ?_
  }
  · simpa only [di] using result.generator
  · simpa only [registerRegion, si] using result.output
  · exact (result.calleeSaved .rbp (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans input.rbp)
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans input.rbx)
  · exact (result.calleeSaved .r13 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 13) (by simp)).trans input.r13)
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp)).trans input.r14)
  · exact (result.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans input.r15)

end P256.Proofs.Signing.Core.NextNonce
