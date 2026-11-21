import P256.Proofs.Program.Compare.Main
import P256.Proofs.Program.Compare.Pre

set_option autoImplicit false

namespace P256.Proofs.Program.Compare

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {size : Nat}

theorem Result.stackFrame (result : Result s t) (pre : CallPre s) :
    MemoryWriteFrame s t #v[Stack.region s 64] := by
  apply result.agrees.memoryWriteFrame
  intro c hc address hcover
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  exact ⟨Stack.region s 64, by simp,
    pre.frame.stack_sub_contains (offset := 64) (len := 64) (by decide) (by decide) hi⟩

theorem Result.loaded (result : Result s t) (pre : ComparePre s boundary size) : ProgramLoaded t := by
  intro address byte hbyte
  refine (result.agrees.byte ?_).trans (pre.loaded address byte hbyte)
  intro c hc hcover
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  exact pre.avoids _ (by simp) _
    (pre.callFrame.stack_sub_contains (offset := 64) (len := 64)
      (by decide) (by decide) hi) (.inl ⟨byte,hbyte⟩)

theorem Result.zero_iff_bytes (result : Result s t) (allowed : size ∈ [1,33,39,65])
    (pre : ComparePre s boundary size) :
    (t.regValue .rax).setWidth 32 = 0 ↔
      ∀ i < size, s.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
        s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
  have bounded : size < 2^64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with rfl | rfl | rfl | rfl <;> decide
  change (Operand.reg 0 : Operand 32).read t = 0 ↔ _
  rw [result.zero_iff, show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
  have left := (pre.callPre allowed).left
  have right := (pre.callPre allowed).right
  rw [show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] at left right
  constructor
  · intro he i hi
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (left.mem i hi)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (right.mem i hi)
    have equal := he i hi
    change (s.external[s.regValue .rdi + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[s.regValue .rsi + BitVec.ofNat 64 i]?).getD 0 at equal
    change s.external[s.regValue .rdi + BitVec.ofNat 64 i]? = some a at ha
    change s.external[s.regValue .rsi + BitVec.ofNat 64 i]? = some b at hb
    simp only [ha, hb, Option.getD_some] at equal
    rw [ha, hb, equal]
  · intro he i hi
    exact congrArg (fun x : Option UInt8 ↦ x.getD 0) (he i hi)

theorem compare_correct_of_size (allowed : size ∈ [1,33,39,65])
    (pre : ComparePre s boundary size) : ∃ t, CompareResult s t boundary size := by
  obtain ⟨fuel, t, run, result⟩ := correct boundary s (pre.callPre allowed) pre.callBoundary
  have frame := result.stackFrame (pre.callPre allowed)
  refine ⟨t, ⟨⟨⟨fuel, run⟩, result.rip, result.rsp,
    bindingsSupported_of_ready_agrees pre.bindingsSupported result.ready result.agrees,
    supportedMachine_of_ready_agrees pre.machine result.ready result.agrees,
    result.calleeSaved, result.agrees.directionFlagClear (by simp [callChanges]) pre.directionFlag,
    result.agrees.mxcsr (by simp [callChanges]), result.agrees.fcw (by simp [callChanges]),
    ?_, result.loaded pre, result.agrees.grow⟩, frame, result.zero_iff_bytes allowed pre⟩⟩
  intro address outside
  apply frame address
  intro region member
  have same : region = Stack.region s 64 := by simpa using member
  subst region
  exact outside _ (by simp)

theorem compare_correct (pre : ComparePre s boundary) : ∃ t, CompareResult s t boundary :=
  compare_correct_of_size (by decide) pre

end P256.Proofs.Program.Compare
