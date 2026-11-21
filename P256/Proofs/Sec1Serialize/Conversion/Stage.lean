import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem carry_extract {t : RamState} {v : Bool}
    (h : (StatusFlags.ofRFLAGS t.RFLAGS).CF = v) :
    t.RFLAGS.extractLsb' 0 1 = BitVec.ofBool v := by
  change t.RFLAGS.getLsbD 0 = v at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he : i = 0 := by omega
  subst i
  simpa only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, Nat.zero_lt_succ,
    decide_true, Bool.true_and, Nat.add_zero] using h

theorem setb_zero (c : Bool) :
    mergeGPR 8 (if c then 1 else 0) 0 = (BitVec.ofBool c).setWidth 64 := by
  cases c <;> rfl

structure Stage [Bindings] (s start t : RamState) (boundary : ReturnBoundary) : Prop
    extends FrameState s t 65 328 312 where
  execution : ∃ fuel, Advances boundary fuel start t

theorem Stage.ready [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (stage : Stage s start t boundary) : ReadyToStep t :=
  readyToStep stage.machine stage.bindingsSupported

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve offset len : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (hspan : offset + len ≤ inputBytes) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) len := by
  have hb := pre.inputBounded
  change (s.regValue .rsi).toNat + inputBytes < 2^32 at hb
  have ho : offset < 2^64 := by omega
  have haddr : (s.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rsi).toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    apply Nat.mod_eq_of_lt
    omega
  apply readable_of_grow (s := s) ?_ grow
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · change (s.regValue .rsi).toNat ≤ _
    rw [haddr]
    omega
  · change _ ≤ (s.regValue .rsi).toNat + inputBytes
    rw [haddr]
    omega

theorem Stage.of_registers [Bindings] {s start t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat}
    (stage : Stage s start t boundary) (exec : Advances boundary fuel t u)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (hcs : ∀ c ∈ cs, (∃ r : BitVec 5, c = .reg r ∧ r.toNat < 16) ∨
      c = .flags ∨ c = .rip)
    (rsp : .reg 4 ∉ cs) : Stage s start u boundary := by
  have memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a := by
    intro c hc a
    rcases hcs c hc with ⟨r, rfl, _⟩ | rfl | rfl <;> exact id
  have df : Component.df ∉ cs := by
    intro h
    rcases hcs _ h with ⟨r, he, _⟩ | he | he <;> cases he
  have mx : Component.mxcsr ∉ cs := by
    intro h
    rcases hcs _ h with ⟨r, he, _⟩ | he | he <;> cases he
  have fc : Component.fcw ∉ cs := by
    intro h
    rcases hcs _ h with ⟨r, he, _⟩ | he | he <;> cases he
  obtain ⟨n, hn⟩ := stage.execution
  exact ⟨stage.toFrameState.after_registers ready agrees memory rsp df mx fc,
    n + fuel, hn.trans exec⟩

theorem Stage.step_registers [Bindings] {s start t u : RamState} {boundary : ReturnBoundary}
    {effect : Effect}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s start t boundary)
    (step : Machine.step t = some (.next u)) (ready : ReadyToStep u)
    (holds : effect.Holds t u)
    (hcs : ∀ c ∈ effect.components, (∃ r : BitVec 5, c = .reg r ∧ r.toNat < 16) ∨
      c = .flags ∨ c = .rip)
    (rsp : .reg 4 ∉ effect.components)
    (next : InProgram effect.rip) : Stage s start u boundary := by
  have advances := Advances.of_step step (.inl (by
    rw [holds.rip]
    exact boundary_ne_program pre.outerBoundary next))
  exact stage.of_registers advances ready holds.agrees hcs rsp

end P256.Proofs.Sec1Serialize.Conversion
