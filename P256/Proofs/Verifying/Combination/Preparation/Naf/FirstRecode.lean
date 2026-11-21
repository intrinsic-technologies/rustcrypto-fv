import P256.Proofs.Verifying.Combination.Preparation.Naf.FirstSerialize
import P256.Proofs.Verifying.Combination.Preparation.Naf.Scalar
import P256.Proofs.Verifying.Combination.Preparation.Naf.Call
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev PointerComponents (s : RamState) : List Component :=
  [.mem (stackPtr s - 6520) 8, .mem (stackPtr s - 6504) 8,
    .mem (stackPtr s - 6512) 8, .mem (stackPtr s - 6528) 8,
    .reg 0, .reg 3, .reg 5, .reg 7, .reg 6, .rip]

theorem pointer_byte [Bindings] {s t a : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (PointerComponents s) t a)
    {off len i : Nat} (ho : off ≤ 8808) (hl : len ≤ off+8)
    (apart : ∀ dst ∈ [6520,6504,6512,6528], off+8 ≤ dst ∨ dst+len ≤ off)
    (hi : i < len) :
    a.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [PointerComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals
    obtain ⟨j, hj, he⟩ := hv
    exact stack_sub_apart pre.stack (by decide) ho (by decide) hl
      (apart _ (by simp)) j hj i hi he.symm

structure FirstScalarCallInput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552 where
  rip : t.RIP = 0x106684
  values : InputAt t (stackPtr s - 6496) p q u v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi
  cursorPointer : memLoad t.external (stackPtr s - 6528) 64 = stackPtr s - 6520
  pointPointer : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6496
  input : t.regValue .rsi = stackPtr s - 6528
  output : t.regValue .rdi = stackPtr s - 6240
  buffer : t.regValue .rbx = stackPtr s - 6240
  iterator : t.regValue .rbp = stackPtr s - 6528
  target : t.regValue .r14 = 0x11c930

theorem first_recode_input [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary) (input : ScalarInput s t p q u v) :
    ∃ fuel a, Advances boundary fuel t a ∧ FirstScalarCallInput s a p q u v := by
  have cp : FirstSerialize.Pre t := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro k hk
      change MemWritable t (stackPtr t + BitVec.ofNat 64 (24+8*k)) 8
      rw [scalar_stack_address (frameOffset := 6552) input.rsp (by decide) (by omega)]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp))
        (by omega) (by omega)) input.allocated
    · intro k hk off len bound
      exact stack_code (frameOffset := 6552) pre input.toFrameState (by decide) (by omega) bound
  obtain ⟨n, a, runA, readyA, _, effect⟩ := FirstSerialize.run boundary pre.outerBoundary t
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x664e FirstSerialize.bytes
      (by decide) (by decide +kernel)) cp
  have a24 : (Operand.reg 4 : Operand 64).read t + 24 = stackPtr s - 6528 :=
    scalar_stack_address input.rsp (offset := 24) (by decide) (by decide)
  have a32 : (Operand.reg 4 : Operand 64).read t + 32 = stackPtr s - 6520 :=
    scalar_stack_address input.rsp (offset := 32) (by decide) (by decide)
  have a40 : (Operand.reg 4 : Operand 64).read t + 40 = stackPtr s - 6512 :=
    scalar_stack_address input.rsp (offset := 40) (by decide) (by decide)
  have a48 : (Operand.reg 4 : Operand 64).read t + 48 = stackPtr s - 6504 :=
    scalar_stack_address input.rsp (offset := 48) (by decide) (by decide)
  have a312 : (Operand.reg 4 : Operand 64).read t + 312 = stackPtr s - 6240 :=
    scalar_stack_address input.rsp (offset := 312) (by decide) (by decide)
  have agrees : AgreesExcept (PointerComponents s) t a := by
    have h := effect.agrees
    simp only [FirstSerialize.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append] at h
    simpa only [PointerComponents, a24, a32, a40, a48] using h
  have stateA : State s a := by
    apply FrameState.after_effect pre (by decide) input.toFrameState readyA agrees ?_ (by simp [PointerComponents])
    intro c hc addr covered
    simp only [PointerComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨workRegion s 8808, by simp, work_contains pre (by decide) (by decide) covered⟩
  have writes := effect.writes
  change memLoad a.external ((Operand.reg 4 : Operand 64).read t + 32) 64 = t.regValue .rbx ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 48) 64 = _ ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 40) 64 = _ ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 24) 64 = t.regValue .r15 ∧
    a.regValue .rax = _ ∧ a.regValue .rbx = _ ∧ a.regValue .rbp = _ ∧
    a.regValue .rdi = _ ∧ a.regValue .rsi = _ at writes
  rw [a24, a32, a40, a48, a312] at writes
  obtain ⟨b, runB, readyB, zero⟩ := (xor_r32_r32_effect_step 0x106682 0xd2 rfl).advances
    (readyToStep stateA.machine stateA.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateA.loaded) 0x6682 _
      (by decide) (by decide +kernel)) effect.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6684 (by decide)))
  have agreesB : AgreesExcept [.reg 2, .flags, .rip] a b := zero.agrees
  have stateB := stateA.after_registers readyB agreesB (by simp [Component.Covers]) (by simp)
  have memB := agreesB.external (by simp [Component.Covers])
  have kept (off len : Nat) (ho : off ≤ 8808) (hl : len ≤ off+8)
      (apart : ∀ dst ∈ [6520,6504,6512,6528], off+8 ≤ dst ∨ dst+len ≤ off) :
      ∀ i < len, b.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (congrArg (fun ram : Ram => ram[_]?) memB).trans (pointer_byte pre agrees ho hl apart hi)
  refine ⟨n+1, b, runA.trans runB, stateB, zero.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact input.values.of_bytes_eq (kept 6496 256 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · exact input.leftTable.of_copy (kept 3120 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · exact input.rightTable.of_copy (kept 2352 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6536 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)
  · rw [memB]; exact writes.2.2.2.1.trans input.cursor
  · rw [memB]; exact writes.1.trans input.pair
  · exact (agreesB.read (n := 64) (r := 6) (by simp)).trans writes.2.2.2.2.2.2.2.2
  · exact (agreesB.read (n := 64) (r := 7) (by simp)).trans writes.2.2.2.2.2.2.2.1
  · exact (agreesB.read (n := 64) (r := 3) (by simp)).trans writes.2.2.2.2.2.1
  · exact (agreesB.read (n := 64) (r := 5) (by simp)).trans writes.2.2.2.2.2.2.1
  · exact (agreesB.read (n := 64) (r := 14) (by simp)).trans
      ((agrees.read (n := 64) (r := 14) (by simp [PointerComponents])).trans input.target)

def firstScalarSite : ScalarCallSite :=
  ⟨0x6684, 0x4ae7, by decide, by decide +kernel, by decide⟩

structure FirstRecodeOutput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552 where
  rip : t.RIP = 0x106689
  naf : Combination.Naf.NafAt t (stackPtr s - 6240) u
  second : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - 6368 + 96) v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi
  cursorPointer : memLoad t.external (stackPtr s - 6528) 64 = stackPtr s - 6520
  pointPointer : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6368
  buffer : t.regValue .rbx = stackPtr s - 6240
  iterator : t.regValue .rbp = stackPtr s - 6528
  target : t.regValue .r14 = 0x11c930

theorem first_recode (correct : Combination.Naf.Serialize.ScalarCorrect) [Bindings]
    {s t : RamState} {boundary : ReturnBoundary} {p q : Projective} {u v : Nat}
    (pre : Pre s boundary) (input : FirstScalarCallInput s t p q u v) :
    ∃ fuel a, Advances boundary fuel t a ∧ FirstRecodeOutput s a p q u v := by
  obtain ⟨n, a, run, stateA, ripA, naf, point, regs, kept⟩ :=
    serialize_call_of_correct correct pre input.toFrameState firstScalarSite
      (by decide) (by decide) input.rip input.input input.output input.cursorPointer
      input.pointPointer input.values.2.1
  have second : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - 6368 + 96) v := by
    have h := input.values.2.2.2
    have addr : stackPtr s - 6496 + 224 = stackPtr s - 6368 + 96 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    simpa only [addr] using h
  refine ⟨n, a, run, stateA, ripA, naf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨second.1, ?_⟩
    intro i hi
    refine Eq.trans ?_ (second.2 i hi)
    have h := kept 6368 128 (by decide) (by decide) (Or.inr (by decide))
      (Or.inl (by decide)) (96+i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h
  · exact input.leftTable.of_copy (kept 3120 768 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)))
  · exact input.rightTable.of_copy (kept 2352 768 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)))
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6536 8 (by decide) (by decide)
      (Or.inr (by decide)) (Or.inr (by decide)) i hi)
  · refine Eq.trans ?_ input.cursorPointer
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6528 8 (by decide) (by decide)
      (Or.inr (by decide)) (Or.inr (by decide)) i hi)
  · rw [point]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · exact (regs .rbx (by simp)).trans input.buffer
  · exact (regs .rbp (by simp)).trans input.iterator
  · exact (regs .r14 (by simp)).trans input.target

end P256.Proofs.Verifying.Combination.Preparation.Naf
