import P256.Proofs.Verifying.Combination.Preparation.Naf.Store
import P256.Proofs.Verifying.Combination.Preparation.Naf.ThirdCopy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x106796)
    (saved : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi) :
    ∃ a, Advances boundary 2 t a ∧ State s a ∧ a.RIP = 0x10679e ∧
      a.regValue .rdi = s.regValue .rdi ∧ AgreesExcept [.reg 3, .reg 7, .rip] t a := by
  have addr : (AddrMode.sib 4 none 0 (.d8 16)).addr t 0x10679b = stackPtr s - 6536 :=
    scalar_stack_address state.rsp (offset := 16) (by decide) (by decide)
  have readable : MemReadable t (stackPtr s - 6536) 8 :=
    readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r64_m64_effect_step 0x106796 0x48 (by simp [RexWPrefix]) 3
      (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6796 _
        (by decide) (by decide +kernel)) ⟨rip, addr ▸ readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x679b (by decide)))
  have agreesA : AgreesExcept [.reg 3, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have source : a.regValue .rbx = s.regValue .rdi := by
    have h := effectA.writes
    change a.regValue .rbx = memLoad t.external ((AddrMode.sib 4 none 0 (.d8 16)).addr t 0x10679b) 64 at h
    rw [addr] at h
    exact h.trans saved
  obtain ⟨b, runB, readyB, effectB⟩ := (mov_r64_r64_effect_step 0x10679b 0x48 0xdf
    (by simp [RexWPrefix]) rfl).advances (readyToStep stateA.machine stateA.bindingsSupported)
      (programText_slice (programLoaded_codeIn stateA.loaded) 0x679b _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x679e (by decide)))
  have agreesB : AgreesExcept [.reg 7, .rip] a b := effectB.agrees
  refine ⟨b, runA.trans runB, stateA.after_registers readyB agreesB (by simp [Component.Covers])
    (by simp), effectB.rip, effectB.writes.trans source, ?_⟩
  apply (agreesA.trans agreesB).mono
  simp

abbrev MetadataComponents (s : RamState) : List Component :=
  [.mem (stackPtr s - 6240) 8, .mem (stackPtr s - 6232) 8,
    .mem (stackPtr s - 6224) 8, .mem (stackPtr s - 6216) 8,
    .mem (stackPtr s - 6208) 8, .mem (stackPtr s - 6200) 8,
    .reg 0, .reg 1, .reg 2, .reg 6, .rip]

theorem metadata_byte [Bindings] {s t a : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (MetadataComponents s) t a)
    {off len i : Nat} (ho : off ≤ 8808) (hl : len ≤ off+8)
    (apart : ∀ dst ∈ [6240,6232,6224,6216,6208,6200], off+8 ≤ dst ∨ dst+len ≤ off)
    (hi : i < len) :
    a.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [MetadataComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals
    obtain ⟨j, hj, he⟩ := hv
    exact stack_sub_apart pre.stack (by decide) ho (by decide) hl
      (apart _ (by simp)) j hj i hi he.symm

structure MultiCallInput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552 where
  rip : t.RIP = 0x10679e
  input : t.regValue .rsi = stackPtr s - 6240
  output : t.regValue .rdi = s.regValue .rdi
  leftNaf : Combination.Naf.NafAt t (stackPtr s - 4656) u
  rightNaf : Combination.Naf.NafAt t (stackPtr s - 4384) v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  tables : memLoad t.external (stackPtr s - 6240) 64 = stackPtr s - 3120
  tablesEnd : memLoad t.external (stackPtr s - 6232) 64 = stackPtr s - 1584
  digits : memLoad t.external (stackPtr s - 6224) 64 = stackPtr s - 4656
  digitsEnd : memLoad t.external (stackPtr s - 6216) 64 = stackPtr s - 4112
  beginIndex : memLoad t.external (stackPtr s - 6208) 64 = 0
  endIndex : memLoad t.external (stackPtr s - 6200) 64 = 2

theorem prepare_metadata [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary) (input : PackedNafOutput s t p q u v) :
    ∃ fuel w, Advances boundary fuel t w ∧ MultiCallInput s w p q u v := by
  have cp : Store.Pre t := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro k hk
      change MemWritable t (stackPtr t + BitVec.ofNat 64 (312+8*k)) 8
      rw [scalar_stack_address (frameOffset := 6552) input.rsp (by decide) (by omega)]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp))
        (by omega) (by omega)) input.allocated
    · intro k hk off len bound
      exact stack_code (frameOffset := 6552) pre input.toFrameState (by decide) (by omega) bound
  obtain ⟨n, a, runA, readyA, _, effect⟩ := Store.run boundary pre.outerBoundary t
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x673e Store.bytes
      (by decide) (by decide +kernel)) cp
  have a312 : (Operand.reg 4 : Operand 64).read t + 312 = stackPtr s - 6240 :=
    scalar_stack_address input.rsp (offset := 312) (by decide) (by decide)
  have a320 : (Operand.reg 4 : Operand 64).read t + 320 = stackPtr s - 6232 :=
    scalar_stack_address input.rsp (offset := 320) (by decide) (by decide)
  have a328 : (Operand.reg 4 : Operand 64).read t + 328 = stackPtr s - 6224 :=
    scalar_stack_address input.rsp (offset := 328) (by decide) (by decide)
  have a336 : (Operand.reg 4 : Operand 64).read t + 336 = stackPtr s - 6216 :=
    scalar_stack_address input.rsp (offset := 336) (by decide) (by decide)
  have a344 : (Operand.reg 4 : Operand 64).read t + 344 = stackPtr s - 6208 :=
    scalar_stack_address input.rsp (offset := 344) (by decide) (by decide)
  have a352 : (Operand.reg 4 : Operand 64).read t + 352 = stackPtr s - 6200 :=
    scalar_stack_address input.rsp (offset := 352) (by decide) (by decide)
  have a3432 : (Operand.reg 4 : Operand 64).read t + 3432 = stackPtr s - 3120 :=
    scalar_stack_address input.rsp (offset := 3432) (by decide) (by decide)
  have a4968 : (Operand.reg 4 : Operand 64).read t + 4968 = stackPtr s - 1584 :=
    scalar_stack_address input.rsp (offset := 4968) (by decide) (by decide)
  have a2440 : (Operand.reg 4 : Operand 64).read t + 2440 = stackPtr s - 4112 :=
    scalar_stack_address input.rsp (offset := 2440) (by decide) (by decide)
  have agrees : AgreesExcept (MetadataComponents s) t a := by
    have h := effect.agrees
    simp only [Store.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append] at h
    simpa only [MetadataComponents, a312, a320, a328, a336, a344, a352] using h
  have stateA : State s a := by
    apply FrameState.after_effect pre (by decide) input.toFrameState readyA agrees ?_ (by simp [MetadataComponents])
    intro c hc addr covered
    simp only [MetadataComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨workRegion s 8808, by simp, work_contains pre (by decide) (by decide) covered⟩
  have writes := effect.writes
  change memLoad a.external ((Operand.reg 4 : Operand 64).read t + 312) 64 = _ ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 320) 64 = _ ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 328) 64 = t.regValue .r15 ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 336) 64 = _ ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 344) 64 = 0 ∧
    memLoad a.external ((Operand.reg 4 : Operand 64).read t + 352) 64 = 2 ∧
    a.regValue .rax = _ ∧ a.regValue .rcx = _ ∧ a.regValue .rdx = _ ∧ a.regValue .rsi = _ at writes
  rw [a312, a320, a328, a336, a344, a352, a3432, a4968, a2440] at writes
  have saved : memLoad a.external (stackPtr s - 6536) 64 = s.regValue .rdi := by
    refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (metadata_byte pre agrees (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hi)
  obtain ⟨w, runW, stateW, ripW, output, agreesW⟩ := output_registers pre stateA effect.rip saved
  have memoryW := agreesW.external (by simp [Component.Covers])
  have kept (off len : Nat) (ho : off ≤ 8808) (hl : len ≤ off+8)
      (apart : ∀ dst ∈ [6240,6232,6224,6216,6208,6200], off+8 ≤ dst ∨ dst+len ≤ off) :
      ∀ i < len, w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (congrArg (fun ram : Ram => ram[_]?) memoryW).trans (metadata_byte pre agrees ho hl apart hi)
  refine ⟨n+2, w, runA.trans runW, stateW, ripW, ?_, output, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (agreesW.read (n := 64) (r := 6) (by simp)).trans writes.2.2.2.2.2.2.2.2.2
  · exact input.leftNaf.of_copy (kept 4656 272 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  · exact input.rightNaf.of_copy (kept 4384 272 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  · exact input.leftTable.of_copy (kept 3120 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  · exact input.rightTable.of_copy (kept 2352 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  · rw [memoryW]; exact writes.1
  · rw [memoryW]; exact writes.2.1
  · rw [memoryW]; exact writes.2.2.1.trans input.third
  · rw [memoryW]; exact writes.2.2.2.1
  · rw [memoryW]; exact writes.2.2.2.2.1
  · rw [memoryW]; exact writes.2.2.2.2.2.1

end P256.Proofs.Verifying.Combination.Preparation.Naf
