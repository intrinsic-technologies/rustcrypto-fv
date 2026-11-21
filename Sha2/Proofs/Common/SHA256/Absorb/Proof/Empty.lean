import Sha2.Proofs.Common.SHA256.Absorb.Proof.Stage
import Sha2.Proofs.Wrapper.Absorb.Arithmetic

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem empty_setup [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (data : Prepared l (l.sp initial) prior input {s with RIP := l.entry})
    (rip : s.RIP = l.pc .emptySetup) (empty : prior.size % 64 = 0) :
    ∃ t, Preserved l initial before t regions ∧ Aligned l (l.sp initial) prior input 0 t ∧
      (Stage.emptySetup.effect l (l.sp initial) s).Holds s t ∧
      (∀ r ∈ l.bufferRestore, Blocks.readReg t r = l.buffer (l.sp initial)) ∧
      t.regValue .rdx = BitVec.ofNat 64 (input.bytes.size / 64) := by
  obtain ⟨t, preserved, effect⟩ := run_stage ctx state .emptySetup rfl rip
    data.bufferRegister (by intro h; cases h)
  have memory := effect.agrees.external (by
    cases hr : l.bufferRestore <;>
      simp [Stage.effect, hr, Effect.components, Write.component, Operand.component, Component.Covers])
  have sourceNotRemaining : l.registers.source ≠ l.registers.remaining := by
    have h := (List.pairwise_cons.mp ctx.flow.splitRegisters).1 l.registers.remaining (by simp)
    simpa only [ctx.flow.alignedSource] using h
  have source : Blocks.readReg t l.registers.source = Blocks.readReg s l.registers.source := by
    apply effect.agrees.read
    intro member
    cases hr : l.bufferRestore with
    | none =>
      simp only [Stage.effect, hr, Option.toList_none, List.map_nil, List.append_nil,
        Effect.components, List.map_cons, List.map_nil, Write.component, Operand.component,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with ((eq | eq) | eq) | eq
      · apply sourceNotRemaining
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using
          congrArg BitVec.toNat (Component.reg.inj eq)
      · apply ctx.flow.sourceNotCount
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using
          congrArg BitVec.toNat (Component.reg.inj eq)
      all_goals cases eq
    | some r =>
      have saved := (ctx.flow.restoredSaved r (by simp [hr])).2 .restoreSource (by simp)
        (l.sp initial) s
      have independent : (r.setWidth 5) ≠ l.registers.source.setWidth 5 := by
        intro same
        apply saved
        simp [Stage.effect, Effect.components, Write.component, Operand.component,
          same, ctx.flow.alignedSource]
      simp only [Stage.effect, hr, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with eq | eq | eq | eq | eq
      · apply sourceNotRemaining
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using
          congrArg BitVec.toNat (Component.reg.inj eq)
      · apply ctx.flow.sourceNotCount
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using
          congrArg BitVec.toNat (Component.reg.inj eq)
      · exact independent (Component.reg.inj eq).symm
      all_goals cases eq
  have writes := effect.writes
  simp only [Stage.effect, List.cons_append, List.nil_append] at writes
  have length : Blocks.readReg t l.registers.remaining = BitVec.ofNat 64 input.bytes.size :=
    writes.1.trans data.length
  have countWrite : t.regValue .rdx = Blocks.readReg s l.registers.length >>> 6 := by
    cases hr : l.bufferRestore with
    | none =>
      have w := writes.2
      simp only [hr, Option.toList_none, List.map_nil] at w
      exact w
    | some r =>
      have w := effect.writes
      simp only [Stage.effect, hr, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append] at w
      exact w.2.1
  have inputLength : Blocks.readReg s l.registers.length = BitVec.ofNat 64 input.bytes.size := data.length
  have count : t.regValue .rdx = BitVec.ofNat 64 (input.bytes.size / 64) := by
    rw [countWrite, inputLength, Wrapper.Absorb.block_count, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := data.messageBound; omega)]
  refine ⟨t, preserved, ?_, effect, ?_, count⟩
  · refine ⟨preserved.rsp, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using empty
    · apply Wrapper.hashState_of_bytes (s := s) (by simpa [HashStateAt] using data.hasher.hashWords)
      intro i hi
      rw [memory]
      rfl
    · simpa [memory] using data.hasher.blocks
    · simpa [ctx.flow.alignedSource] using source.trans data.source
    · simpa using length
  · intro r member
    cases hr : l.bufferRestore with
    | none => simp [hr] at member
    | some r' =>
      have same : r' = r := by simpa [hr] using member
      subst r
      have w := effect.writes
      simp only [Stage.effect, hr, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append] at w
      exact w.2.2

end Sha2.Proofs.Common.SHA256.Absorb
