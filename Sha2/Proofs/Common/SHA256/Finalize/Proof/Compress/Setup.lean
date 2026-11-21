import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem setup [Bindings] (last : Bool) {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : HashAt L initial before s regions hash)
    (rip : s.RIP = if last then L.lastSetup else L.firstSetup) :
    ∃ t, HashAt L initial before t regions hash ∧
      t.RIP = (if last then L.lastCall else L.firstCall) ∧
      t.regValue .rdi = L.hash (L.sp initial) ∧ t.regValue .rsi = L.scratch (L.sp initial) ∧
      t.regValue .rdx = 1 ∧ t.external = s.external ∧
      (.reg L.variant.registers.tail : Operand 64).read t = (.reg L.variant.registers.tail : Operand 64).read s ∧
      (.reg L.variant.registers.blocks : Operand 64).read t = (.reg L.variant.registers.blocks : Operand 64).read s ∧
      (last = true → (.reg L.variant.hashReg : Operand 64).read t = L.hash (L.sp initial)) := by
  let p := if last then L.lastSetup else L.firstSetup
  have inside : BlockInProgram p (Setup.bytes L.variant last).length := by
    cases last
    · exact ctx.code.inside .firstSetup
    · exact ctx.code.inside .lastSetup
  obtain ⟨_,t,run,ready,_,effect⟩ := ctx.blocks.setup p last inside s
    (supportedMachine_readyToStep input.state.machine) (by
      cases last
      · exact ctx.code.loaded .firstSetup s input.state.loaded
      · exact ctx.code.loaded .lastSetup s input.state.loaded) rip
  have noMem : ∀ c ∈ (Setup.effect p L.variant last s).components, ∀ a, ¬ c.Covers a := by
    cases h : L.variant <;> cases last <;>
      simp [Setup.effect,Effect.components,Write.component,Operand.component,Component.Covers]
  have memory := effect.agrees.external noMem
  have preserved := input.toPreserved.of_agrees ctx run ready effect.agrees
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by
      intro r _ kept
      cases h : L.variant <;> cases last <;>
        simp_all [Setup.effect,Effect.components,Write.component,Operand.component,Variant.clobbered,
          Variant.padReg,Variant.hashReg,Variant.registers,Blocks.Length.Registers.tail,
          Blocks.Length.Registers.blocks,Blocks.Length.Registers.preShifted])
    (by cases h : L.variant <;> cases last <;>
      simp [Setup.effect,Effect.components,Write.component,Operand.component])
  have state : HashAt L initial before t regions hash := by
    refine ⟨preserved,?_,?_⟩
    · simpa only [HashStateAt,memory] using input.hashWords
    · intro notFirst
      exact (effect.agrees.read (n := 64) (r := L.variant.hashReg) (by
        cases h : L.variant <;> cases last <;>
          simp_all [Setup.effect,Effect.components,Write.component,Operand.component,Variant.hashReg])).trans
        (input.hashPointer notFirst)
  have source : t.regValue .rsi = L.scratch (L.sp initial) := by
    have word := effect.writes.1
    change t.regValue .rsi = rspOf s + BitVec.ofNat 64 L.variant.scratch at word
    simpa only [Layout.scratch,show rspOf s = L.sp initial from input.rsp] using word
  have count : t.regValue .rdx = 1 := effect.writes.2.1
  have output : t.regValue .rdi = if L.variant = .finalizeFirst then rspOf s + 72
      else (.reg L.variant.hashReg : Operand 64).read s := by
    have stores := effect.writes
    cases h : L.variant <;> cases last <;>
      simp only [Setup.effect,h,↓reduceIte,List.cons_append,List.nil_append,Write.AllHold] at stores ⊢
    all_goals first | exact stores.2.2 | exact stores.2.2.1
  refine ⟨t,state,?_,?_,source,count,memory,?_,?_,?_⟩
  · have h := effect.rip
    cases last
    · exact h.trans ctx.flow.firstSetup
    · exact h.trans ctx.flow.lastSetup
  · rw [output]
    by_cases h : L.variant = .finalizeFirst
    · simp only [h,ite_true,show rspOf s = L.sp initial from input.rsp,
        Layout.hash,Layout.buffer,Variant.buffer,Blocks.Zero.Offset.value]
      simp only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat]
      rfl
    · simp only [h,ite_false]
      exact input.hashPointer h
  · exact effect.agrees.read (n := 64) (r := L.variant.registers.tail) (by
      cases h : L.variant <;> cases last <;>
        simp [Setup.effect,Effect.components,Write.component,Operand.component,
          Variant.registers,Blocks.Length.Registers.tail])
  · exact effect.agrees.read (n := 64) (r := L.variant.registers.blocks) (by
      cases h : L.variant <;> cases last <;>
        simp [Setup.effect,Effect.components,Write.component,Operand.component,
          Variant.registers,Blocks.Length.Registers.blocks])
  · intro isLast
    by_cases h : L.variant = .finalizeFirst
    · have stores := effect.writes
      simp only [Setup.effect,h,isLast,and_self,↓reduceIte,List.cons_append,List.nil_append,Write.AllHold] at stores
      simpa only [Layout.hash,Layout.buffer,h,Variant.hashReg,Variant.buffer,Blocks.Zero.Offset.value,
        show rspOf s = L.sp initial from input.rsp,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2
    · exact state.hashPointer h

end Sha2.Proofs.Common.SHA256.Finalize.Compress
