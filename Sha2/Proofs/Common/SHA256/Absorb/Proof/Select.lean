import Sha2.Proofs.Common.SHA256.Absorb.Proof.Stage
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Preparation

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem select_size [Bindings] {l : Layout} {initial s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : ExecutionState initial s regions)
    (data : Prepared l (l.sp initial) prior input s) :
    ∃ t, Preserved l initial s t regions ∧
      Prepared l (l.sp initial) prior input {t with RIP := l.entry} ∧
      t.regValue .rdx = BitVec.ofNat 64 (64 - prior.size % 64) ∧
      Blocks.readReg t l.registers.remaining =
        BitVec.ofNat 64 input.bytes.size - BitVec.ofNat 64 (64 - prior.size % 64) ∧
      t.RIP = if input.bytes.size < 64 - prior.size % 64 then l.pc .smallSetup else l.pc .emptyTest := by
  obtain ⟨u, preservedU, first⟩ := run_stage ctx (Preserved.initial state data.rsp)
    .prepare rfl (data.rip.trans ctx.flow.entry) data.bufferRegister (by intro h; cases h)
  have bufferU : ∀ r ∈ l.bufferSource, Blocks.readReg u r = l.buffer (l.sp initial) := by
    intro r member
    exact (preservedU.frame.registers (r.setWidth 5)
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      (ctx.flow.bufferSaved r member).1).trans (data.bufferRegister r member)
  obtain ⟨t, preservedT, second⟩ := run_stage ctx preservedU .smallBranch rfl first.rip bufferU
    (by intro h; cases h)
  have values := prepare_values data first
  have branchRead (r : BitVec 5) :
      (.reg r : Operand 64).read t = (.reg r : Operand 64).read u :=
    second.agrees.read (by simp [Stage.effect, branchEffect, Effect.components])
  have read (r : BitVec 4) (count : r ≠ 2) (remaining : r ≠ l.registers.remaining) :
      Blocks.readReg t r = Blocks.readReg s r := by
    exact (branchRead (r.setWidth 5)).trans
      (prepare_source (sp := l.sp initial) (l := {l with registers := {l.registers with source := r}})
        count remaining first)
  have memory (a : BitVec 64) : t.external[a]? = s.external[a]? := by
    apply (first.agrees.trans second.agrees).memory
    simp [Stage.effect, Blocks.effect, branchEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]
  have distinct := List.pairwise_cons.mp ctx.flow.prepareRegisters
  have lengthDistinct := List.pairwise_cons.mp distinct.2
  have sourceDistinct : l.registers.source ≠ l.registers.remaining := by
    have h := (List.pairwise_cons.mp ctx.flow.splitRegisters).1 l.registers.remaining (by simp)
    simpa only [ctx.flow.alignedSource] using h
  refine ⟨t, preservedT, ?_, (branchRead 2).trans values.1,
    (branchRead (l.registers.remaining.setWidth 5)).trans values.2.1, ?_⟩
  · refine ⟨rfl, preservedT.rsp, ?_, ?_, ?_, ?_, ?_, data.bounded, data.messageBound, ?_, ?_⟩
    · exact data.hasher.of_bytes (fun _ _ => memory _)
    · exact (read _ ctx.flow.sourceNotCount sourceDistinct).trans data.source
    · exact (read _ (lengthDistinct.1 2 (by simp))
        (lengthDistinct.1 _ (by simp))).trans data.length
    · exact (read _ (distinct.1 2 (by simp)) (distinct.1 _ (by simp))).trans data.position
    · exact ⟨data.bytes.1, fun i => (memory _).trans (data.bytes.2 i)⟩
    · intro r member
      exact (preservedT.frame.registers (r.setWidth 5)
        (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
        (ctx.flow.bufferSaved r member).1).trans (data.bufferRegister r member)
    · intro call member r encoding
      have kept := ctx.targets.copies call member
      rw [encoding] at kept
      exact (preservedT.frame.registers (r.setWidth 5)
        (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
        kept.2).trans (data.copyRegister call member r encoding)
  · rw [second.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF then l.pc .smallSetup else l.pc .emptyTest) = _
    rw [values.2.2]
    simp only [decide_eq_true_eq]

end Sha2.Proofs.Common.SHA256.Absorb
