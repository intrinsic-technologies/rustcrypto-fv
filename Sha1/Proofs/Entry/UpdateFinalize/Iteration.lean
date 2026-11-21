import Sha1.Proofs.Streaming.UpdateFinalize.Geometry
import Sha1.Proofs.Entry.UpdateFinalize.Iteration.Load
import Sha1.Proofs.Entry.UpdateFinalize.Iteration.Latch
import Sha1.Proofs.Buffered.Update.Slices
namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Streaming.UpdateFinalize Sha1.Proofs.Buffered

private theorem update_covers {s : RamState} {c : Component} {a : BitVec 64}
    (hl : 344 ≤ (stackPtr s).toNat) (hh : (stackPtr s).toNat + 368 < 2^32)
    (hm : c ∈ UpdateKind.updateFinalize.changes s) (hc : c.Covers a) :
    ((stackPtr s).toNat - 344 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat) ∨
    ((stackPtr s).toNat + 216 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat + 308) := by
  cases c with
  | mem addr len =>
    simp only [UpdateKind.changes, UpdateKind.workRegisters, List.map, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Component.mem.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := hc
      right
      simp only [UpdateKind.context, UpdateKind.contextOffset]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)]
      omega
    · obtain ⟨j, hj, rfl⟩ := hc
      left
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  | _ => exact absurd hc (by simp [Component.Covers])

private theorem frame_after_update [bindings : Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {message input : ByteArray} (h : Frame initial s)
    (hs : Stack.Valid initial SliceHash.updateFinalize.minStackBytes)
    (hp : UpdatePost .updateFinalize boundary message input s t) : Frame initial t := by
  obtain ⟨hl, _, hh, _⟩ := h.stack_bounds hs
  have hrsp : stackPtr t = stackPtr s := hp.agrees.agree (.reg 4)
    (by simp [UpdateKind.changes, UpdateKind.workRegisters]) rfl
  have hword (k : Nat) (hloc : k + 8 ≤ 216 ∨ 308 ≤ k) (hk : k + 8 ≤ 368) :
      stackWord t k = stackWord s k := by
    unfold stackWord
    rw [hrsp]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
    apply hp.agrees.byte
    intro c hm hc
    have hx := update_covers hl hh hm hc
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)] at hx
    omega
  have hmem : MemoryWriteFrame s t #v[Stack.region initial SliceHash.updateFinalize.minStackBytes] := by
    apply hp.agrees.memoryWriteFrame
    intro c hm a hc
    have hx := update_covers hl hh hm hc
    exact ⟨_, Vector.getElem_mem (i := 0) (by decide), (h.stack_contains hs).mpr (by omega)⟩
  exact ⟨hp.ready, hp.code, hp.agrees.directionFlagClear
    (by simp [UpdateKind.changes, UpdateKind.workRegisters]) h.df,
    hrsp.trans h.stack,
    (hword _ (by decide) (by decide)).trans h.output,
    (hword _ (by decide) (by decide)).trans h.pointers,
    (hword _ (by decide) (by decide)).trans h.lengths,
    (hword _ (by decide) (by decide)).trans h.savedRbx,
    (hword _ (by decide) (by decide)).trans h.savedR12,
    (hword _ (by decide) (by decide)).trans h.savedR13,
    (hword _ (by decide) (by decide)).trans h.savedR14,
    (hword _ (by decide) (by decide)).trans h.savedR15,
    (hword _ (by decide) (by decide)).trans h.savedRbp,
    (hword _ (by decide) (by decide)).trans h.returnSlot,
    memoryWriteFrame_trans h.memory hmem, fun a ha ↦ hp.agrees.grow a (h.grows a ha),
    hp.agrees.rest.trans h.fixed⟩

theorem iteration [bindings : Bindings] {initial : RamState} {inputs : Array Slices.Input}
    {i : Nat} {s : RamState} (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hi : i < inputs.size) (h : Header initial inputs i s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Header initial inputs (i + 1) t := by
  obtain ⟨nf, u, hload, hf, hpre, hnonzero, hidx, hsize⟩ := load_slice hCall hStride hOutside hi h
  obtain ⟨v, hp⟩ := Update.update_family hpre hnonzero
  have hreg (r : BitVec 5) (hr : Component.reg r ∉ UpdateKind.updateFinalize.changes u) :=
    show (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read u from hp.agrees.read hr
  have hframe := frame_after_update hf hCall.stackAvailable hp
  have hasp : stackPtr v = stackPtr u := hframe.stack.trans hf.stack.symm
  have hAbs := hp.absorbed
  change Absorbed (stackPtr u + 0xd8) _ v at hAbs
  rw [← hasp, ← Sha1.Proofs.Streaming.message_prefix_succ inputs i hi] at hAbs
  obtain ⟨nl, t, hlatch, ht⟩ := loop_latch hi
    (Sha1.Proofs.Streaming.validInputs_size_lt hCall.inputInMemory) hOutside hframe hAbs hp.rip
    ((hreg 15 (by simp [UpdateKind.changes, UpdateKind.workRegisters])).trans hidx)
    ((hreg 12 (by simp [UpdateKind.changes, UpdateKind.workRegisters])).trans hsize)
  obtain ⟨nu, hupdate⟩ := hp.advances
  exact ⟨_, t, (hload.trans hupdate).trans hlatch, ht⟩

end Sha1.Proofs.Entry.UpdateFinalize
