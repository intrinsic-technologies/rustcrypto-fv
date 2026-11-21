import Sha2.Proofs.Digest.Arguments
import Sha2.Proofs.Wrapper512.State

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512
open Sha2.Proofs.Common.SHA256.Blocks.Digest

theorem prologue512_saved {initial s : RamState} {p : BitVec 64}
    (push : (Prologue.effect p .six552 initial).Holds initial s) :
    SavedStackAt initial s := by
  constructor
  · intro slot member
    apply Write.allHold_iff.mp push.writes
      (⟨(.mem (stackPtr initial - BitVec.ofNat 64 slot.2) : Operand 64),
        initial.regValue slot.1⟩ : Write)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six, rspOf,
      stackPtr, Operand.read]
    all_goals rfl
  · apply memLoad_congr
    intro i hi
    change (s.external[_]?).getD 0 = (initial.external[_]?).getD 0
    congr 1
    apply push.agrees.byte
    intro c member covered
    simp only [Prologue.effect, Prologue.registers, Epilogue.Layout.six,
      ite_true, List.nil_append, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.append, List.cons_append, Effect.components,
      Write.component, Operand.component] at member
    change c ∈ [Component.mem (rspOf initial - 8) 8,
      .mem (rspOf initial - 16) 8, .mem (rspOf initial - 24) 8,
      .mem (rspOf initial - 32) 8, .mem (rspOf initial - 40) 8,
      .mem (rspOf initial - 48) 8, .reg 4, .flags, .rip] at member
    have apart (offset : BitVec 64) (h : OffsetsApart (-offset) 8 0#64 8)
        (cover : (Component.mem (rspOf initial - offset) 8).Covers
          (stackPtr initial + BitVec.ofNat 64 i)) : False := by
      obtain ⟨j, hj, eq⟩ := cover
      apply OffsetsApart.ne h (stackPtr initial) hj hi (by decide)
      have hz : stackPtr initial + 0#64 = stackPtr initial := BitVec.add_zero _
      rw [hz]
      have hr : rspOf initial = stackPtr initial := by simp [rspOf, stackPtr, Operand.read]
      simpa only [hr, BitVec.sub_eq_add_neg] using eq.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals apply apart _ (by unfold OffsetsApart; decide +kernel) covered

theorem entered512_state [bindings : Bindings] (v : Variant)
    {initial : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (v.routine .digest) initial data) :
    ∃ s, Preserved v initial s .digest ∧
      s.regValue .r14 = BitVec.ofNat 64 data.size ∧
      s.regValue .rsi = initial.regValue .rdi ∧
      s.RIP = v.pc 0x1a .digest := by
  have member : v.routine .digest ∈
      [sha384Digest, sha512Digest, sha512_224Digest, sha512_256Digest] := by
    cases v <;> simp [Variant.routine_sha384_digest, Variant.routine_sha512_digest,
      Variant.routine_sha512_224_digest, Variant.routine_sha512_256_digest]
  obtain ⟨p, s, state, push, args, output, length, source, rsp, rip⟩ :=
    entered512 (v.routine .digest) member machine call
  have memory (a : BitVec 64) : s.external[a]? = p.external[a]? := by
    apply args.agrees.memory
    intro c hc
    change c ∈ [.reg 3,.reg 14,.reg 6,.rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp [Component.Covers]
  have reads (a : BitVec 64) : memLoad s.external a 64 = memLoad p.external a 64 := by
    apply memLoad_congr
    intro i _
    exact congrArg (fun b => b.getD 0) (memory (a + BitVec.ofNat 64 i))
  have saved := prologue512_saved push
  have savedS : SavedStackAt initial s := by
    constructor
    · intro slot hs
      exact (reads _).trans (saved.words slot hs)
    · exact (reads _).trans saved.returnAddress
  refine ⟨s, ⟨State.of_executionState state savedS rsp, output, trivial, trivial⟩,
    length, source, ?_⟩
  simpa [Variant.routine, Variant.pc, BitVec.add_assoc, BitVec.ofNat_add] using rip

end Sha2.Proofs.Digest
