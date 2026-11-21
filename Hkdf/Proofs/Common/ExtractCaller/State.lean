import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.ExtractCaller
import Hkdf.Proofs.Common.ExtractCaller.Spill
import Hkdf.Proofs.Standard.State

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem saved_of_prologue {initial s : RamState}
    (memory : s.external = Hkdf.Proofs.Common.Encoding.Serialize.saveMemory initial) :
    Hkdf.Proofs.Standard.SavedStackAt initial s := by
  constructor
  · intro slot member
    rw [memory]
    exact Hkdf.Proofs.Common.Encoding.Serialize.saveMemory_saved initial slot member
  · change memLoad s.external (stackPtr initial) 64 = memLoad initial.external (stackPtr initial) 64
    rw [memory]
    simp only [Hkdf.Proofs.Common.Encoding.Serialize.saveMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

theorem standard_middle [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (context : Hkdf.Proofs.Standard.Context initial salt inputs) :
    ∃ s, Hkdf.Proofs.Standard.Preserved initial s ∧ s.RIP = 0x101445 ∧
      stackPtr s = stackPtr initial - 520 ∧
      s.regValue .rcx = initial.regValue .rcx ∧ s.regValue .r8 = initial.regValue .r8 := by
  obtain ⟨p, _, ready, running, rip, rsp, memory, frame⟩ := standard_prologue context
  have saved := saved_of_prologue memory
  have outside := (Hkdf.Proofs.Common.Machine.returnBoundary_valid
    (Hkdf.Proofs.Common.Machine.entryReady bindings context.environment context.machine
      context.call.programLoaded).ready context.call.stack context.call.returnAddress).2.2
  obtain ⟨s, _, _, current, effect, sameRsp, endpoint, rcx, r8⟩ :=
    Spill.standard context.call running outside rsp rip
  have savedRange : (Component.mem (stackPtr initial - 48) 56).Agrees p s := by
    have pointer : rspOf p = stackPtr initial - 520 := rsp
    intro i hi
    apply effect.agrees.memory
    intro component member covered
    have changed : ∃ offset ∈ ([-424, -408, -512, -416] : List (BitVec 64)),
        component = .mem (stackPtr initial + offset) 8 := by
      simp only [Spill.standardEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.append_nil, List.cons_append,
        List.nil_append, pointer, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceDiv,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      all_goals exact ⟨_, by simp, rfl⟩
    obtain ⟨offset, offsetMember, rfl⟩ := changed
    have apart : OffsetsApart (-48) 56 offset 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at offsetMember
      rcases offsetMember with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
    obtain ⟨j, hj, eq⟩ := covered
    exact apart.ne (stackPtr initial) hi hj (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using eq)
  have count : p.regValue .rsi = initial.regValue .rsi :=
    frame.read (n := 64) (r := 6) (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame])
  have output : p.regValue .r9 = initial.regValue .r9 :=
    frame.read (n := 64) (r := 9) (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame])
  have pointers : p.regValue .rdi = initial.regValue .rdi :=
    frame.read (n := 64) (r := 7) (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame])
  have lengths : p.regValue .rdx = initial.regValue .rdx :=
    frame.read (n := 64) (r := 2) (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame])
  have base : rspOf p = Hkdf.Proofs.Standard.frameBase initial := rsp
  have stores := effect.writes
  change
    memLoad s.external (rspOf p + 96) 64 = p.regValue .r9 ∧
    memLoad s.external (rspOf p + 112) 64 = p.regValue .rdx ∧
    memLoad s.external (rspOf p + 8) 64 = p.regValue .rsi ∧
    memLoad s.external (rspOf p + 104) 64 = p.regValue .rdi at stores
  rw [base, count, output, pointers, lengths] at stores
  have preserved : Hkdf.Proofs.Standard.Preserved initial s :=
    ⟨⟨current, saved.of_agrees savedRange⟩, sameRsp.trans base,
      stores.2.2.1, stores.1, stores.2.2.2, stores.2.1⟩
  exact ⟨s, preserved, endpoint, sameRsp.trans rsp,
    rcx.trans (frame.read (n := 64) (r := 1)
      (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame])),
    r8.trans (frame.read (n := 64) (r := 8)
      (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame]))⟩

end Hkdf.Proofs.Common.ExtractCaller
