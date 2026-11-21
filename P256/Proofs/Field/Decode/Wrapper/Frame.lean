import P256.Proofs.Field.Decode.Wrapper.Epilogue
import P256.Proofs.Field.Decode.Wrapper.Output
import P256.Proofs.Ecdh.Normalize.Conversion.State

set_option autoImplicit false

namespace P256.Proofs.Field.Decode.Wrapper

open P256.Proofs.Ecdh.Normalize.Conversion (Stage registers inputRegisters agrees_trans read_mem_of_agrees)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem work_frame (pre : Pre s boundary)
    (body : AgreesExcept registers t u)
    (stores : AgreesExcept [.mem (s.regValue .rdi) 32, .rip] u v) :
    MemoryWriteFrame t v #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 40 40] := by
  apply (body.trans stores).memoryWriteFrame
  intro c hc a ha
  simp only [registers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  all_goals try exact ha.elim
  obtain ⟨i, hi, rfl⟩ := ha
  exact ⟨registerRegion s .rdi 32, by simp, output_contains pre hi⟩

theorem return_state (pre : Pre s boundary) (entry : Entry s t boundary)
    (body : AgreesExcept registers t u)
    (stores : AgreesExcept [.mem (s.regValue .rdi) 32, .rip] u v)
    (ready : ReadyToStep v) (rip : v.RIP = 0x114364) :
    ReturnState s v (prologueComponents s ++ registers ++ [.mem (s.regValue .rdi) 32, .rip]) := by
  have work := work_frame pre body stores
  have whole : MemoryWriteFrame s v #v[registerRegion s .rdi 32, Stack.region s 40] := by
    apply memoryWriteFrame_trans (h₂ := ScalarFrame.Work.frame pre work)
    intro a ha
    apply entry_frame pre entry a
    intro r hr hin
    have eq : r = Stack.region s 40 := by simpa using hr
    subst r
    exact ha _ (by simp) hin
  have read (off : Nat) (ho : off ≤ 40) :
      memLoad v.external (stackPtr s - BitVec.ofNat 64 off) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 off) 64 :=
    ScalarFrame.Work.read pre (by decide) work ho (by omega)
  refine ⟨ready, ScalarFrame.loaded_of_frame pre whole, rip, ?_, ?_, ?_,
    (entry.agrees.trans body).trans stores, whole⟩
  · exact (stores.read (n := 64) (r := 4) (by simp)).trans
      ((body.read (n := 64) (r := 4) (by simp [registers])).trans entry.rsp)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    all_goals rw [read _ (by decide), entry.memory]
    all_goals simp only [prologueMemory, sources, pushSequenceMemory, BitVec.ofNat_eq_ofNat,
      Nat.reduceAdd, BitVec.sub_eq_add_neg]
    all_goals repeat first
      | rw [memLoad_memStore_apart _ (stackPtr s) _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _
  · have h := read 0 (by decide)
    simp only [BitVec.sub_zero] at h
    rw [h, entry.memory]
    simp only [prologueMemory, sources, pushSequenceMemory, BitVec.ofNat_eq_ofNat,
      Nat.reduceAdd, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    rfl

end P256.Proofs.Field.Decode.Wrapper
