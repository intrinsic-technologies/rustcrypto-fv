import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Compose
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Lift
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Branch
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false


namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

theorem prepare_swap_compression [Bindings] {s t u : RamState}
    (stage : FrameState s t 65 328 312) (compress : compressionFlag s t)
    (effect : (prepareSwapEffect t).Holds t u) : compressionFlag s u := by
  have haddr : stackPtr s - 300 = rspOf t + 12 := by
    change _ = stackPtr t + 12
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  change (Operand.mem (stackPtr s - 300) : Operand 32).read u = 0
  rw [read_mem_of_agrees effect.agrees]
  · exact compress
  · intro i hi c hc
    rw [haddr]
    simp only [prepareSwapEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    all_goals (
      rintro ⟨j, hj, he⟩
      first
      | exact OffsetsApart.ne (c₁ := 88) (len₁ := 8) (c₂ := 12) (len₂ := 4)
          (by unfold OffsetsApart; decide +kernel) (rspOf t) hj hi (by decide) he.symm
      | exact OffsetsApart.ne (c₁ := 96) (len₁ := 8) (c₂ := 12) (len₂ := 4)
          (by unfold OffsetsApart; decide +kernel) (rspOf t) hj hi (by decide) he.symm
      | exact OffsetsApart.ne (c₁ := 104) (len₁ := 8) (c₂ := 12) (len₂ := 4)
          (by unfold OffsetsApart; decide +kernel) (rspOf t) hj hi (by decide) he.symm
      | exact OffsetsApart.ne (c₁ := 112) (len₁ := 8) (c₂ := 12) (len₂ := 4)
          (by unfold OffsetsApart; decide +kernel) (rspOf t) hj hi (by decide) he.symm)

theorem prepare_encoding_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (state : FrameState s t 65 328 312)
    (rip : t.RIP = 0x110fdc) (compress : compressionFlag s t) :
    ∃ u, FrameState s u 65 328 312 ∧ (∃ fuel, Advances boundary fuel t u) ∧
      (prepareEncodingEffect t).Holds t u := by
  obtain ⟨a, statea, ⟨na, runa⟩, swap⟩ := prepare_swap_stage pre state rip
  obtain ⟨b, stateb, ⟨nb, runb⟩, ripb, branch⟩ := prepare_uncompressed_branch pre statea swap.rip
    (prepare_swap_compression state compress swap)
  obtain ⟨c, statec, ⟨nc, runc⟩, copy⟩ := prepare_copy_stage pre stateb ripb
  obtain ⟨d, stated, ⟨nd, rund⟩, storex⟩ := prepare_storex_stage pre statec copy.rip
  obtain ⟨e, statee, rune, tag⟩ := prepare_tag pre stated storex.rip
  obtain ⟨u, stateu, ⟨nu, runu⟩, storey⟩ := prepare_storey_stage pre statee tag.rip
  exact ⟨u, stateu, ⟨na+nb+nc+nd+1+nu, ((((runa.trans runb).trans runc).trans rund).trans rune).trans runu⟩,
    prepare_compose swap (prepare_branch_holds ripb branch) copy storex tag storey⟩

end P256.Proofs.Sec1Serialize.Prepare
