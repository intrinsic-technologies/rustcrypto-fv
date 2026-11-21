import P256.Proofs.Sec1Serialize.Conversion.Stage

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

theorem savedInput_compress_apart (s : RamState) (i : Nat) (hi : i < 4) :
    ¬ Component.Covers (.mem (stackPtr s - 192) 8)
      (stackPtr s - 300 + BitVec.ofNat 64 i) := by
  rintro ⟨j, hj, hje⟩
  apply OffsetsApart.ne (c₁ := -192) (len₁ := 8) (c₂ := -300) (len₂ := 4)
    (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide +kernel)
  simpa only [BitVec.sub_eq_add_neg] using hje.symm

theorem save_input_pointer_mode [Bindings] {s start t : RamState} {boundary : ReturnBoundary} {mode : BitVec 32}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s start t boundary) (rip : t.RIP = 0x110f80)
    (compress : (Operand.mem (stackPtr s - 300) : Operand 32).read t = mode) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110f85 ∧
      AgreesExcept [.mem (stackPtr s - 192) 8, .rip] t u ∧
      (Operand.mem (stackPtr s - 192) : Operand 64).read u = t.regValue .r14 ∧
      (Operand.mem (stackPtr s - 300) : Operand 32).read u = mode := by
  let am : AddrMode := .sib 4 none 0 (.d8 120)
  have address : storeAddrAt 0x110f80 am (3 + am.tail.length) t = stackPtr s - 192 := by
    change stackPtr t + 120 = stackPtr s - 192
    exact scalar_stack_address (frameOffset := 312) stage.rsp (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 192) 8 := by
    apply writable_of_grow (s := s) _ stage.allocated
    apply stack_sub_writable pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
      (offset := 192) (by decide) (by decide) (by decide)
    rw [stack_sub_toNat pre.stack (offset := 192) (by decide)]
    have hs : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
    have hn := (stack_bounds pre.stack).1
    have ha : ((stackPtr s).toNat - 192) % 8 = 0 := by omega
    have hm := Nat.mod_mod_of_dvd ((stackPtr s).toNat - 192) (show 8 ∣ 4096 by decide)
    omega
  have apart : RangeApart (stackPtr s - 192) 8 0x110f80 5 := by
    have h := stack_code pre stage.toFrameState (offset := 120) (len := 8)
      (codeOffset := 0x10f80) (codeLen := 5) (by decide) (by decide) (by decide)
    rw [scalar_stack_address (frameOffset := 312) stage.rsp (by decide) (by decide)] at h
    exact h
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step 0x110f80 0x4c (by simp [RexWPrefix]) 6 am
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      stage.ready
      (programText_slice (programLoaded_codeIn stage.loaded) 0x10f80 _
        (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸ apart⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10f85 (by decide)))
  have frame : AgreesExcept [.mem (stackPtr s - 192) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components, address] at h
    exact h
  have writes : WritesWithin [.mem (stackPtr s - 192) 8, .rip]
      #v[registerRegion s .rdi 65, workRegion s 328] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨workRegion s 328, by simp, work_contains pre (by decide) (by decide) ha⟩
    · exact ha.elim
  obtain ⟨fuel, execution⟩ := stage.execution
  have state := stage.toFrameState.after_effect pre (by decide) ready frame writes (by simp)
  refine ⟨u, ⟨state, fuel + 1, execution.trans run⟩, effect.rip, frame, ?_, ?_⟩
  · have h := effect.writes
    change (Operand.mem (storeAddrAt 0x110f80 am (3 + am.tail.length) t) : Operand 64).read u =
      t.regValue .r14 at h
    rwa [address] at h
  · change (Operand.mem (stackPtr s - 300) : Operand 32).read u = mode
    rw [read_mem_of_agrees frame]
    · exact compress
    · intro i hi c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact savedInput_compress_apart s i hi
      · exact id

theorem save_input_pointer [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s start t boundary) (rip : t.RIP = 0x110f80)
    (compress : compressionFlag s t) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110f85 ∧
      AgreesExcept [.mem (stackPtr s - 192) 8, .rip] t u ∧
      (Operand.mem (stackPtr s - 192) : Operand 64).read u = t.regValue .r14 ∧
      compressionFlag s u :=
  save_input_pointer_mode pre stage rip compress

end P256.Proofs.Sec1Serialize.Conversion
