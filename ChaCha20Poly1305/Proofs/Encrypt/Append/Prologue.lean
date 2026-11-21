import ChaCha20Poly1305.Proofs.Wrapper
import ChaCha20Poly1305.Proofs.Encrypt.Append.Contract
import ChaCha20Poly1305.Proofs.Encrypt.Append.Stack

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def appendPushChanges (s : RamState) : List Component :=
  [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 8) 8, .rip] ++
  [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 16) 8, .rip] ++
  [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 24) 8, .rip] ++
  [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 32) 8, .rip] ++
  [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 40) 8, .rip]

theorem append_prologue [Bindings] {s : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101fb8 ∧ stackPtr t = stackPtr s - BitVec.ofNat 64 40 ∧
      AgreesExcept (appendPushChanges s) s t ∧
      wd t (stackPtr s - BitVec.ofNat 64 8) = rd s 15 ∧
      wd t (stackPtr s - BitVec.ofNat 64 16) = rd s 14 ∧
      wd t (stackPtr s - BitVec.ofNat 64 24) = rd s 12 ∧
      wd t (stackPtr s - BitVec.ofNat 64 32) = rd s 3 := by
  obtain ⟨hroom, htop⟩ := stack_bounds pre.stack
  have hav := pre.separation.2.2 (Stack.region s 48) (by simp)
  have R0 : ReadyToStep s := ReadyToStep.of_supported pre.machine
    pre.environment.smrr pre.environment.memoryType
    (DecoderFeatures.of_supported pre.machine pre.environment.leadingZeroCount)
  have C0 := pre.code
  have G0 : Grows s s := fun _ h => h
  have P1 : pushAddr s = stackPtr s - BitVec.ofNat 64 8 := by
    rfl
  obtain ⟨u1, a1, R1, C1, e1⟩ := stack_push_run pre.stack hav G0
    (k := 8) (by omega) R0 C0
    (program_text_slice C0 0x1fb0 2 (by decide +kernel))
    (push_r64_rex_effect_step 0x101fb0 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
        pre.entry P1
    (code_inProgram 0x1fb0 2 (by omega))
    (code_ne_boundary outside 0x1fb2 (by omega))
  change (pushR64Effect 0x101fb0 2 15 s).Holds s u1 at e1
  have S1 : stackPtr u1 = stackPtr s - BitVec.ofNat 64 8 := by
    exact e1.writes.1.trans P1
  have G1 : Grows s u1 := G0.step e1.agrees
  have P2 : pushAddr u1 = stackPtr s - BitVec.ofNat 64 16 := by
    rw [pushAddr, S1]; bv_omega
  obtain ⟨u2, a2, R2, C2, e2⟩ := stack_push_run pre.stack hav G1
    (k := 16) (by omega) R1 C1
    (program_text_slice C1 0x1fb2 2 (by decide +kernel))
    (push_r64_rex_effect_step 0x101fb2 0x41 0x56 (by unfold RexPrefix; decide) (by decide)) e1.rip
        P2
    (code_inProgram 0x1fb2 2 (by omega))
    (code_ne_boundary outside 0x1fb4 (by omega))
  change (pushR64Effect 0x101fb2 2 14 u1).Holds u1 u2 at e2
  have S2 : stackPtr u2 = stackPtr s - BitVec.ofNat 64 16 := by
    exact e2.writes.1.trans P2
  have G2 : Grows s u2 := G1.step e2.agrees
  have P3 : pushAddr u2 = stackPtr s - BitVec.ofNat 64 24 := by
    rw [pushAddr, S2]; bv_omega
  obtain ⟨u3, a3, R3, C3, e3⟩ := stack_push_run pre.stack hav G2
    (k := 24) (by omega) R2 C2
    (program_text_slice C2 0x1fb4 2 (by decide +kernel))
    (push_r64_rex_effect_step 0x101fb4 0x41 0x54 (by unfold RexPrefix; decide) (by decide)) e2.rip
        P3
    (code_inProgram 0x1fb4 2 (by omega))
    (code_ne_boundary outside 0x1fb6 (by omega))
  change (pushR64Effect 0x101fb4 2 12 u2).Holds u2 u3 at e3
  have S3 : stackPtr u3 = stackPtr s - BitVec.ofNat 64 24 := by
    exact e3.writes.1.trans P3
  have G3 : Grows s u3 := G2.step e3.agrees
  have P4 : pushAddr u3 = stackPtr s - BitVec.ofNat 64 32 := by
    rw [pushAddr, S3]; bv_omega
  obtain ⟨u4, a4, R4, C4, e4⟩ := stack_push_run pre.stack hav G3
    (k := 32) (by omega) R3 C3
    (program_text_slice C3 0x1fb6 1 (by decide +kernel))
    (push_r64_effect_step 0x101fb6 0x53 (by decide)) e3.rip P4
    (code_inProgram 0x1fb6 1 (by omega))
    (code_ne_boundary outside 0x1fb7 (by omega))
  change (pushR64Effect 0x101fb6 1 3 u3).Holds u3 u4 at e4
  have S4 : stackPtr u4 = stackPtr s - BitVec.ofNat 64 32 := by
    exact e4.writes.1.trans P4
  have G4 : Grows s u4 := G3.step e4.agrees
  have P5 : pushAddr u4 = stackPtr s - BitVec.ofNat 64 40 := by
    rw [pushAddr, S4]; bv_omega
  obtain ⟨u5, a5, R5, C5, e5⟩ := stack_push_run pre.stack hav G4
    (k := 40) (by omega) R4 C4
    (program_text_slice C4 0x1fb7 1 (by decide +kernel))
    (push_r64_effect_step 0x101fb7 0x50 (by decide)) e4.rip P5
    (code_inProgram 0x1fb7 1 (by omega))
    (code_ne_boundary outside 0x1fb8 (by omega))
  change (pushR64Effect 0x101fb7 1 0 u4).Holds u4 u5 at e5
  have S5 : stackPtr u5 = stackPtr s - BitVec.ofNat 64 40 := by
    exact e5.writes.1.trans P5
  have all := (((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees
  refine ⟨u5, a1.trans (a2.trans (a3.trans (a4.trans a5))), R5, C5, e5.rip, S5, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [appendPushChanges, pushR64Effect_components, P1, P2, P3, P4, P5, List.append_assoc,
      BitVec.ofNat_eq_ofNat] using all
  · have keep := gload (e2.agrees.trans (e3.agrees.trans (e4.agrees.trans e5.agrees))) (a :=
      stackPtr s - BitVec.ofNat 64 8) (by
      simp only [pushR64Effect_components, P2, P3, P4, P5, List.forall_mem_append,
          List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals intro i hi
      all_goals first
        | exact nonmem_not_covers rfl _
        | (apply mem_not_covers <;>
            simp only [BitVec.toNat_add,
              BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega))
    rw [keep]
    have written : wd u1 (stackPtr s - BitVec.ofNat 64 8) = rd s 15 := by
      have hw : wd u1 (pushAddr s) = rd s 15 := e1.writes.2
      simpa only [P1] using hw
    exact written
  · have keep := gload (e3.agrees.trans (e4.agrees.trans e5.agrees)) (a := stackPtr s - BitVec.ofNat
      64 16) (by
      simp only [pushR64Effect_components, P3, P4, P5, List.forall_mem_append, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals intro i hi
      all_goals first
        | exact nonmem_not_covers rfl _
        | (apply mem_not_covers <;>
            simp only [BitVec.toNat_add,
              BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega))
    rw [keep]
    have written : wd u2 (stackPtr s - BitVec.ofNat 64 16) = rd u1 14 := by
      have hw : wd u2 (pushAddr u1) = rd u1 14 := e2.writes.2
      simpa only [P2] using hw
    rw [written]
    exact e1.agrees.read (by simp)
  · have keep := gload (e4.agrees.trans e5.agrees) (a := stackPtr s - BitVec.ofNat 64 24) (by
      simp only [pushR64Effect_components, P4, P5, List.forall_mem_append, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals intro i hi
      all_goals first
        | exact nonmem_not_covers rfl _
        | (apply mem_not_covers <;>
            simp only [BitVec.toNat_add,
              BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega))
    rw [keep]
    have written : wd u3 (stackPtr s - BitVec.ofNat 64 24) = rd u2 12 := by
      have hw : wd u3 (pushAddr u2) = rd u2 12 := e3.writes.2
      simpa only [P3] using hw
    rw [written]
    exact (e1.agrees.trans e2.agrees).read (by simp)
  · have keep := gload e5.agrees (a := stackPtr s - BitVec.ofNat 64 32) (by
      simp only [pushR64Effect_components, P5, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals intro i hi
      all_goals first
        | exact nonmem_not_covers rfl _
        | (apply mem_not_covers <;>
            simp only [BitVec.toNat_add,
              BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega))
    rw [keep]
    have written : wd u4 (stackPtr s - BitVec.ofNat 64 32) = rd u3 3 := by
      have hw : wd u4 (pushAddr u3) = rd u3 3 := e4.writes.2
      simpa only [P4] using hw
    rw [written]
    exact ((e1.agrees.trans e2.agrees).trans e3.agrees).read (by simp)

theorem append_push_frame {s t : RamState} (hs : Stack.Valid s 48)
    (hag : AgreesExcept (appendPushChanges s) s t) :
    MemoryWriteFrame s t #v[Stack.region s 48] := by
  apply hag.memoryWriteFrame
  intro c hc a hcover
  simp only [appendPushChanges, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  all_goals
    obtain ⟨i, hi, rfl⟩ := hcover
    exact ⟨Stack.region s 48, by simp, stack_slot_contains hs (by omega) (by omega)⟩

end ChaCha20Poly1305.Proofs.Encrypt
