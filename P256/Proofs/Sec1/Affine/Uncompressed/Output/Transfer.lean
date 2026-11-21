import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputX
import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputY

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem transfer_y [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110cc7)
    (output : t.regValue .rbx = s.regValue .rdi)
    (input : Field.MontgomeryAt t (stackPtr s - 632) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110cf7 ∧
      Field.MontgomeryAt u (s.regValue .rdi+32) value ∧
      (outputYEffect t).Holds t u ∧ MemoryWriteFrame t u #v[registerRegion s .rdi 80] := by
  have hp : OutputYPre t := by
    refine ⟨rip,?_,?_,?_,?_⟩
    · intro off member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre state (by decide) (by decide)
    · intro off member
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t
        (t.regValue .rbx+BitVec.ofNat 64 off) 8
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add _ (by decide)
    · intro off member pc len bound
      change RangeApart (t.regValue .rbx+BitVec.ofNat 64 off) 8 _ len
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact (P256.Proofs.Common.Instructions.RangeApart.add_left
        (ScalarFrame.output_code pre.toCalleePre bound) _ (by decide))
    · intro off member stackOff stackMember
      change RangeApart (t.regValue .rbx+BitVec.ofNat 64 off) 8
        (stackPtr t+BitVec.ofNat 64 stackOff) 8
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member stackMember
      rcases member with rfl | rfl | rfl | rfl
      all_goals rcases stackMember with rfl | rfl | rfl | rfl
      all_goals exact output_stack_apart pre state (by decide) (by decide)
  obtain ⟨n,u,run,ready,_,effect⟩ := output_y boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10cc7 outputYBytes
      (by decide) (by decide +kernel)) hp
  have lift (off : Nat) (bound : off+8 ≤ 80) (a : BitVec 64)
      (covered : (Component.mem (t.regValue .rbx+BitVec.ofNat 64 off) 8).Covers a) :
      ∃ r ∈ #v[registerRegion s .rdi 80], r.Contains a.toNat := by
    rw [output] at covered
    exact ⟨_,by simp,ScalarFrame.output_contains pre.toCalleePre bound covered⟩
  have writes : WritesWithin (outputYEffect t).components #v[registerRegion s .rdi 80] := by
    intro c hc a covered
    simp only [outputYEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,Nat.reduceDiv] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    · exact lift 32 (by decide) a covered
    · exact lift 40 (by decide) a covered
    · exact lift 48 (by decide) a covered
    · exact lift 56 (by decide) a covered
  have frame := after_output pre state ready effect.agrees writes
    (by simp [outputYEffect,Effect.components])
  refine ⟨n,u,run,frame,effect.rip,?_,effect,effect.agrees.memoryWriteFrame writes⟩
  have source : stackPtr t+128 = stackPtr s-632 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  apply montgomery_words (source := stackPtr t+128)
  · rwa [source]
  · exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)
  · exact (ScalarFrame.output_writable pre.toCalleePre (by decide) frame.allocated).add 32 (by decide) |>.toMemReadable
  · intro j hj
    have values := effect.writes
    simp only [outputYEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h : memLoad u.external (t.regValue .rbx+32) 64 = memLoad t.external (stackPtr t+128) 64 := values.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h
    · have h : memLoad u.external (t.regValue .rbx+40) 64 = memLoad t.external (stackPtr t+136) 64 := values.2.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h
    · have h : memLoad u.external (t.regValue .rbx+48) 64 = memLoad t.external (stackPtr t+144) 64 := values.2.2.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h
    · have h : memLoad u.external (t.regValue .rbx+56) 64 = memLoad t.external (stackPtr t+152) 64 := values.2.2.2.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h

theorem transfer_x [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110cf7)
    (output : t.regValue .rbx = s.regValue .rdi)
    (input : Field.MontgomeryAt t (stackPtr s - 664) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d1a ∧
      Field.MontgomeryAt u (s.regValue .rdi+0) value ∧
      (outputXEffect t).Holds t u ∧ MemoryWriteFrame t u #v[registerRegion s .rdi 80] := by
  have hp : OutputXPre t := by
    refine ⟨rip,?_,?_,?_,?_⟩
    · intro off member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre state (by decide) (by decide)
    · intro off member
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t
        (t.regValue .rbx+off) 8
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add _ (by decide)
    · intro off member pc len bound
      change RangeApart (t.regValue .rbx+off) 8 _ len
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact (P256.Proofs.Common.Instructions.RangeApart.add_left
        (ScalarFrame.output_code pre.toCalleePre bound) _ (by decide))
    · intro off member stackOff stackMember
      change RangeApart (t.regValue .rbx+off) 8
        (stackPtr t+stackOff) 8
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member stackMember
      rcases member with rfl | rfl | rfl | rfl
      all_goals rcases stackMember with rfl | rfl | rfl | rfl
      all_goals exact output_stack_apart pre state (by decide) (by decide)
  obtain ⟨n,u,run,ready,_,effect⟩ := output_x boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10cf7 outputXBytes
      (by decide) (by decide +kernel)) hp
  have lift (off : Nat) (bound : off+8 ≤ 80) (a : BitVec 64)
      (covered : (Component.mem (t.regValue .rbx+BitVec.ofNat 64 off) 8).Covers a) :
      ∃ r ∈ #v[registerRegion s .rdi 80], r.Contains a.toNat := by
    rw [output] at covered
    exact ⟨_,by simp,ScalarFrame.output_contains pre.toCalleePre bound covered⟩
  have writes : WritesWithin (outputXEffect t).components #v[registerRegion s .rdi 80] := by
    intro c hc a covered
    simp only [outputXEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,Nat.reduceDiv] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    · exact lift 0 (by decide) a covered
    · exact lift 8 (by decide) a covered
    · exact lift 16 (by decide) a covered
    · exact lift 24 (by decide) a covered
  have frame := after_output pre state ready effect.agrees writes
    (by simp [outputXEffect,Effect.components])
  refine ⟨n,u,run,frame,effect.rip,?_,effect,effect.agrees.memoryWriteFrame writes⟩
  have source : stackPtr t+96 = stackPtr s-664 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  apply montgomery_words (source := stackPtr t+96)
  · rwa [source]
  · exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)
  · exact (ScalarFrame.output_writable pre.toCalleePre (by decide) frame.allocated).add 0 (by decide) |>.toMemReadable
  · intro j hj
    have values := effect.writes
    simp only [outputXEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h : memLoad u.external (t.regValue .rbx+0) 64 = memLoad t.external (stackPtr t+96) 64 := values.2.2.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h
    · have h : memLoad u.external (t.regValue .rbx+8) 64 = memLoad t.external (stackPtr t+104) 64 := values.2.2.2.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h
    · have h : memLoad u.external (t.regValue .rbx+16) 64 = memLoad t.external (stackPtr t+112) 64 := values.2.2.2.2.1
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h
    · have h : memLoad u.external (t.regValue .rbx+24) 64 = memLoad t.external (stackPtr t+120) 64 := values.2.2.2.2.2
      rw [output] at h
      simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,
        BitVec.reduceAdd] using h

end P256.Proofs.Sec1.Affine.Uncompressed.Output
