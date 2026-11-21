import P256.Proofs.Signing.Core.Iteration.Point.Copy
import P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Registers

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Basepoint (register_block basePoint)
open NextNonce (scalarFrame coreFrame)
open Blocks

structure Initialized [Bindings] (s t : RamState) : Prop where
  frame : Frame s t
  first : ProjectiveAt t (frameBase s+528) basePoint
  temporary : ProjectiveAt t (frameBase s+1328) basePoint
  rbp : t.regValue .rbp = frameBase s+528
  r13 : t.regValue .r13 = frameBase s+432
  r15 : t.regValue .r15 = frameBase s+1328
  rbx : t.regValue .rbx = frameBase s+304

set_option maxHeartbeats 600000 in
theorem initialize_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (input : Input s t nonce) (rip : t.RIP = 0x10cd5b) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cd7f ∧
      Initialized s u ∧ Preserved s t u := by
  let st0 := input.frame
  have bp0 := input.rbp
  have r120 := input.r13
  have r150 := input.r15
  obtain ⟨n1,v1,run1,sv1,ef1,mem1⟩ := register_block (offset := 0xcd5b)
    (scalarFrame st0) (b100fa3_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip
    (by simp [b100fa3Effect,Effect.components,Component.Covers])
    (by simp [b100fa3Effect,Effect.components]) (by simp [b100fa3Effect,Effect.components])
    (by simp [b100fa3Effect,Effect.components]) (by simp [b100fa3Effect,Effect.components])
  have dst1 : v1.regValue .rdi = frameBase s+528 := by
    exact ef1.writes.2.1.trans bp0
  obtain ⟨t1,copy1,st1,rip1,value1,ag1⟩ := copy_generator pre (coreFrame sv1)
    0xcd6a (by decide) (by decide +kernel) ef1.rip 528 (by decide)
    dst1 ef1.writes.1 ef1.writes.2.2
  have bp1 : t1.regValue .rbp = frameBase s+528 :=
    ((ef1.agrees.trans ag1).read (n := 64) (r := 5)
      (by simp [b100fa3Effect,Effect.components,copyComponents])).trans bp0
  have r121 : t1.regValue .r13 = frameBase s+432 :=
    ((ef1.agrees.trans ag1).read (n := 64) (r := 13)
      (by simp [b100fa3Effect,Effect.components,copyComponents])).trans r120
  have r151 : t1.regValue .r15 = frameBase s+1328 :=
    ((ef1.agrees.trans ag1).read (n := 64) (r := 15)
      (by simp [b100fa3Effect,Effect.components,copyComponents])).trans r150
  have rbx1 : t1.regValue .rbx = frameBase s+304 :=
    ((ef1.agrees.trans ag1).read (n := 64) (r := 3)
      (by simp [b100fa3Effect,Effect.components,copyComponents])).trans input.rbx
  have first1 := value1
  have preserve1 : Preserved s t t1 := by
    intro off live
    have keep := copy_preserved ag1 (by decide)
      (by intro i hi; rcases hi with h|h|h|h <;> omega) off live
    rw [keep,mem1]
  obtain ⟨n8,v8,run8,sv8,ef8,mem8⟩ := register_block (offset := 0xcd6d)
    (scalarFrame st1) (b101048_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip1
    (by simp [b101048Effect,Effect.components,Component.Covers])
    (by simp [b101048Effect,Effect.components]) (by simp [b101048Effect,Effect.components])
    (by simp [b101048Effect,Effect.components]) (by simp [b101048Effect,Effect.components])
  have dst8 : v8.regValue .rdi = frameBase s+1328 := by
    exact ef8.writes.2.1.trans r151
  obtain ⟨t8,copy8,st8,rip8,value8,ag8⟩ := copy_generator pre (coreFrame sv8)
    0xcd7c (by decide) (by decide +kernel) ef8.rip 1328 (by decide)
    dst8 ef8.writes.1 ef8.writes.2.2
  have bp8 : t8.regValue .rbp = frameBase s+528 :=
    ((ef8.agrees.trans ag8).read (n := 64) (r := 5)
      (by simp [b101048Effect,Effect.components,copyComponents])).trans bp1
  have r128 : t8.regValue .r13 = frameBase s+432 :=
    ((ef8.agrees.trans ag8).read (n := 64) (r := 13)
      (by simp [b101048Effect,Effect.components,copyComponents])).trans r121
  have r158 : t8.regValue .r15 = frameBase s+1328 :=
    ((ef8.agrees.trans ag8).read (n := 64) (r := 15)
      (by simp [b101048Effect,Effect.components,copyComponents])).trans r151
  have rbx8 : t8.regValue .rbx = frameBase s+304 :=
    ((ef8.agrees.trans ag8).read (n := 64) (r := 3)
      (by simp [b101048Effect,Effect.components,copyComponents])).trans rbx1
  have first8 : ProjectiveAt t8 (frameBase s+528) basePoint :=
    copy_point (source := 528) ag8 (by decide) (by decide) (.inl (by decide))
      (first1.of_bytes_eq (by intro i hi; rw [mem8] <;> rfl))
  have preserve8 : Preserved s t1 t8 := by
    intro off live
    have keep := copy_preserved ag8 (by decide)
      (by intro i hi; rcases hi with h|h|h|h <;> omega) off live
    rw [keep,mem8]
  exact ⟨_,t8,(run1.trans copy1).trans (run8.trans copy8),rip8,
    ⟨st8,first8,value8,bp8,r128,r158,rbx8⟩,preserve1.trans preserve8⟩

end P256.Proofs.Signing.Core.Iteration.Point.Table
