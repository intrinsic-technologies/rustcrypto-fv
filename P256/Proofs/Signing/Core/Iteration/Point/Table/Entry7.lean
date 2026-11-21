import P256.Proofs.Signing.Core.Iteration.Point.Table.Memory
import P256.Proofs.Signing.Core.Iteration.Point.Table.Sites
import P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
import P256.Proofs.Signing.Core.Iteration.Point.Table.Initialize

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Basepoint (basePoint register_block)
open NextNonce (scalarFrame coreFrame base_add)
open Blocks

set_option maxHeartbeats 600000 in
theorem entry7_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t)
    (regs : Registers s t 304) (entries : Prefix s t 6)
    (source : t.regValue .rax = frameBase s+1008)
    (rip : t.RIP = 0x10ceb6) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cef7 ∧
      Frame s u ∧ Registers s u 304 ∧ Prefix s u 7 ∧
      u.regValue .rax = frameBase s+1104 ∧
      Preserved s t u := by
  obtain ⟨n1,t1,run1,sf1,ef1,mem1⟩ := register_block (offset := 0xceb6)
    (scalarFrame frame) (b101181_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip
    (by simp [b101181Effect,Effect.components,Component.Covers])
    (by simp [b101181Effect,Effect.components]) (by simp [b101181Effect,Effect.components])
    (by simp [b101181Effect,Effect.components]) (by simp [b101181Effect,Effect.components])
  have f1 := coreFrame sf1
  have r1 := regs.agrees ef1.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101181Effect,Effect.components])
  have p1 := entries.of_external mem1
  have keep1 : Preserved s t t1 := by intro i hi; rw [mem1]
  have src1 : t1.regValue .rax = frameBase s+1008 :=
    (ef1.agrees.read (n := 64) (r := 0) (by simp [b101181Effect,Effect.components])).trans source
  obtain ⟨t2,run2,f2,rip2,temp2,ag2⟩ := copy_generator pre f1
    0xcec5 (by decide) (by decide +kernel) ef1.rip 1328 (by decide)
    (ef1.writes.2.1.trans regs.r15) ef1.writes.1 ef1.writes.2.2
  have r2 := r1.agrees ag2 (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl|rfl <;> simp [copyComponents])
  have p2 := p1.copy ag2 (by decide) (by decide) (.inr (by decide))
  have keep2 : Preserved s t1 t2 := copy_preserved ag2 (by decide) (by intro i hi; rcases hi with h|h|h|h <;> omega)
  have src2 : t2.regValue .rax = frameBase s+1008 := (ag2.read (n := 64) (r := 0) (by simp [copyComponents])).trans src1
  obtain ⟨n3,t3,run3,sf3,ef3,mem3⟩ := register_block (offset := 0xcec8)
    (scalarFrame f2) (b101193_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip2
    (by simp [b101193Effect,Effect.components,Component.Covers])
    (by simp [b101193Effect,Effect.components]) (by simp [b101193Effect,Effect.components])
    (by simp [b101193Effect,Effect.components]) (by simp [b101193Effect,Effect.components])
  have f3 := coreFrame sf3
  have r3 := r2.agrees ef3.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101193Effect,Effect.components])
  have p3 := p2.of_external mem3
  have keep3 : Preserved s t2 t3 := by intro i hi; rw [mem3]
  have temp3 : ProjectiveAt t3 (frameBase s+1328) basePoint := temp2.of_bytes_eq (by intro i hi; rw [mem3] <;> rfl)
  have sourceAt : ProjectiveAt t3 (frameBase s+1008) (Projective.tableEntry basePoint 5) := p3 5 (by decide)
  obtain ⟨t4,res4⟩ := add_stack pre f3 add101199 ef3.rip (ef3.writes.1.trans r2.r15) (ef3.writes.2.trans src2) (by decide) temp3 sourceAt
  obtain ⟨n4,run4⟩ := res4.execution
  have f4 := coreFrame res4.toFrameState
  have r4 := r3.preserve res4.registers
  have p4 := p3.call (by decide) res4
  have keep4 := call_preserved res4
  have value4 : ProjectiveAt t4 (frameBase s+1328) (Projective.tableEntry basePoint 6) := by
    have address : frameBase s+1328 = stackPtr s-952 := base_add s (offset := 1328) (by decide)
    rw [address]; exact res4.value
  obtain ⟨n5,t5,run5,sf5,ef5,mem5⟩ := register_block (offset := 0xced3)
    (scalarFrame f4) (b10119e_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) res4.rip
    (by simp [b10119eEffect,Effect.components,Component.Covers])
    (by simp [b10119eEffect,Effect.components]) (by simp [b10119eEffect,Effect.components])
    (by simp [b10119eEffect,Effect.components]) (by simp [b10119eEffect,Effect.components])
  have f5 := coreFrame sf5
  have r5 := r4.agrees ef5.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b10119eEffect,Effect.components])
  have p5 := p4.of_external mem5
  have keep5 : Preserved s t4 t5 := by intro i hi; rw [mem5]
  have value5 : ProjectiveAt t5 (frameBase s+1328) (Projective.tableEntry basePoint 6) := value4.of_bytes_eq (by intro i hi; rw [mem5] <;> rfl)
  obtain ⟨t6,run6,f6,rip6,value6,ag6⟩ := copy_stack pre f5
    0xcede (by decide) (by decide +kernel) ef5.rip 432 (by decide)
    (ef5.writes.2.1.trans r4.r13) ef5.writes.1 (by decide) (by decide) (ef5.writes.2.2.trans r4.r15) value5
  have r6 := r5.agrees ag6 (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl|rfl <;> simp [copyComponents])
  have p6 := p5.copy ag6 (by decide) (by decide) (by decide)
  have keep6 : Preserved s t5 t6 := copy_preserved ag6 (by decide) (by intro i hi; rcases hi with h|h|h|h <;> omega)
  obtain ⟨n7,t7,run7,sf7,ef7,mem7⟩ := register_block (offset := 0xcee1)
    (scalarFrame f6) (b1011ac_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip6
    (by simp [b1011acEffect,Effect.components,Component.Covers])
    (by simp [b1011acEffect,Effect.components]) (by simp [b1011acEffect,Effect.components])
    (by simp [b1011acEffect,Effect.components]) (by simp [b1011acEffect,Effect.components])
  have f7 := coreFrame sf7
  have r7 := r6.agrees ef7.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b1011acEffect,Effect.components])
  have p7 := p6.of_external mem7
  have keep7 : Preserved s t6 t7 := by intro i hi; rw [mem7]
  have value7 : ProjectiveAt t7 (frameBase s+432) (Projective.tableEntry basePoint 6) := value6.of_bytes_eq (by intro i hi; rw [mem7] <;> rfl)
  obtain ⟨t8,run8,f8,rip8,value8,ag8⟩ := copy_stack pre f7
    0xcef4 (by decide) (by decide +kernel) ef7.rip 1104 (by decide)
    (ef7.writes.2.2.1.trans (congrArg (·+1104) f6.rsp)) ef7.writes.1 (by decide) (by decide) (ef7.writes.2.2.2.trans r6.r13) value7
  have r8 := r7.agrees ag8 (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl|rfl <;> simp [copyComponents])
  have p8 := p7.copy ag8 (by decide) (by decide) (by decide)
  have keep8 : Preserved s t7 t8 := copy_preserved ag8 (by decide) (by intro i hi; rcases hi with h|h|h|h <;> omega)
  have rax8 : t8.regValue .rax = frameBase s+1104 := (ag8.read (n := 64) (r := 0) (by simp [copyComponents])).trans (ef7.writes.2.1.trans (congrArg (·+1104) f6.rsp))
  exact ⟨_,t8,(((((((run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8,rip8,f8,r8,p8.append value8,rax8,(((((((keep1).trans keep2).trans keep3).trans keep4).trans keep5).trans keep6).trans keep7).trans keep8⟩

end P256.Proofs.Signing.Core.Iteration.Point.Table
