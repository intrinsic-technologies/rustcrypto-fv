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
theorem entry2_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t)
    (regs : Registers s t 304) (entries : Prefix s t 1)
    (temporary : ProjectiveAt t (frameBase s+1328) basePoint)
    (rip : t.RIP = 0x10cd7f) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cdb2 ∧
      Frame s u ∧ Registers s u 304 ∧ Prefix s u 2 ∧
      u.regValue .rax = frameBase s+624 ∧
      Preserved s t u := by
  obtain ⟨n1,t1,run1,sf1,ef1,mem1⟩ := register_block (offset := 0xcd7f)
    (scalarFrame frame) (b10105a_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip
    (by simp [b10105aEffect,Effect.components,Component.Covers])
    (by simp [b10105aEffect,Effect.components]) (by simp [b10105aEffect,Effect.components])
    (by simp [b10105aEffect,Effect.components]) (by simp [b10105aEffect,Effect.components])
  have f1 := coreFrame sf1
  have r1 := regs.agrees ef1.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b10105aEffect,Effect.components])
  have p1 := entries.of_external mem1
  have keep1 : Preserved s t t1 := by intro i hi; rw [mem1]
  have temp1 : ProjectiveAt t1 (frameBase s+1328) basePoint := temporary.of_bytes_eq (by intro i hi; rw [mem1] <;> rfl)
  obtain ⟨t2,res2⟩ := add_generator pre f1 add101064 ef1.rip (ef1.writes.1.trans regs.r15) ef1.writes.2 temp1
  obtain ⟨n2,run2⟩ := res2.execution
  have f2 := coreFrame res2.toFrameState
  have r2 := r1.preserve res2.registers
  have p2 := p1.call (by decide) res2
  have keep2 := call_preserved res2
  have value2 : ProjectiveAt t2 (frameBase s+1328) (Projective.tableEntry basePoint 1) := by
    have address : frameBase s+1328 = stackPtr s-952 := base_add s (offset := 1328) (by decide)
    rw [address]; exact res2.value
  obtain ⟨n3,t3,run3,sf3,ef3,mem3⟩ := register_block (offset := 0xcd8e)
    (scalarFrame f2) (b101069_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) res2.rip
    (by simp [b101069Effect,Effect.components,Component.Covers])
    (by simp [b101069Effect,Effect.components]) (by simp [b101069Effect,Effect.components])
    (by simp [b101069Effect,Effect.components]) (by simp [b101069Effect,Effect.components])
  have f3 := coreFrame sf3
  have r3 := r2.agrees ef3.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101069Effect,Effect.components])
  have p3 := p2.of_external mem3
  have keep3 : Preserved s t2 t3 := by intro i hi; rw [mem3]
  have value3 : ProjectiveAt t3 (frameBase s+1328) (Projective.tableEntry basePoint 1) := value2.of_bytes_eq (by intro i hi; rw [mem3] <;> rfl)
  obtain ⟨t4,run4,f4,rip4,value4,ag4⟩ := copy_stack pre f3
    0xcd99 (by decide) (by decide +kernel) ef3.rip 432 (by decide)
    (ef3.writes.2.1.trans r2.r13) ef3.writes.1 (by decide) (by decide) (ef3.writes.2.2.trans r2.r15) value3
  have r4 := r3.agrees ag4 (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl|rfl <;> simp [copyComponents])
  have p4 := p3.copy ag4 (by decide) (by decide) (by decide)
  have keep4 : Preserved s t3 t4 := copy_preserved ag4 (by decide) (by intro i hi; rcases hi with h|h|h|h <;> omega)
  obtain ⟨n5,t5,run5,sf5,ef5,mem5⟩ := register_block (offset := 0xcd9c)
    (scalarFrame f4) (b101077_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip4
    (by simp [b101077Effect,Effect.components,Component.Covers])
    (by simp [b101077Effect,Effect.components]) (by simp [b101077Effect,Effect.components])
    (by simp [b101077Effect,Effect.components]) (by simp [b101077Effect,Effect.components])
  have f5 := coreFrame sf5
  have r5 := r4.agrees ef5.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101077Effect,Effect.components])
  have p5 := p4.of_external mem5
  have keep5 : Preserved s t4 t5 := by intro i hi; rw [mem5]
  have value5 : ProjectiveAt t5 (frameBase s+432) (Projective.tableEntry basePoint 1) := value4.of_bytes_eq (by intro i hi; rw [mem5] <;> rfl)
  obtain ⟨t6,run6,f6,rip6,value6,ag6⟩ := copy_stack pre f5
    0xcdaf (by decide) (by decide +kernel) ef5.rip 624 (by decide)
    (ef5.writes.2.2.1.trans (congrArg (·+624) f4.rsp)) ef5.writes.1 (by decide) (by decide) (ef5.writes.2.2.2.trans r4.r13) value5
  have r6 := r5.agrees ag6 (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl|rfl <;> simp [copyComponents])
  have p6 := p5.copy ag6 (by decide) (by decide) (by decide)
  have keep6 : Preserved s t5 t6 := copy_preserved ag6 (by decide) (by intro i hi; rcases hi with h|h|h|h <;> omega)
  have rax6 : t6.regValue .rax = frameBase s+624 := (ag6.read (n := 64) (r := 0) (by simp [copyComponents])).trans (ef5.writes.2.1.trans (congrArg (·+624) f4.rsp))
  exact ⟨_,t6,(((((run1).trans run2).trans run3).trans run4).trans run5).trans run6,rip6,f6,r6,p6.append value6,rax6,(((((keep1).trans keep2).trans keep3).trans keep4).trans keep5).trans keep6⟩

end P256.Proofs.Signing.Core.Iteration.Point.Table
