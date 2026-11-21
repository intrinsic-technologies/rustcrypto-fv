import P256.Proofs.Verifying.Core.Initialize
import P256.Proofs.Verifying.Core.Prepare.FirstCheck.Correct
import P256.Proofs.Verifying.Core.Prepare.Nonzero

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

structure Pointers (s t : RamState) : Prop where
  signature : t.regValue .rbx = s.regValue .r8

set_option maxHeartbeats 1000000 in
theorem first [Bindings] {s entry : RamState} {boundary : ReturnBoundary} {r : Nat}
    (pre : Core.Pre s boundary) (frame : Frame s entry) (rip : entry.RIP = 0x10da4d)
    (signature : memLoad entry.external (frameBase s+464) 64 = s.regValue .r8)
    (input : Nat256At entry (s.regValue .r8) r)
    (positive : 0 < r) :
    ∃ n t, Advances boundary n entry t ∧ Frame s t ∧ t.RIP = 0x10dad2 ∧
      Pointers s t ∧ MemoryWriteFrame entry t (prefixRegions s) := by
  obtain ⟨n,a,ha,sa,memA,ga⟩ := initialize_full pre frame rip signature
  have ma : MemoryWriteFrame entry a (prefixRegions s) := by
    intro addr _
    exact congrArg (fun ram => ram[addr]?) memA
  have va : Nat256At a (s.regValue .r8) r := by
    have h := signature_nat256 pre (offset := 0) (by decide) (prefix_memory_stack pre ma)
      (by simpa only [BitVec.add_zero] using input)
    simpa only [BitVec.add_zero] using h
  obtain ⟨m,b,hb,sb,eb,vb,zb⟩ := FirstCheck.setup pre sa.toFrameState sa.rip sa.signature va
  have db : b.regValue .rdi = stackPtr s-1176 := by
    have h : b.regValue .rdi = rspOf a+0 := eb.writes.2.2.1
    change b.regValue .rdi = stackPtr a+0#64 at h
    simpa only [BitVec.add_zero,sa.rsp] using h
  have ib : b.regValue .rsi = stackPtr s-1048 := by
    have h : b.regValue .rsi = rspOf a+128 := eb.writes.2.2.2.1
    change b.regValue .rsi = stackPtr a+128#64 at h
    rw [h,sa.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have mb : MemoryWriteFrame a b (prefixRegions s) := eb.agrees.memoryWriteFrame (by
    intro c hc addr covered
    simp only [FirstCheck.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals exact prefix_local_contains pre sa.toFrameState (by decide) covered)
  obtain ⟨k,t,ht,st,ipt,gt⟩ := nonzero pre sb false eb.rip vb zb db ib positive
  have mt : MemoryWriteFrame b t (prefixRegions s) := gt.memoryWriteFrame (by
    intro c hc addr covered
    simp only [nonzeroClobbers,compareClobbers,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) | rfl
    all_goals try exact covered.elim
    all_goals try exact prefix_stack_contains pre (by decide) (by decide) covered
    have address : frameBase s+128#64 = stackPtr s-1048 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    change (Component.mem (frameBase s+128#64) 1).Covers addr at covered
    rw [address] at covered
    exact prefix_stack_contains pre (by decide) (by decide) covered)
  have signatureT : t.regValue .rbx = a.regValue .rbx :=
    (eb.agrees.trans gt).read (n := 64) (r := 3)
      (by simp [FirstCheck.effect,Effect.components,nonzeroClobbers,compareClobbers])
  refine ⟨n+m+k,t,(ha.trans hb).trans ht,st,ipt,?_,
    memoryWriteFrame_trans (memoryWriteFrame_trans ma mb) mt⟩
  exact ⟨signatureT.trans sa.signature⟩

end P256.Proofs.Verifying.Core.Prepare
