import P256.Proofs.Verifying.Core.Prepare.Pointers
import P256.Proofs.Verifying.Core.Prepare.PreserveR
import P256.Proofs.Verifying.Core.Prepare.CopyR.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

set_option maxHeartbeats 1400000 in
theorem signature_scalars [Bindings] {s entry : RamState} {boundary : ReturnBoundary} {r scalarS : Nat}
    (pre : Core.Pre s boundary) (frame : Frame s entry) (rip : entry.RIP = 0x10da4d)
    (signature : memLoad entry.external (frameBase s+464) 64 = s.regValue .r8)
    (inputR : Nat256At entry (s.regValue .r8) r)
    (inputS : Nat256At entry (s.regValue .r8+32#64) scalarS)
    (rPositive : 0 < r) (sPositive : 0 < scalarS) :
    ∃ n t, Advances boundary n entry t ∧ Frame s t ∧ t.RIP = 0x10dbb2 ∧
      Pointers s t ∧ Nat256At t (stackPtr s-472#64) r ∧
      Nat256At t (stackPtr s-440#64) scalarS ∧
      MemoryWriteFrame entry t (prefixRegions s) := by
  obtain ⟨n,a,ha,sa,ipa,pa,ma⟩ := first pre frame rip signature inputR rPositive
  have ar : Nat256At a (s.regValue .r8) r := by
    have h := signature_nat256 pre (offset := 0) (by decide) (prefix_memory_stack pre ma)
      (by simpa only [BitVec.add_zero] using inputR)
    simpa only [BitVec.add_zero] using h
  obtain ⟨m,b,hb,sb,eb,br,_⟩ := CopyR.copy pre sa ipa pa.signature ar
  have pb := pa.after eb.agrees (by simp [CopyR.Block.effect,Effect.components])
  have mb := eb.agrees.memoryWriteFrame (show WritesWithin (CopyR.Block.effect a).components (prefixRegions s) from by
    intro c hc addr covered
    simp only [CopyR.Block.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals exact prefix_local_contains pre sa (by decide) covered)
  have bm := memoryWriteFrame_trans ma mb
  have bs : Nat256At b (s.regValue .r8+32#64) scalarS :=
    signature_nat256 pre (by decide) (prefix_memory_stack pre bm) inputS
  obtain ⟨k,c,hc,sc,ec,cs,cz⟩ := SecondCheck.setup pre sb eb.rip pb.signature bs
  have pc := pb.after ec.agrees (by simp [SecondCheck.Block.effect,Effect.components])
  have di : c.regValue .rdi = stackPtr s-1176 := by
    have h : c.regValue .rdi = stackPtr b+0#64 := ec.writes.2.2.2.1
    simpa only [BitVec.add_zero,sb.rsp] using h
  have si : c.regValue .rsi = stackPtr s-1048 := by
    have h : c.regValue .rsi = stackPtr b+128#64 := ec.writes.2.2.1
    rw [h,sb.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have mc : MemoryWriteFrame b c (prefixRegions s) :=
    ec.agrees.memoryWriteFrame (by
      intro component hin addr covered
      simp only [SecondCheck.Block.effect,Effect.components,List.map_cons,List.map_nil,
        Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
        List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals try exact covered.elim
      all_goals exact prefix_local_contains pre sb (by decide) covered)
  have cr := second_check_r pre sb ec br
  obtain ⟨l,d,hd,sd,ipd,gd⟩ := nonzero pre sc true ec.rip cs cz di si sPositive
  have pd := pc.after gd (by simp [nonzeroClobbers,compareClobbers])
  have md : MemoryWriteFrame c d (prefixRegions s) := gd.memoryWriteFrame (by
    intro component hin addr covered
    simp only [nonzeroClobbers,compareClobbers,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hin
    rcases hin with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) | rfl
    all_goals try exact covered.elim
    all_goals try exact prefix_stack_contains pre (by decide) (by decide) covered
    have address : frameBase s+128#64 = stackPtr s-1048 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    change (Component.mem (frameBase s+128#64) 1).Covers addr at covered
    rw [address] at covered
    exact prefix_stack_contains pre (by decide) (by decide) covered)
  have dr := nonzero_r pre gd cr
  have dm := memoryWriteFrame_trans (memoryWriteFrame_trans bm mc) md
  have ds : Nat256At d (s.regValue .r8+32#64) scalarS :=
    signature_nat256 pre (by decide) (prefix_memory_stack pre dm) inputS
  obtain ⟨q,t,ht,st,et,ts,_⟩ := CopyS.copy pre sd ipd pd.signature ds
  have mt := et.agrees.memoryWriteFrame (show WritesWithin (CopyS.Block.effect d).components (prefixRegions s) from by
    intro c hc addr covered
    simp only [CopyS.Block.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals exact prefix_local_contains pre sd (by decide) covered)
  have pt := pd.after et.agrees (by simp [CopyS.Block.effect,Effect.components])
  exact ⟨n+m+k+l+q,t,(((ha.trans hb).trans hc).trans hd).trans ht,
    st,et.rip,pt,copy_s_r pre sd et dr,ts,memoryWriteFrame_trans dm mt⟩

end P256.Proofs.Verifying.Core.Prepare
