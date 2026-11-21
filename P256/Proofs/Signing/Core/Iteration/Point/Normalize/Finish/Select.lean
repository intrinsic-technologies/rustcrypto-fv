import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Prepare
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks.B1013a1
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks.B1013b4

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add)
open Projective.Multiply.Machine.Basepoint (register_block)
open P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

structure Selected [Bindings] (s t : RamState) (x y : Nat) : Prop where
  frame : Frame s t
  registers : Registers s t
  x : Field.MontgomeryAt t (frameBase s+104) x
  y : Field.MontgomeryAt t (frameBase s+136) y
  tag : t.external[frameBase s+592]? = some 0

theorem select [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : SignPre s boundary) (state : Prepared s t x y) (rip : t.RIP = 0x10d0c5) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d0f8 ∧
      Selected s u x y ∧ Preserved s t u := by
  have f0 := state.payload.frame
  have r0 := state.payload.registers
  obtain ⟨n1,a,run1,sf1,e1,mem1⟩ := register_block (offset := 0xd0c5)
    (scalarFrame f0) (b1013a1_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip
    (by simp [b1013a1Effect,Effect.components,Component.Covers])
    (by simp [b1013a1Effect,Effect.components]) (by simp [b1013a1Effect,Effect.components])
    (by simp [b1013a1Effect,Effect.components]) (by simp [b1013a1Effect,Effect.components])
  have ra := r0.preserve e1.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp [b1013a1Effect,Effect.components])
  have choice1 : (a.regValue .rcx).setWidth 8 = 1 := by
    have h : a.regValue .rcx = ((t.regValue .r12).setWidth 32).setWidth 64 := e1.writes.2.2.2
    rw [h,BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact r0.flag
  obtain ⟨n2,b,run2,sf2,ip2,x2,regs2,bytes2,_⟩ := PublicPoint.Normalize.select_binary_call
    (x := 0) (y := x) (op := fun _ v => v) pre.toCalleePre sf1 xSelectSite
    (fun _ hp hc hx hy => by
      simpa using Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
        (select := true) ((congrArg (BitVec.setWidth 8) hc).trans choice1)) e1.rip
    ((e1.writes.2.1.trans r0.r15).trans (base_add s (by decide)))
    ((e1.writes.2.2.1.trans r0.rbp).trans (base_add s (by decide)))
    ((e1.writes.1.trans (congrArg (·+104) f0.rsp)).trans (base_add s (by decide)))
    (by
      change Field.MontgomeryAt a (stackPtr s-952) 0
      rw [← (show frameBase s+1328 = stackPtr s-952 from base_add s (by decide))]
      exact state.zeroX.of_bytes_eq (by intros; rw [mem1]))
    (by
      change Field.MontgomeryAt a (stackPtr s-1752) x
      rw [← (show frameBase s+528 = stackPtr s-1752 from base_add s (by decide))]
      exact state.payload.point.1.of_bytes_eq (by intros; simp only [mem1,BitVec.ofNat_eq_ofNat]))
  have keep2 := bytes_from_stack (s := s) (output := 104) (lenOut := 32) (by decide) bytes2
  have rb : Registers s b := ⟨(regs2 _ (by simp)).trans ra.rbp,(regs2 _ (by simp)).trans ra.r13,
    (regs2 _ (by simp)).trans ra.r14,(regs2 _ (by simp)).trans ra.r15,
    (congrArg (BitVec.setWidth 8) (regs2 _ (by simp))).trans ra.flag⟩
  obtain ⟨n3,c,run3,sf3,e3,mem3⟩ := register_block (offset := 0xd0d8)
    sf2 (b1013b4_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) ip2
    (by simp [b1013b4Effect,Effect.components,Component.Covers])
    (by simp [b1013b4Effect,Effect.components]) (by simp [b1013b4Effect,Effect.components])
    (by simp [b1013b4Effect,Effect.components]) (by simp [b1013b4Effect,Effect.components])
  have fb := coreFrame sf2
  have rc := rb.preserve e3.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp [b1013b4Effect,Effect.components])
  have choice3 : (c.regValue .rcx).setWidth 8 = 1 := by
    have h : c.regValue .rcx = ((b.regValue .r12).setWidth 32).setWidth 64 := e3.writes.2.2.2
    rw [h,BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact rb.flag
  have y0 : Field.MontgomeryAt t (frameBase s+560) y := by
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using state.payload.point.2.1
  have y3 : Field.MontgomeryAt c (frameBase s+560) y := y0.of_bytes_eq (by
    intro i hi
    simpa only [mem1,mem3,BitVec.ofNat_eq_ofNat] using keep2 560 32 (by decide) (.inr (by decide)) i hi)
  have z3 : Field.MontgomeryAt c (frameBase s+1360) 0 := state.zeroY.of_bytes_eq (by
    intro i hi
    simpa only [mem1,mem3,BitVec.ofNat_eq_ofNat] using keep2 1360 32 (by decide) (.inr (by decide)) i hi)
  obtain ⟨n4,u,run4,sf4,ip4,y4,regs4,bytes4,_⟩ := PublicPoint.Normalize.select_binary_call
    (x := 0) (y := y) (op := fun _ v => v) pre.toCalleePre sf3 ySelectSite
    (fun _ hp hc hx hy => by
      simpa using Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
        (select := true) ((congrArg (BitVec.setWidth 8) hc).trans choice3)) e3.rip
    ((e3.writes.2.1.trans (congrArg (·+1360) fb.rsp)).trans (base_add s (by decide)))
    ((e3.writes.2.2.1.trans (congrArg (·+560) fb.rsp)).trans (base_add s (by decide)))
    ((e3.writes.1.trans (congrArg (·+136) fb.rsp)).trans (base_add s (by decide)))
    (by
      change Field.MontgomeryAt c (stackPtr s-920) 0
      rw [← (show frameBase s+1360 = stackPtr s-920 from base_add s (by decide))]
      exact z3)
    (by
      change Field.MontgomeryAt c (stackPtr s-1720) y
      rw [← (show frameBase s+560 = stackPtr s-1720 from base_add s (by decide))]
      exact y3)
  have keep4 := bytes_from_stack (s := s) (output := 136) (lenOut := 32) (by decide) bytes4
  have ru : Registers s u := ⟨(regs4 _ (by simp)).trans rc.rbp,(regs4 _ (by simp)).trans rc.r13,
    (regs4 _ (by simp)).trans rc.r14,(regs4 _ (by simp)).trans rc.r15,
    (congrArg (BitVec.setWidth 8) (regs4 _ (by simp))).trans rc.flag⟩
  have unchanged (i : Nat) (small : i+1 ≤ 2280) (apart : i < 104 ∨ 168 ≤ i) :
      u.external[frameBase s+BitVec.ofNat 64 i]? = t.external[frameBase s+BitVec.ofNat 64 i]? := by
    have h4 := keep4 i 1 small (by omega) 0 (by decide)
    have h2 := keep2 i 1 small (by omega) 0 (by decide)
    simp only [BitVec.add_zero,mem1,mem3] at h4 h2
    exact h4.trans h2
  refine ⟨n1+n2+n3+n4,u,((run1.trans run2).trans run3).trans run4,ip4,
    ⟨coreFrame sf4,ru,?_,?_,?_⟩,?_⟩
  · have xb : Field.MontgomeryAt b (frameBase s+104) x := by
      rw [show frameBase s+104 = stackPtr s-2176 from base_add s (by decide)]
      exact x2
    exact xb.of_bytes_eq (by intro i hi; simpa only [mem3,BitVec.ofNat_eq_ofNat] using keep4 104 32 (by decide) (.inl (by decide)) i hi)
  · rw [show frameBase s+136 = stackPtr s-2144 from base_add s (by decide)]
    exact y4
  · have tag0 : t.external[frameBase s+592]? = some 0 := by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using state.payload.point.2.2
    exact (unchanged 592 (by decide) (.inr (by decide))).trans tag0
  · intro i hi
    exact unchanged i (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
