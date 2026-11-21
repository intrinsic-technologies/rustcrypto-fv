import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Save
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Constants
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks.B10138f

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add)
open Projective.Multiply.Machine.Basepoint (register_block)
open PublicPoint.Normalize.Finish (constant_readable constant_zero)
open P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

structure Prepared [Bindings] (s t : RamState) (x y : Nat) : Prop where
  payload : Payload s t x y 528
  zeroX : Field.MontgomeryAt t (frameBase s+1328) 0
  zeroY : Field.MontgomeryAt t (frameBase s+1360) 0

set_option maxRecDepth 2048 in
theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : SignPre s boundary) (state : Payload s t x y 528) (rip : t.RIP = 0x10d0ab) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d0c5 ∧
      Prepared s u x y ∧ Preserved s t u := by
  obtain ⟨v,run1,ip1,store⟩ := flag pre state.frame rip
  obtain ⟨n,w,run2,sf,ef,mem⟩ := register_block (offset := 0xd0b3)
    (scalarFrame store.frame) (b10138f_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) ip1
    (by simp [b10138fEffect,Effect.components,Component.Covers])
    (by simp [b10138fEffect,Effect.components]) (by simp [b10138fEffect,Effect.components])
    (by simp [b10138fEffect,Effect.components]) (by simp [b10138fEffect,Effect.components])
  have f := coreFrame sf
  have dst : w.regValue .rdi = frameBase s+1328 := ef.writes.2.1.trans
    ((store.agrees.read (n := 64) (r := 15) (by simp)).trans state.registers.r15)
  have src : w.regValue .rsi = 0x2024f0 := ef.writes.2.2
  obtain ⟨u,run3,fu,ip,bytes,ag⟩ := movsq72 pre.toCalleePre sf 0xd0c2 1328
    (by decide) (by decide) (by decide +kernel) ef.rip
    (by rw [dst,f.rsp]; rfl) ef.writes.1
    (by rw [src]; exact constant_readable f.loaded)
    (by rw [src,dst,show frameBase s+1328 = stackPtr s-952 from base_add s (by decide)]
        exact constant_disjoint pre.toCalleePre)
  rw [src,dst] at bytes
  rw [dst] at ag
  have unchanged (i : Nat) (small : i < 2^64) (apart : i < 1328 ∨ 1400 ≤ i) :
      u.external[frameBase s+BitVec.ofNat 64 i]? = v.external[frameBase s+BitVec.ofNat 64 i]? := by
    have h := region_byte ag (s := s) (offset := 1328) (len := 72)
      (by intro c hc a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
          exact ha) (by decide) small apart
    simpa only [mem] using h
  have regs := state.registers.preserve ((store.agrees.trans ef.agrees).trans ag) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp [b10138fEffect,Effect.components])
  refine ⟨1+n+9,u,(run1.trans run2).trans run3,ip,⟨⟨coreFrame fu,regs,?_⟩,?_,?_⟩,?_⟩
  · apply state.point.of_bytes_eq
    intro i hi
    have h := (unchanged (528+i) (by omega) (.inl (by omega))).trans
      (store.unchanged (by decide) (i := 528+i) (by omega) (.inl (by omega)))
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using h
  · apply (constant_zero f.loaded 0 (by decide)).of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using bytes i (by omega)
  · apply (constant_zero f.loaded 32 (by decide)).of_bytes_eq
    intro i hi
    have h := bytes (32+i) (by omega)
    have left : frameBase s+1328+BitVec.ofNat 64 (32+i) = frameBase s+1360+BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add,← BitVec.add_assoc]
      exact congrArg (fun b : BitVec 64 => b+BitVec.ofNat 64 i)
        (by rw [BitVec.add_assoc]; rfl)
    have right : (0x2024f0 : BitVec 64)+BitVec.ofNat 64 (32+i) =
        (0x2024f0+BitVec.ofNat 64 32)+BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
    rw [left,right] at h
    exact h

  · intro i hi
    exact (unchanged i (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega)).trans
      (store.unchanged (by decide) (by rcases hi with h|h|h|h <;> omega)
        (by rcases hi with h|h|h|h <;> omega))

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
