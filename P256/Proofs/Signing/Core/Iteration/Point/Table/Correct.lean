import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry2
import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry3
import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry4
import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry5
import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry6
import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry7
import P256.Proofs.Signing.Core.Iteration.Point.Table.Entry8

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Basepoint (basePoint)

structure Prepared [Bindings] (s t : RamState) : Prop where
  frame : Frame s t
  registers : Registers s t 304
  table : Projective.Multiply.Machine.Lookup.TableAt t (frameBase s+528) (Projective.table basePoint)

theorem table_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (input : Input s t nonce) (rip : t.RIP = 0x10cd5b) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cf35 ∧
      Prepared s u ∧ Preserved s t u := by
  obtain ⟨n0,t0,run0,rip0,st0,keep0⟩ := initialize_correct pre input rip
  have regs0 : Registers s t0 304 :=
    ⟨st0.rbp,st0.r13,st0.r15,st0.rbx⟩
  have entries0 : Prefix s t0 1 := by
    intro i hi
    have zero : i = 0 := by omega
    subst i
    exact st0.first
  obtain ⟨n1,t1,run1,rip1,f1,r1,p1,rax1,keep1⟩ :=
    entry2_correct pre st0.frame regs0 entries0 st0.temporary rip0
  obtain ⟨n2,t2,run2,rip2,f2,r2,p2,rax2,keep2⟩ := entry3_correct pre f1 r1 p1 rax1 rip1
  obtain ⟨n3,t3,run3,rip3,f3,r3,p3,rax3,keep3⟩ := entry4_correct pre f2 r2 p2 rax2 rip2
  obtain ⟨n4,t4,run4,rip4,f4,r4,p4,rax4,keep4⟩ := entry5_correct pre f3 r3 p3 rax3 rip3
  obtain ⟨n5,t5,run5,rip5,f5,r5,p5,rax5,keep5⟩ := entry6_correct pre f4 r4 p4 rax4 rip4
  obtain ⟨n6,t6,run6,rip6,f6,r6,p6,rax6,keep6⟩ := entry7_correct pre f5 r5 p5 rax5 rip5
  obtain ⟨n7,t7,run7,rip7,f7,r7,p7,keep7⟩ := entry8_correct pre f6 r6 p6 rax6 rip6
  refine ⟨_,t7,((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7,
    rip7,⟨f7,r7,?_⟩,
    ((((((keep0.trans keep1).trans keep2).trans keep3).trans keep4).trans keep5).trans keep6).trans keep7⟩
  intro index
  simpa only [Projective.table,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using p7 index.val index.isLt

end P256.Proofs.Signing.Core.Iteration.Point.Table
