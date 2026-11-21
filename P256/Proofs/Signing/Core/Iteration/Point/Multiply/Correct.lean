import P256.Proofs.Signing.Core.Iteration.Point.Table.Correct
import P256.Proofs.Signing.Core.Iteration.Point.Multiply.Radix
import P256.Proofs.Signing.Core.Iteration.Point.Multiply.Copy
import P256.Proofs.Signing.Core.Iteration.Point.Multiply.Loop

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply Projective.Multiply.Machine
open Projective.Multiply.Machine.Basepoint (basePoint register_block)
open NextNonce (scalarFrame coreFrame)
open SecretKeyFromBytes.Scalar (Nat256At)
open Table.Blocks

structure Multiplied [Bindings] (s t : RamState) (nonce : Nat) : Prop where
  frame : Frame s t
  registers : Table.Registers s t 304
  point : ProjectiveAt t (frameBase s+176) (model basePoint nonce)

theorem table_of_bytes {t u : RamState} {source destination : BitVec 64}
    {points : Fin 8 → Projective} (input : Lookup.TableAt t source points)
    (bytes : ∀ i < 768, u.external[destination+BitVec.ofNat 64 i]? =
      t.external[source+BitVec.ofNat 64 i]?) : Lookup.TableAt u destination points := by
  intro index
  apply (input index).of_bytes_eq
  intro i hi
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using bytes (96*index.val+i)
    (by have := index.isLt; omega)

set_option maxHeartbeats 600000 in
theorem multiply_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (input : Input s t nonce) (rip : t.RIP = 0x10cd5b) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cf6f ∧
      Multiplied s u nonce ∧ Preserved s t u := by
  obtain ⟨n0,t0,run0,rip0,table0,keep0⟩ := Table.table_correct pre input rip
  obtain ⟨n1,t1,run1,sf1,ef1,mem1⟩ := register_block (offset := 0xcf35)
    (scalarFrame table0.frame) (b101200_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip0
    (by simp [b101200Effect,Effect.components,Component.Covers])
    (by simp [b101200Effect,Effect.components]) (by simp [b101200Effect,Effect.components])
    (by simp [b101200Effect,Effect.components]) (by simp [b101200Effect,Effect.components])
  have f1 := coreFrame sf1
  have regs1 := table0.registers.agrees ef1.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101200Effect,Effect.components])
  have scalar1 : Nat256At t1 (frameBase s+304) nonce := by
    refine ⟨input.scalar.1,fun i hi => ?_⟩
    rw [mem1]
    have h := keep0 (304+i) (Or.inr (Or.inl (by omega)))
    have address : frameBase s+BitVec.ofNat 64 (304+i) =
        frameBase s+304+BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    rw [address] at h
    exact h.trans (input.scalar.2 i hi)
  obtain ⟨n2,t2,run2,f2,rip2,digits2,regs2,bytes2⟩ := radix_call pre f1 ef1.rip
    (ef1.writes.2.trans table0.registers.rbx)
    (ef1.writes.1.trans table0.registers.r13) scalar1
  have table2 : Lookup.TableAt t2 (frameBase s+528) (Projective.table basePoint) := by
    apply table_of_bytes table0.table
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat,mem1] using bytes2 528 768 (by decide) (.inr (by decide)) i hi
  have r2 := regs1.preserve regs2
  have keep2 : Preserved s t t2 := by
    intro i hi
    have h := bytes2 i 1 (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) 0 (by decide)
    simp only [BitVec.add_zero,mem1] at h
    exact h.trans (keep0 i hi)
  obtain ⟨n3,t3,run3,sf3,ef3,mem3⟩ := register_block (offset := 0xcf40)
    (scalarFrame f2) (b101210_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip2
    (by simp [b101210Effect,Effect.components,Component.Covers])
    (by simp [b101210Effect,Effect.components]) (by simp [b101210Effect,Effect.components])
    (by simp [b101210Effect,Effect.components]) (by simp [b101210Effect,Effect.components])
  have f3 := coreFrame sf3
  have r3 := r2.agrees ef3.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101210Effect,Effect.components])
  obtain ⟨n4,t4,run4,f4,rip4,copied4,regs4,bytes4⟩ := copy_call pre f3 ef3.rip
    (ef3.writes.2.2.trans r2.rbp) (ef3.writes.2.1.trans r2.r15) ef3.writes.1
  have table4 : Lookup.TableAt t4 (frameBase s+1328) (Projective.table basePoint) := by
    apply table_of_bytes table2
    intro i hi
    rw [copied4 i hi,mem3]
  have digits4 : Bytes t4.external (frameBase s+432) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte nonce i)) := by
    intro i hi
    have h := bytes4 432 65 (by decide) (.inl (by decide)) i hi
    simp only [mem3] at h
    exact h.trans (digits2 i hi)
  have r4 := r3.preserve regs4
  have keep4 : Preserved s t t4 := by
    intro i hi
    have h := bytes4 i 1 (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) 0 (by decide)
    simp only [BitVec.add_zero,mem3] at h
    exact h.trans (keep2 i hi)
  obtain ⟨n5,t5,run5,sf5,ef5,mem5⟩ := register_block (offset := 0xcf51)
    (scalarFrame f4) (b101221_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip4
    (by simp [b101221Effect,Effect.components,Component.Covers])
    (by simp [b101221Effect,Effect.components]) (by simp [b101221Effect,Effect.components])
    (by simp [b101221Effect,Effect.components]) (by simp [b101221Effect,Effect.components])
  have f5 := coreFrame sf5
  have r5 := r4.agrees ef5.agrees (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [b101221Effect,Effect.components])
  have table5 : Lookup.TableAt t5 (frameBase s+1328) (Projective.table basePoint) :=
    table_of_bytes table4 (by intros; rw [mem5])
  have digits5 : Bytes t5.external (frameBase s+432) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte nonce i)) := by
    rw [mem5]
    exact digits4
  obtain ⟨n6,t6,run6,f6,rip6,point6,regs6,bytes6⟩ := loop_call pre f5 ef5.rip
    (ef5.writes.2.2.2.1.trans r4.r15) (ef5.writes.2.2.1.trans (congrArg (·+176) f4.rsp))
    (ef5.writes.2.2.2.2.trans r4.r13) ef5.writes.1 ef5.writes.2.1 table5 digits5
  refine ⟨_,t6,(((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6,
    rip6,⟨f6,r5.preserve regs6,point6⟩,?_⟩
  intro i hi
  have h := bytes6 i 1 (by rcases hi with h|h|h|h <;> omega)
    (by rcases hi with h|h|h|h <;> omega) 0 (by decide)
  simp only [BitVec.add_zero,mem5] at h
  exact h.trans (keep4 i hi)

end P256.Proofs.Signing.Core.Iteration.Point.Multiply
