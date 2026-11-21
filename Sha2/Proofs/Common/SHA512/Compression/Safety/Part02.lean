import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part02

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
theorem part02 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block):
    Certificate initial Decoded.part02 before02 after02 positions02 := by
  unfold Decoded.part02 before02 after02 positions02
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56915 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56919 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 56922 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56925 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 56928 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 56931 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56934 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56937 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56940 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 336 ?_ (fun _ => rfl) (text_inside 56948 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 336) 8
        rw [rspEq]
        exact frame_writable8 pre 336 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 336 8 124 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 56951 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 56954 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56957 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56961 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 56964 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56967 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56971 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56974 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56977 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56981 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56984 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56987 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56990 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56993 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56996 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56999 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 328 ?_ (fun _ => rfl) (text_inside 57007 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 328) 8
        rw [rspEq]
        exact frame_writable8 pre 328 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 328 8 183 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 57010 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl) (text_inside 57014 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105586 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 32) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 32 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 57017 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57021 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105593 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 40) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 40 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 24 ?_ (fun _ => rfl) (text_inside 57026 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 24) 8
        rw [rspEq]
        exact frame_writable8 pre 24 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 24 8 205 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 57029 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57033 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105605 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 48) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 48 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 32 ?_ (fun _ => rfl) (text_inside 57038 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 32) 8
        rw [rspEq]
        exact frame_writable8 pre 32 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 32 8 217 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57042 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105614 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 56) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 56 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 48 ?_ (fun _ => rfl) (text_inside 57047 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 48) 8
        rw [rspEq]
        exact frame_writable8 pre 48 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 48 8 226 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57051 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105623 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 64) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 64 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 104 ?_ (fun _ => rfl) (text_inside 57056 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 104) 8
        rw [rspEq]
        exact frame_writable8 pre 104 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 104 8 235 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57060 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105632 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 72) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 72 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 8 ?_ (fun _ => rfl) (text_inside 57065 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 8) 8
        rw [rspEq]
        exact frame_writable8 pre 8 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 8 8 244 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57069 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105641 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 80) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 80 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 16 ?_ (fun _ => rfl) (text_inside 57074 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 16) 8
        rw [rspEq]
        exact frame_writable8 pre 16 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 16 8 253 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57078 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105650 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 88) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 88 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 64 ?_ (fun _ => rfl) (text_inside 57083 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 64) 8
        rw [rspEq]
        exact frame_writable8 pre 64 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 64 8 262 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57087 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105659 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 96) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 96 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 40 ?_ (fun _ => rfl) (text_inside 57092 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 40) 8
        rw [rspEq]
        exact frame_writable8 pre 40 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 40 8 271 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57096 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105668 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 104) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 104 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 88 ?_ (fun _ => rfl) (text_inside 57101 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 88) 8
        rw [rspEq]
        exact frame_writable8 pre 88 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 88 8 280 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57105 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105677 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 112) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 112 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 96 ?_ (fun _ => rfl) (text_inside 57110 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 96) 8
        rw [rspEq]
        exact frame_writable8 pre 96 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 96 8 289 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 57114 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105686 ∧ MemReadable initial ((Operand.reg 6 : Operand 64).read model + 120) 8
      rw [state.pointers 6 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 120 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by change 6 ∈ [6]; simp⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 136 ?_ (fun _ => rfl) (text_inside 57122 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 136) 8
        rw [rspEq]
        exact frame_writable8 pre 136 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 136 8 298 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro hs
      cases hs
  exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
