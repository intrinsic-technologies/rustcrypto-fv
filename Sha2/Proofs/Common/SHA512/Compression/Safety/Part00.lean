import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part00

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Safety

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem part00 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part00 before00 after00 positions00 := by
  unfold Decoded.part00 before00 after00 positions00
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 176 ?_ (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56824 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 176) 8
        rw [rspEq]
        exact frame_writable8 pre 176 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 176 8 0 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 360 ?_ (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56832 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 360) 8
        rw [rspEq]
        exact frame_writable8 pre 360 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 360 8 8 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 (fun model state => state.rip) (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56835 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    intro model state
    refine ⟨_, rfl, ?_⟩
    intro r hr
    have hr6 : r = 6 := by simpa [positionOf] using hr
    subst r
    exact Or.inr ⟨by decide, by simp [positionOf]⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 (fun model state => state.rip) (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56838 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    intro model state
    refine ⟨_, rfl, ?_⟩
    intro r hr
    have hr6 : r = 6 := by simpa [positionOf] using hr
    subst r
    exact Or.inr ⟨by decide, by simp [positionOf]⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 (fun model state => state.rip) (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56841 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    intro model state
    refine ⟨_, rfl, ?_⟩
    intro r hr
    have hr6 : r = 6 := by simpa [positionOf] using hr
    subst r
    exact Or.inr ⟨by decide, by simp [positionOf]⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 344 ?_ (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56849 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 344) 8
        rw [rspEq]
        exact frame_writable8 pre 344 (by decide) (by decide)
      · simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 344 8 25 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 (fun model state => state.rip) (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56852 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    intro model state
    refine ⟨_, rfl, ?_⟩
    intro r hr
    have hr6 : r = 6 := by simpa [positionOf] using hr
    subst r
    exact Or.inr ⟨by decide, by simp [positionOf]⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 (fun model state => state.rip) (fun _ => rfl)
      (by simpa [positionOf] using text_inside 56855 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    intro model state
    refine ⟨_, rfl, ?_⟩
    intro r hr
    have hr6 : r = 6 := by simpa [positionOf] using hr
    subst r
    exact Or.inr ⟨by decide, by simp [positionOf]⟩
  exact .nil _

end Sha2.Proofs.Common.SHA512.Compression.Safety
