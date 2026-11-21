import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part24

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
 theorem part24 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block)
    (loaded : ProgramLoaded initial):
    Certificate initial Decoded.part24 before24 after24 positions24 := by
  unfold Decoded.part24 before24 after24 positions24
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60702 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60705 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60709 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60712 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60715 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60718 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60721 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60725 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60728 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60731 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60735 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60738 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 152 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60746 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => by cases h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 152) 8
        rw [rspEq]
        exact frame_writable8 pre 152 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 152 8 3922 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60749 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60753 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => by cases h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 0) 8
        rw [rspEq]
        exact frame_writable8 pre 0 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 0 8 3933 4 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simp only [Disp.value]
        have hz : BitVec.setWidth 64 model.GPR[↑(gprIndex (4 : BitVec 5))] + (0 : BitVec 64) = BitVec.setWidth 64 model.GPR[↑(gprIndex (4 : BitVec 5))] := BitVec.add_zero _
        have hinner : BitVec.setWidth 5 (4 : BitVec 4) = (4 : BitVec 5) := by decide
        rw [hinner]
        rw [hz]
        simpa [BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60756 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60760 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60763 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60766 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60769 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60773 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60776 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60779 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60783 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60786 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60789 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60793 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60796 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60803 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109372 ∧ MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (160)) 8
      have h : MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (160)) 8 := by
        refine ⟨by decide, ?_⟩
        intro i hi
        have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 160 + i) (by omega)
        exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, BitVec.add_assoc] using byte⟩
      exact ⟨state.rip, h⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60806 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60814 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109382 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 128) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 128 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60817 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60820 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 80 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60825 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => by cases h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 80) 8
        rw [rspEq]
        exact frame_writable8 pre 80 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 80 8 4004 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60828 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60831 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60834 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60838 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60841 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60844 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60848 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60851 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60854 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60858 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60861 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60864 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60867 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60870 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60873 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60876 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60879 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60882 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60887 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109458 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 120) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 120 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60890 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60893 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60901 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109469 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 256) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 256 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60904 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60912 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109480 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 264) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 264 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60916 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60919 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60927 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109495 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 272) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 272 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60931 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60934 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60937 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60941 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60944 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60948 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60951 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60954 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60957 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60960 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60964 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60967 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60970 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60974 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60977 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 160 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60985 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => by cases h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 160) 8
        rw [rspEq]
        exact frame_writable8 pre 160 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 160 8 4161 8 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60988 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 72 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60993 (by decide)) (by decide)
      (fun model state => by
        rw [← state.rsp]
        refine ⟨_, rfl, ?_⟩
        intro hs
        cases hs)
      (fun _ h => by cases h)
    · intro model state
      refine ⟨state.rip, ?_, ?_⟩
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 72) 8
        rw [rspEq]
        exact frame_writable8 pre 72 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 72 8 4172 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 60996 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61000 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61003 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61008 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109579 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 24) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 24 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61011 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61014 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61017 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61021 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61024 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61028 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61031 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61034 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61038 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61041 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61048 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109617 ∧ MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (168)) 8
      have h : MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (168)) 8 := by
        refine ⟨by decide, ?_⟩
        intro i hi
        have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 168 + i) (by omega)
        exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, BitVec.add_assoc] using byte⟩
      exact ⟨state.rip, h⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61051 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61054 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61059 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1109630 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 56) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 56 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61062 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61065 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 61068 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
