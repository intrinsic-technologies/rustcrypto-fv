import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part38

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
 theorem part38 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block)
    (loaded : ProgramLoaded initial):
    Certificate initial Decoded.part38 before38 after38 positions38 := by
  unfold Decoded.part38 before38 after38 positions38
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65502 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65505 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65509 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65512 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65515 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65518 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65521 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65524 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65528 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65531 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65535 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65538 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65543 (by decide)) (by decide)
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
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 8) 8
        rw [rspEq]
        exact frame_writable8 pre 8 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 8 8 8722 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65546 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 72 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65551 (by decide)) (by decide)
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
        have h := frame_apart pre.stack 72 8 8730 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65554 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65558 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65561 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65566 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1114137 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 96) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 96 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65569 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65572 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65576 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65579 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65583 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65586 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65589 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65593 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65596 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65603 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1114172 ∧ MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (360)) 8
      have h : MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (360)) 8 := by
        refine ⟨by decide, ?_⟩
        intro i hi
        have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 360 + i) (by omega)
        exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, BitVec.add_assoc] using byte⟩
      exact ⟨state.rip, h⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65606 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65609 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65612 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65615 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65618 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65621 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65624 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65627 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65630 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65634 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65637 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65641 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65644 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65647 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65651 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65654 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65657 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65660 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65663 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65666 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65669 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65672 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65675 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65678 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65682 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65685 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65688 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65692 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65695 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65698 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65701 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65704 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65707 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65711 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65714 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65717 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65720 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65724 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65727 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 40 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65732 (by decide)) (by decide)
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
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 40) 8
        rw [rspEq]
        exact frame_writable8 pre 40 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 40 8 8911 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65735 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 104 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65740 (by decide)) (by decide)
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
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 104) 8
        rw [rspEq]
        exact frame_writable8 pre 104 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 104 8 8919 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65743 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65747 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65750 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65754 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65757 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65760 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65764 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65769 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1114340 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 48) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 48 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65772 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65775 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65779 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65782 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65785 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65792 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1114361 ∧ MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (368)) 8
      have h : MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (368)) 8 := by
        refine ⟨by decide, ?_⟩
        intro i hi
        have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 368 + i) (by omega)
        exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, BitVec.add_assoc] using byte⟩
      exact ⟨state.rip, h⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65795 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65798 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65801 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65804 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65807 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65810 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65813 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65817 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65820 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65823 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65827 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65830 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65833 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65837 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 65840 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
