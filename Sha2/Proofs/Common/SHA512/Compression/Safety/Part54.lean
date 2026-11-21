import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part54

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
 theorem part54 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block):
    Certificate initial Decoded.part54 before54 after54 positions54 := by
  unfold Decoded.part54 before54 after54 positions54
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70967 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70970 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70973 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70976 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70979 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70983 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70986 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70989 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70993 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70996 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 70999 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71003 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71006 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71009 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71012 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71015 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71018 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71021 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71024 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71027 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71030 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71033 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71036 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71040 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71043 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71046 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71050 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71053 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71056 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71060 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71063 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71068 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1119639 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 48) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 48 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71071 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 48 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71076 (by decide)) (by decide)
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
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 48) 8
        rw [rspEq]
        exact frame_writable8 pre 48 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 48 8 14255 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71079 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71083 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71086 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71090 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71093 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71096 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71100 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71103 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71106 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71109 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71112 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71115 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71118 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71121 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71124 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71127 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71130 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71134 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71137 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71141 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71144 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71147 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71151 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71154 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71157 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71160 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71163 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71166 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71169 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71172 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71175 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71178 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71181 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71184 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71187 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71191 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71194 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71198 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71201 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71205 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71208 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71211 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71215 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71220 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1119791 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 64) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 64 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71223 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71226 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71230 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71233 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71236 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71240 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71243 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71248 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1119819 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 40) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 40 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71251 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71254 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71257 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71260 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71263 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71266 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71269 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71272 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71275 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71279 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71282 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71286 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71289 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71292 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
