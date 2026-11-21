import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part31

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
 theorem part31 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block)
    (loaded : ProgramLoaded initial):
    Certificate initial Decoded.part31 before31 after31 positions31 := by
  unfold Decoded.part31 before31 after31 positions31
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63129 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63132 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63135 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63139 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63142 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63149 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1111718 ∧ MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (256)) 8
      have h : MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (256)) 8 := by
        refine ⟨by decide, ?_⟩
        intro i hi
        have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 256 + i) (by omega)
        exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, BitVec.add_assoc] using byte⟩
      exact ⟨state.rip, h⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63152 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63155 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63158 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63161 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63164 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63167 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63170 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63173 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63176 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63180 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63183 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63187 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63190 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63193 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63197 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63200 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63203 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63206 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63209 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63212 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63215 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63218 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63221 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63224 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63227 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63230 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63234 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63237 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63241 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63244 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63247 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63250 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63253 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63256 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63260 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63263 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63266 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63270 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63273 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 32 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63278 (by decide)) (by decide)
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
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 32) 8
        rw [rspEq]
        exact frame_writable8 pre 32 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 32 8 6457 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63281 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 16 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63286 (by decide)) (by decide)
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
        change MemWritable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 16) 8
        rw [rspEq]
        exact frame_writable8 pre 16 (by decide) (by decide)
      · simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
        have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
          simpa [Operand.read] using state.rsp
        have h := frame_apart pre.stack 16 8 6465 5 (by decide) (by decide)
        change RangeApart (stackPtr initial + BitVec.ofNat 64 _ ) _ _ _ at h
        rw [← rspEq] at h
        simpa [Disp.value, BitVec.signExtend_eq, BitVec.setWidth_eq, AddrMode.tail, Disp.bytes] using h

  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63289 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63293 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63296 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63301 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1111872 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 8) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 8 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63304 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63307 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63311 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63314 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63318 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63321 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63324 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63328 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63331 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63338 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1111907 ∧ MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (264)) 8
      have h : MemReadable initial (Sha2.Spec.Program.Extracted.rodataAddress + BitVec.ofNat 64 (264)) 8 := by
        refine ⟨by decide, ?_⟩
        intro i hi
        have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 264 + i) (by omega)
        exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, BitVec.add_assoc] using byte⟩
      exact ⟨state.rip, h⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63341 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63344 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63347 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63350 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63353 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63356 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63359 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63362 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63365 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63369 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63372 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63376 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63379 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63382 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63386 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63389 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63392 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63395 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63398 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63401 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63404 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63407 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63410 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63414 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63417 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63420 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63424 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63427 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63430 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63433 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63436 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63439 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63443 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63446 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63449 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63452 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63456 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 63459 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
