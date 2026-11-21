import P256.Proofs.Sec1.SquareRoot.Square.Wide.Body
import P256.Proofs.Sec1.SquareRoot.Square.Wide.BodyFrame
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Memory
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Output

set_option autoImplicit false

open P256.Proofs.Field.Schoolbook (packEight)
open P256.Proofs.Program (CalleePre CalleeResult memoryRegion_contains_add programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field.SquareRoot

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 600000 in
theorem execute_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x11cba0 32 64 88) (count : s.regValue .rdx = 4) :
    ∃ t u, CalleeResult s u boundary 64 88 ∧
      AgreesExcept (Multiply.prologueComponents s) s t ∧
      Bytes u.external (s.regValue .rdi) 64
        (fun i => UInt8.ofNat (packEight ((squareWords (sourceWords t)).map BitVec.toNat) / 256^i % 256)) := by
  obtain ⟨t, run0, ready0, loaded0, rip0, rsp0, mem0, frame0⟩ := prologue_correct pre count
  have rdi0 : t.regValue .rdi = s.regValue .rdi :=
    frame0.read (n := 64) (r := 7) (by simp [Multiply.prologueComponents])
  have bp := bodyPre_of_prologue pre rip0 rsp0 frame0
  have code : CodeIn (codeRange 0x11cbb8 bodyBytes) t :=
    programText_slice (programLoaded_codeIn loaded0) 0x1cbb8 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨n, v, run1, ready1, _, body⟩ := body_correct boundary pre.outerBoundary t ready0 code bp
  have bf := bodyEffect_frame body
  have frame1 : AgreesExcept (frame s) s v :=
    ((prologue_frame frame0).trans (body_frame rsp0 rdi0 bf)).mono (by simp)
  have loaded1 := loaded_of_frame pre frame1
  have rsp1 : stackPtr v = stackPtr s-88 :=
    (body.agrees.read (n := 64) (r := 4) (by simp [bodyEffect_components])).trans rsp0
  have rdi1 : v.regValue .rdi = s.regValue .rdi :=
    (body.agrees.read (n := 64) (r := 7) (by simp [bodyEffect_components])).trans rdi0
  have ep : EpiloguePre s v (frame s) := by
    refine ⟨ready1, loaded1, body.rip, rsp1, rdi1, ?_, ?_, frame1⟩
    · intro item hitem
      have ho : item.2 ≤ 48 := by
        simp only [P256.Proofs.Common.Encoding.Serialize.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hitem
        rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      change memLoad v.external (stackPtr s-BitVec.ofNat 64 item.2) 64 = _
      rw [saved_word_preserved pre rsp0 rdi0 bf ho, mem0]
      exact Multiply.savedMemory_registers s item hitem
    · have h := saved_word_preserved pre rsp0 rdi0 bf (offset := 0) (by decide)
      rw [BitVec.sub_zero, mem0, Multiply.savedMemory_return] at h
      exact h
  obtain ⟨u, result⟩ := epilogue_correct pre ep
  have frame2 : AgreesExcept (frame s) s u :=
    (frame1.trans (epilogue_frame (s := s) result.agrees)).mono (by simp)
  refine ⟨t, u, ⟨⟨9+n+9, (run0.trans run1).trans result.execution⟩, result.rip,
    result.rsp, result.bindingsSupported, result.machine, result.calleeSaved,
    result.directionFlag, result.mxcsr, result.fp87, frame2.memoryWriteFrame (frame_within pre),
    result.loaded, frame2.grow⟩, frame0, ?_⟩
  rw [result.external]
  have bytes := body_output_bytes body (fun i hi => by
    rw [rdi0]
    apply frame1.grow
    obtain ⟨b, hb⟩ := pre.outputAllocated _ (memoryRegion_contains_add pre.outputBounded
      (Nat.le_refl _) (Nat.le_refl _) hi)
    rw [hb]
    rfl)
  simpa only [rdi0] using bytes

end P256.Proofs.Sec1.SquareRoot.Square.Wide
