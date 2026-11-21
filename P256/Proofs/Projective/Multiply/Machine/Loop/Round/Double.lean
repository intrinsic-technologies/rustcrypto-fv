import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Double
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Memory
import P256.Proofs.Projective.Copy
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem double_step [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (index : Fin 3) (rip : t.RIP = (0x103350 : BitVec 64) + BitVec.ofNat 64 (8*index.val))
    (r13 : t.regValue .r13 = stackPtr s - 336)
    (input : ProjectiveAt t (stackPtr s - 336) point) :
    ∃ u, PointCallResult s t u boundary ((0x103358 : BitVec 64) + BitVec.ofNat 64 (8*index.val))
      336 point.double := by
  have code : Extracted.textBytes.toListFrom (0x3350 + 8*index.val) 3 = [0x4c,0x89,0xef] := by
    rcases index with ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> dsimp only [Fin.val_mk] <;> decide +kernel
  have start : (0x103350 : BitVec 64) + BitVec.ofNat 64 (8*index.val) =
      Extracted.textAddress + BitVec.ofNat 64 (0x3350 + 8*index.val) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  obtain ⟨v, run, ready, effect⟩ :=
    (mov_r64_r64_effect_step _ 0x4c 0xef (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) (0x3350 + 8*index.val)
        [0x4c,0x89,0xef] (by have := index.isLt; change 0x3350 + 8*index.val + 3 ≤ 118431; omega) code)
      (rip.trans start)
      (by
        change Extracted.textAddress + BitVec.ofNat 64 (0x3350 + 8*index.val) + 3#64 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset _ (by have := index.isLt; omega)))
  have frame : AgreesExcept [.reg 7, .rip] t v := effect.agrees
  have memory : v.external = t.external := frame.external (by simp [Component.Covers])
  have stateV := state.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have ripV : v.RIP = Extracted.textAddress + BitVec.ofNat 64 (nextDouble index).offset := by
    have h := effect.rip
    change v.RIP = Extracted.textAddress + BitVec.ofNat 64 (0x3350 + 8*index.val) + 3#64 at h
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [nextDouble, show 0x3350 + 8*index.val + 3 = 0x3353 + 8*index.val by omega] using h
  have dstV : v.regValue .rdi = stackPtr s - 336 := effect.writes.trans r13
  have inputV : ProjectiveAt v (stackPtr s - 336) point :=
    input.of_bytes_eq (fun i hi => by rw [memory])
  obtain ⟨u, result⟩ := double_call pre stateV (nextDouble index) ripV dstV inputV
  have ret : (nextDouble index).returnRip = (0x103358 : BitVec 64) + BitVec.ofNat 64 (8*index.val) := by
    simp only [CallSite.returnRip, nextDouble, BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
    rw [BitVec.add_comm (BitVec.ofNat 64 (8*index.val)) (5 : BitVec 64), ← BitVec.add_assoc,
      ← BitVec.add_assoc]
    rfl
  refine ⟨u, result.toFrameState, ?_, result.rip.trans ret, result.value, ?_, ?_⟩
  · obtain ⟨fuel, run'⟩ := result.execution
    exact ⟨1+fuel, run.trans run'⟩
  · intro r hr
    apply (result.registers r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp)
    · exact frame.read (n := 64) (r := 5) (by simp)
    · exact frame.read (n := 64) (r := 12) (by simp)
    · exact frame.read (n := 64) (r := 13) (by simp)
    · exact frame.read (n := 64) (r := 14) (by simp)
    · exact frame.read (n := 64) (r := 15) (by simp)
  · intro offset len ho hl apart i hi
    rw [result.bytes offset len ho hl apart i hi, memory]

theorem double_four [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (rip : t.RIP = 0x10334b) (dst : t.regValue .rdi = stackPtr s - 336)
    (r13 : t.regValue .r13 = stackPtr s - 336)
    (input : ProjectiveAt t (stackPtr s - 336) point) :
    ∃ u, PointCallResult s t u boundary 0x103368 336 (ProjectiveLoop.double4 point) := by
  obtain ⟨u₁, result₁⟩ := double_call pre state firstDouble rip dst input
  obtain ⟨u₂, result₂⟩ := double_step pre result₁.toFrameState ⟨0, by decide⟩
    (by exact result₁.rip)
    ((result₁.registers .r13 (by simp)).trans r13) result₁.value
  obtain ⟨u₃, result₃⟩ := double_step pre result₂.toFrameState ⟨1, by decide⟩
    (by simpa using result₂.rip)
    ((result₂.registers .r13 (by simp)).trans ((result₁.registers .r13 (by simp)).trans r13)) result₂.value
  obtain ⟨u₄, result₄⟩ := double_step pre result₃.toFrameState ⟨2, by decide⟩
    (by simpa using result₃.rip)
    ((result₃.registers .r13 (by simp)).trans ((result₂.registers .r13 (by simp)).trans
      ((result₁.registers .r13 (by simp)).trans r13))) result₃.value
  exact ⟨u₄, PointCallResult.trans (PointCallResult.trans (PointCallResult.trans result₁ result₂) result₃) result₄⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
