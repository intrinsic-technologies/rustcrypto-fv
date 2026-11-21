import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.Common.Instructions.ByteLogic.Unary

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

set_option maxRecDepth 4096 in
theorem invert_choice [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t)
    (rip : t.RIP = 0x10cb9a)
    (zero : (t.regValue .rax).setWidth 8 = 0) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧
      u.RIP = (0x10cba1) ∧ u.regValue .rdi = 1 ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u := by
  let offset : Nat := 0xcb9a
  let pc := Extracted.textAddress + BitVec.ofNat 64 offset
  have rip0 : t.RIP = pc := by exact rip
  have outside (i : Nat) (hi : i ≤ 7) : pc + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply boundary_ne_program pre.outerBoundary
    have h := inProgram_of_textOffset (offset+i) (by dsimp [offset] <;> omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, pc] using h
  obtain ⟨a, runA, readyA, effectA⟩ := (not_al_effect_step pc).advances
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) offset [0xf6,0xd0]
      (by decide) (by decide +kernel)) rip0
    (outside 2 (by decide))
  have agreesA : AgreesExcept [.reg 0, .rip] t a := effectA.agrees
  have frameA := after_registers frame readyA agreesA
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  have codeA : CodeIn (codeRange (pc+2#64) P256.Proofs.Generate.Zero.maskBytes) a := by
    have h := programText_slice (programLoaded_codeIn frameA.loaded) (offset+2) P256.Proofs.Generate.Zero.maskBytes
      (by decide) (by decide +kernel)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, pc] using h
  obtain ⟨u, runU, readyU, agreesU, ripU, valueU⟩ := P256.Proofs.Generate.Zero.mask_arguments boundary (pc+2#64)
    readyA codeA effectA.rip
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using outside 4 (by decide))
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using outside 7 (by decide))
  have agrees : AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u :=
    (agreesA.trans agreesU).mono (by simp)
  refine ⟨u, runA.trans runU, after_registers frame readyU agrees
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp), ?_, ?_, agrees⟩
  · exact ripU
  · have valueA : a.regValue .rax = mergeGPR 8 (~~~((t.regValue .rax).setWidth 8)) (t.regValue .rax) :=
      effectA.writes
    rw [valueU, valueA, mergeGPR_low8, zero]
    rfl

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish
