import P256.Proofs.Sec1.Affine.Compact.Finish.ConstantsSetup
import P256.Proofs.Sec1.Affine.Compressed.Finish.Constants
import P256.Proofs.Sec1.Affine.Compact.Finish.State
import P256.Proofs.Sec1.Affine.Compact.Finish.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Compressed.Finish
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_identity [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Standards.SECG.ECC.Curve.Point}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110565) (decoded : AffineResultAt t (stackPtr s - 744) point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11057f ∧
      AffineResultAt u (stackPtr s - 744) point ∧
      AffineAt u (stackPtr s - 592) .infinity ∧ u.regValue .rax = stackPtr s - 592 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 7, .reg 6, .mem (stackPtr s - 592) 72, .rip] t u := by
  obtain ⟨n, a, runA, readyA, _, effect⟩ := constants_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10565 constantsSetupBytes
      (by decide) (by decide +kernel)) rip
  have agreesA : AgreesExcept [.reg 0, .reg 1, .reg 7, .reg 6, .rip] t a := effect.agrees
  have frameA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  change a.regValue .rax = stackPtr t + 168 ∧ a.regValue .rcx = 9 ∧
    a.regValue .rdi = stackPtr t + 168 ∧ a.regValue .rsi = 0x202df8 at writes
  have destination : stackPtr t + 168 = stackPtr s - 592 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨u, runU, frameU, ripU, identity, agreesU⟩ := copy_constants pre frameA
    (offset := 592) (by decide) (by decide) 0x1057c (by decide) (by decide +kernel)
    effect.rip writes.2.2.2 (writes.2.2.1.trans destination) writes.2.1
  refine ⟨n + 9, u, runA.trans runU, frameU, ripU, ?_, identity, ?_,
    (agreesA.trans agreesU).mono (by simp [constantComponents, BitVec.ofNat_eq_ofNat])⟩
  · apply decoded.of_bytes_eq
    intro i hi
    have unchanged : u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
        a.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
      apply agreesU.byte
      intro c hc ha
      simp only [constantComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -592#64) (len₁ := 72) (c₂ := -744#64) (len₂ := 73)
        (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using he.symm
    exact unchanged.trans (by rw [agreesA.external (by simp [Component.Covers])])
  · exact (agreesU.read (n := 64) (r := 0) (by simp [constantComponents])).trans
      (writes.1.trans destination)

theorem initialize_identity [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Standards.SECG.ECC.Curve.Point}
    (pre : AffineDecodePre s boundary bytes) (state : Relocated s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Ready s u point := by
  obtain ⟨fuel,u,run,frame,rip,decoded,_,rax,agrees⟩ :=
    prepare_identity pre state.toFrameState state.rip state.decoded
  refine ⟨fuel,u,run,frame,rip,?_,decoded,rax,?_,?_,?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans state.output
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans state.rdx
  · exact (congrArg (BitVec.setWidth 8) (agrees.read (n := 64) (r := 5) (by simp))).trans state.choice
  · apply Eq.trans (load_preserve (preserve (s := s) agrees (offset := 748) (len := 1) ?_)) state.mask
    intro address count member
    simp only [List.mem_cons,List.not_mem_nil,or_false,false_or,Component.mem.injEq,reduceCtorEq] at member
    obtain ⟨rfl,rfl⟩ := member
    exact ⟨-592,by simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat],by unfold OffsetsApart; decide +kernel,by decide⟩

end P256.Proofs.Sec1.Affine.Compact.Finish
