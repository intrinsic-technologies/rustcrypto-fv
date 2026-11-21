import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Fill
import P256.Proofs.Verifying.Combination.Naf.Machine.PreparePadding
import P256.Proofs.Verifying.Combination.Naf.Machine.RecodeDigitStore
import P256.Proofs.Verifying.Combination.Naf.Machine.RecodeBranchTail

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

set_option maxHeartbeats 600000 in
theorem padding [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i k : Nat}
    (pre : Pre s boundary) (frame : FrameState s t) (bound : i+k ≤ 256)
    (positive : 0<k) (small : k≤5) (rip : t.RIP = 0x10f4ac)
    (cf : (StatusFlags.ofRFLAGS t.RFLAGS).CF = decide (k<2))
    (r14 : t.regValue .r14 = BitVec.ofNat 64 i)
    (rbp : t.regValue .rbp = BitVec.ofNat 64 k)
    (rsi : t.regValue .rsi = s.regValue .rdi)
    (rax : t.regValue .rax = BitVec.ofNat 64 (257-i)) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10f3d3 ∧
      u.regValue .r14 = BitVec.ofNat 64 (i+k) ∧
      Bytes u.external (s.regValue .rdi+BitVec.ofNat 64 (i+1)) (k-1) (fun _ => 0) ∧
      AgreesExcept [.reg 1,.reg 2,.reg 14,.flags,.rip,
        .mem (s.regValue .rdi+BitVec.ofNat 64 (i+1)) (k-1)] t u := by
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset h)
  obtain ⟨a, ra, readyA, _, ripA, ga⟩ := Iterator.Advance.branch32 (offset := 0xf4ac) 2 0xffffff1e
    (decide (k<2)) (readyToStep frame.machine frame.bindingsSupported) frame.loaded rip cf
    (by decide) (by decide +kernel) (by decide +kernel)
    (by split <;> first | exact next 0xf3d0 (by decide) | exact next 0xf4b2 (by decide))
  have fa := frame.after_registers readyA ga (by simp [Component.Covers]) (by simp)
  have r14A : a.regValue .r14 = BitVec.ofNat 64 i := (ga.read (n := 64) (r := 14) (by simp)).trans r14
  by_cases one : k<2
  · have hk : k=1 := by omega
    obtain ⟨u, ru, fu, ipU, r14U, gu⟩ := DigitStore.inc_index pre fa
      (by simpa [one, branchTarget, Extracted.textAddress] using ripA) r14A
    refine ⟨_, u, ra.trans ru, fu, ipU, ?_, ?_, (ga.trans gu).mono (by simp)⟩
    · simpa only [hk] using r14U
    · intro j hj
      omega
  · have bpA : a.regValue .rbp = BitVec.ofNat 64 k := (ga.read (n := 64) (r := 5) (by simp)).trans rbp
    have siA : a.regValue .rsi = s.regValue .rdi := (ga.read (n := 64) (r := 6) (by simp)).trans rsi
    obtain ⟨b, rb, fb, ipB, cxB, r14B, dxB, gb⟩ := prepare_padding fa
      (by simpa [one, branchTarget, Extracted.textAddress] using ripA) r14A bpA siA pre.outerBoundary
    have bpB : b.regValue .rbp = BitVec.ofNat 64 k := (gb.read (n := 64) (r := 5) (by simp)).trans bpA
    have axB : b.regValue .rax = BitVec.ofNat 64 (257-i) :=
      ((ga.trans gb).read (n := 64) (r := 0) (by simp)).trans rax
    obtain ⟨n, c, rc, fc, ipC, _, zerosC, gc⟩ := fill pre fb bound (by omega : 1<k) small
      ipB axB bpB r14B dxB
    obtain ⟨u, ru, fu, ipU, r14U, gu⟩ := BranchTail.padding_exit pre fc ipC
    have cxC : c.regValue .rcx = BitVec.ofNat 64 (i+k) :=
      (gc.read (n := 64) (r := 1) (by simp)).trans cxB
    refine ⟨_, u, ((ra.trans rb).trans rc).trans ru, fu, ipU, r14U.trans cxC, ?_,
      (((ga.trans gb).trans gc).trans gu).mono (by simp)⟩
    intro j hj
    rw [gu.external (by simp [Component.Covers])]
    exact zerosC j hj

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
