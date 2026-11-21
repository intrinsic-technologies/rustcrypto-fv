import P256.Proofs.Sec1.Decode.Prepare.Copy.Run
import P256.Proofs.Sec1.Decode.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 400000 in
theorem prepare_affine_call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre initial boundary bytes) (state : BufferReady initial s bytes) :
    ∃ t fuel, Advances boundary fuel s t ∧ AffineCallReady initial t bytes ∧
      t.regValue .r15 = initial.regValue .rdi ∧ t.regValue .r12 = 0 := by
  let f := fun i ↦ memByte s.external (stackPtr s + BitVec.ofNat 64 i)
  have window : Copy.Window s f := Bytes.of_isSome
    (by simpa using (stack_readable pre state.toFrame (offset := 0) (len := 280) (by decide)).mem)
  obtain ⟨u, fuel, run, frame, rip, copied, r12, r15⟩ :=
    Copy.run pre state.toFrame window state.rip
  obtain ⟨a, aa, ra, ea⟩ := (mov_r64_r64_effect_step 0x10e622 0x48 0xe7
    (by simp [RexWPrefix]) rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xe622 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe625 (by decide)))
  have ga : AgreesExcept [.reg 7, .rip] u a := ea.agrees
  have fa := frame.after_registers pre ra ga (by simp [Component.Covers]) (by simp)
  obtain ⟨t, ab, rb, eb⟩ := (lea_r64_effect_step 0x10e625 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 156)) (by decide) rfl rfl).advances ra
      (programText_slice (programLoaded_codeIn fa.loaded) 0xe625 _
        (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe62d (by decide)))
  have gb : AgreesExcept [.reg 6, .rip] a t := eb.agrees
  have total : AgreesExcept [.reg 7, .reg 6, .rip] u t :=
    (ga.trans gb).mono (by simp)
  have ft := fa.after_registers pre rb gb (by simp [Component.Covers]) (by simp)
  have di : a.regValue .rdi = stackPtr initial - 312 := ea.writes.trans frame.rsp
  have si : t.regValue .rsi = stackPtr initial - 156 := by
    have h : t.regValue .rsi = stackPtr a + 156 := eb.writes
    rw [h, fa.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  refine ⟨t, fuel+2, run.trans (aa.trans ab),
    ⟨ft, eb.rip, si, (gb.read (n := 64) (r := 7) (by simp)).trans di, ?_⟩,
    (total.read (n := 64) (r := 15) (by simp)).trans (r15.trans state.destination),
    (total.read (n := 64) (r := 12) (by simp)).trans (r12.trans state.zero)⟩
  refine ⟨state.encoded.1, ?_⟩
  intro i hi
  have hb := copied (156+i) (by omega)
  rw [Copy.copiedWindow_eq f hi] at hb
  have hs := window i (by omega)
  have addr (v : RamState) (hv : stackPtr v = stackPtr initial - 312) (off : Nat) :
      stackPtr v + BitVec.ofNat 64 (off+i) =
        stackPtr initial - 312 + BitVec.ofNat 64 off + BitVec.ofNat 64 i := by
    rw [hv, BitVec.ofNat_add, ← BitVec.add_assoc]
  rw [addr u frame.rsp 156] at hb
  rw [state.rsp] at hs
  have h156 : stackPtr initial - 312 + 156 = stackPtr initial - 156 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  simp only [BitVec.ofNat_eq_ofNat] at hb hs h156
  rw [h156] at hb
  rw [total.external (by simp [Component.Covers])]
  have enc := state.encoded.2 i hi
  simp only [BitVec.ofNat_eq_ofNat] at enc ⊢
  exact hb.trans (hs.symm.trans enc)

end P256.Proofs.Sec1.Decode.Prepare
