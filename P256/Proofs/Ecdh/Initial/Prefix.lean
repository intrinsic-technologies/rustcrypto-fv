import P256.Proofs.Ecdh.Initial.Prefix.Prologue
import P256.Proofs.Ecdh.Initial.Prefix.Result
import P256.Proofs.Ecdh.Initial.Prefix.Choice

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Standards.SECG.ECC

set_option maxRecDepth 4096 in
theorem prefix_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {point : Curve.Point}
    (pre : Ecdh.Pre s boundary) (peer : Sec1.AffineAt s (s.regValue .rdx) point) :
    ∃ fuel t, Advances boundary fuel s t ∧ Copied s t point := by
  obtain ⟨u,run,frame,rip,_,agrees⟩ := Prefix.frame_entry pre.toCalleePre
  have rsi : u.regValue .rsi = s.regValue .rsi :=
    agrees.read (n := 64) (r := 6) (by simp [saveFrame])
  have rdi : u.regValue .rdi = s.regValue .rdi :=
    agrees.read (n := 64) (r := 7) (by simp [saveFrame])
  have rdx : u.regValue .rdx = s.regValue .rdx :=
    agrees.read (n := 64) (r := 2) (by simp [saveFrame])
  obtain ⟨fuel,v,runV,readyV,_,effectV⟩ := Prefix.Block.correct boundary (by
      intro i hi
      apply boundary_ne_program pre.outerBoundary
      have h := inProgram_of_textOffset (0x11+i) (by omega)
      simp only [BitVec.ofNat_add,←BitVec.add_assoc,Extracted.textAddress,BitVec.reduceAdd] at h
      exact h) u
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x11 Prefix.Block.codeBytes
      (by decide) (by decide +kernel))
    (Prefix.prepare_pre pre frame rip rdx)
  have prepared := Prefix.block_result pre frame readyV effectV rsi rdi rdx peer
  obtain ⟨w,runW,copied⟩ := Prefix.copy_identity pre prepared
  obtain ⟨t,runT,result⟩ := Prefix.choice pre copied peer
  exact ⟨7+fuel+12+7,t,((run.trans runV).trans runW).trans runT,result⟩

end P256.Proofs.Ecdh.Initial
