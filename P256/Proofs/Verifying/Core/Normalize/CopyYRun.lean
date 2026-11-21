import P256.Proofs.Verifying.Core.Normalize.CopyY
import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize.CopyY

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem copyEffect_eq (p : BitVec 64) (s : RamState) :
    copyEffect p s = Copy32.effect (p+52) (fun t => stackPtr t+32) (fun t => stackPtr t+128) s := by
  simp only [copyEffect,Copy32.effect,BitVec.add_assoc]
  rfl

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10def8) :
    CopyPre 0x10def8 t := by
  refine ⟨rip,?_,?_,?_⟩
  · intro k hk
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals exact stack_readable (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide)
  · intro k hk
    exact local_writable8 hp state (by omega) (by omega)
  · intro k hk offset len bound
    have h := stack_code (frameOffset := 1176) hp.toCalleePre state
      (offset := 128+8*k) (len := 8) (codeOffset := 0xdef8+offset)
      (by decide) (by omega) (by omega : 0xdef8+offset+len ≤ 118431)
    simpa only [BitVec.ofNat_add,← BitVec.add_assoc,Extracted.textAddress,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using h

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {y : Nat}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10def8)
    (input : Field.MontgomeryAt t (stackPtr s-1144) y) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10df2c ∧
      Field.MontgomeryAt u (stackPtr s-1048) y ∧
      AgreesExcept (Copy32.components (stackPtr s-1048)) t u := by
  obtain ⟨n,u,execution,ready,_,effect⟩ := copy_block 0x10def8 boundary
    (fun i hi => by
      have h := inProgram_of_textOffset (0xdef8+i) (by omega)
      apply boundary_ne_program hp.outerBoundary
      simpa only [BitVec.ofNat_add,← BitVec.add_assoc,Extracted.textAddress,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using h)
    t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdef8 copyBytes
      (by decide) (by decide +kernel)) (pre hp state rip)
  change (copyEffect 0x10def8 t).Holds t u at effect
  rw [copyEffect_eq] at effect
  have source : stackPtr t+32 = stackPtr s-1144 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have destination : stackPtr t+128 = stackPtr s-1048 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have agrees := Copy32.frame effect
  change AgreesExcept (Copy32.components (stackPtr t+128)) t u at agrees
  rw [destination] at agrees
  have writes : WritesWithin (Copy32.components (stackPtr s-1048))
      #v[registerRegion s .rdi 24,workRegion s 9992] := by
    intro c hc a ha
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s 9992,by simp,work_contains hp.toCalleePre (offset := 1048) (by decide) (by decide) ha⟩
  have final := state.after_effect hp.toCalleePre (by decide) ready agrees writes
    (by simp [Copy32.components])
  refine ⟨n,u,execution,final,effect.rip,?_,agrees⟩
  apply input.of_bytes_eq
  have read := stack_readable (frameOffset := 1176) hp.toCalleePre state
    (offset := 32) (len := 32) (by decide) (by decide)
  have out := stack_readable (frameOffset := 1176) hp.toCalleePre final
    (offset := 128) (len := 32) (by decide) (by decide)
  have sp : stackPtr u = stackPtr t := final.rsp.trans state.rsp.symm
  rw [sp] at out
  have bytes := Copy32.copy_bytes effect read out
  change ∀ i < 32, u.external[stackPtr t+128+BitVec.ofNat 64 i]? =
    t.external[stackPtr t+32+BitVec.ofNat 64 i]? at bytes
  rw [source,destination] at bytes
  exact bytes

end P256.Proofs.Verifying.Core.Normalize.CopyY
