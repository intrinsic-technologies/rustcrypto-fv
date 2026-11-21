import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Select
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Tag
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Convert

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add)

set_option maxRecDepth 2048 in
theorem tag_output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : SignPre s boundary) (state : Selected s t x y) (rip : t.RIP = 0x10d0f8) :
    ∃ u, Advances boundary 6 t u ∧ u.RIP = 0x10d111 ∧
      Affine s u x y ∧ Preserved s t u := by
  have tag : t.external[stackPtr s-1688]? = some 0 := by
    rw [← (show frameBase s+592 = stackPtr s-1688 from base_add s (by decide))]
    exact state.tag
  obtain ⟨v,run,ready,ip,value,ag⟩ := tag_registers (select := true) pre.toCalleePre
    (scalarFrame state.frame) tag state.registers.flag rip
  have frame := after_registers state.frame ready ag (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  have mem : v.external = t.external := ag.external (by simp [Component.Covers])
  obtain ⟨u,run1,ready1,ef⟩ :=
    (Common.Instructions.mov_m8_r8_legacy_effect_step 0x10d10a 0 (by decide)
      (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn frame.loaded) 0xd10a _ (by decide) (by decide +kernel))
      ⟨ip,(by change MemWritable v (stackPtr v+168) 1
              exact local_byte_writable pre.toCalleePre (scalarFrame frame) (offset := 168) (by decide)),
        by change RangeApart (stackPtr v+168) 1 _ 7
           rw [frame.rsp]
           exact local_code_apart pre frame (offset := 168) (len := 1) (codeOffset := 0xd10a) (codeLen := 7) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd111 (by decide)))
  have ag1 : AgreesExcept [.mem (frameBase s+168) 1,.rip] v u := by
    have h := ef.agrees
    simp only [storeEffect_components] at h
    change AgreesExcept [.mem (stackPtr v+168) 1,.rip] v u at h
    rwa [frame.rsp] at h
  have word : memLoad u.external (frameBase s+168) 8 = 0 := by
    have h := ef.writes
    change memLoad u.external (stackPtr v+168) 8 = (Operand.reg 0 : Operand 8).read v at h
    rw [frame.rsp,value] at h
    exact h
  have st := stored pre frame ready1 (offset := 168) (by decide) ag1 word
  have unchanged (i : Nat) (small : i < 2^64) (apart : i < 168 ∨ 169 ≤ i) :
      u.external[frameBase s+BitVec.ofNat 64 i]? = t.external[frameBase s+BitVec.ofNat 64 i]? := by
    simpa only [mem] using st.unchanged (by decide) small apart
  refine ⟨u,run.trans run1,ef.rip,⟨st.frame,⟨?_,?_,?_⟩,?_,?_,?_,?_⟩,?_⟩
  · apply state.x.of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using unchanged (104+i) (by omega) (.inl (by omega))
  · have h : Field.MontgomeryAt u (frameBase s+136) y := by
      apply state.y.of_bytes_eq
      intro i hi
      simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using unchanged (136+i) (by omega) (.inl (by omega))
    change Field.MontgomeryAt u (frameBase s+104+32) y
    rw [show frameBase s+104+32 = frameBase s+136 by rw [BitVec.add_assoc]; rfl]
    exact h
  · change u.external[frameBase s+104+64]? = some 0
    rw [show frameBase s+104+64 = frameBase s+168 by rw [BitVec.add_assoc]; rfl]
    exact st.byte
  · exact ((ag.trans ag1).read (n := 64) (r := 5) (by simp)).trans state.registers.rbp
  · exact ((ag.trans ag1).read (n := 64) (r := 13) (by simp)).trans state.registers.r13
  · exact ((ag.trans ag1).read (n := 64) (r := 14) (by simp)).trans state.registers.r14
  · exact ((ag.trans ag1).read (n := 64) (r := 15) (by simp)).trans state.registers.r15
  · intro i hi
    exact unchanged i (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
