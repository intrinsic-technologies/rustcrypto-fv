import P256.Proofs.Ecdh.Initial.Prefix.Memory
import P256.Proofs.Projective.Copy

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Standards.SECG.ECC

structure IdentityCopied [Bindings] (s t : RamState) (point : Curve.Point) : Prop extends Ecdh.Frame s t where
  rip : t.RIP = 0x1000de
  output : t.regValue .rbx = s.regValue .rdi
  scalar : memLoad t.external (frameBase s + 8) 64 = s.regValue .rsi
  source : ProjectiveAt t (frameBase s + 248) (lifted point)
  identity : ProjectiveAt t (frameBase s + 1016) Projective.identity
  r14 : t.regValue .r14 = frameBase s + 280
  r12 : t.regValue .r12 = frameBase s + 312
  r13 : t.regValue .r13 = frameBase s + 1016
  peer : t.regValue .rdx = s.regValue .rdx

theorem copy_identity [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Curve.Point} (pre : Ecdh.Pre s boundary) (state : Prepared s t point) :
    ∃ u, Advances boundary 12 t u ∧ IdentityCopied s u point := by
  have dst := state.destination.trans (frame_address s 1016 (by decide))
  have readable : MemReadable t (t.regValue .rsi) 96 := by
    rw [state.constant]
    exact Projective.Constants.identity_readable state.loaded
  have apart : (t.regValue .rsi).toNat+96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat+96 ≤ (t.regValue .rsi).toNat := by
    rw [state.constant,dst]
    exact Projective.Constants.identity_stack_disjoint pre.toCalleePre (by decide) (by decide)
  have input : ProjectiveAt t (t.regValue .rsi) Projective.identity := by
    rw [state.constant]
    exact Projective.Constants.identity_at state.loaded
  obtain ⟨u,run,frame,rip,value,agrees⟩ := Projective.Copy.copy_to_stack pre.toCalleePre state.toFrameState
    0xdb (by decide) (by decide +kernel) state.rip 1040 (by decide) (by decide)
    dst state.count readable apart input
  have keep (offset len : Nat) (ho : offset ≤ 2056) (hl : len ≤ offset+8)
      (ha : 1040+len ≤ offset ∨ offset+96 ≤ 1040) {i : Nat} (hi : i < len) :
      u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    apply agrees.byte
    intro c hc covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,eq⟩ := covered
    exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) hl ha.symm j hj i hi eq.symm
  refine ⟨u,run,frame,rip,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans state.output
  · have eq : memLoad u.external (frameBase s+8) 64 = memLoad t.external (frameBase s+8) 64 := by
      rw [show frameBase s+8 = stackPtr s-2048 from frame_address s 8 (by decide)]
      apply memLoad_congr
      intro i hi
      change (u.external[stackPtr s-2048#64+BitVec.ofNat 64 i]?).getD 0 = _
      rw [keep 2048 8 (by decide) (by decide) (by decide) hi]
      rfl
    exact eq.trans state.scalar
  · apply state.source.of_bytes_eq
    intro i hi
    rw [show frameBase s+248 = stackPtr s-1808 from frame_address s 248 (by decide)]
    exact keep 1808 96 (by decide) (by decide) (by decide) hi
  · rw [show frameBase s+1016 = stackPtr s-1040 from frame_address s 1016 (by decide)]
    exact value
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans state.r14
  · exact (agrees.read (n := 64) (r := 12) (by simp)).trans state.r12
  · exact (agrees.read (n := 64) (r := 13) (by simp)).trans state.r13
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans state.peer

end P256.Proofs.Ecdh.Initial.Prefix
