import P256.Proofs.Sec1.Affine.Compact.Copy.Transfer
import P256.Proofs.Sec1.Affine.Compact.Copy.Span

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem copy_point [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {x y : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110294)
    (hx : Field.MontgomeryAt t (stackPtr s - 480) x)
    (hy : Field.MontgomeryAt t (stackPtr s - 448) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110308 ∧
      Field.MontgomeryAt u (stackPtr s - 664) x ∧ Field.MontgomeryAt u (stackPtr s - 632) y ∧
      AgreesExcept [.mem (stackPtr s - 664) 64,.reg 0,.reg 1,.rip] t u := by
  obtain ⟨n,a,runA,frameA,ripA,yA,effectA⟩ := transfer_y pre state rip hy
  have xA : Field.MontgomeryAt a (stackPtr s - 480) x := by
    apply hx.of_bytes_eq
    intro i hi
    have h := y_preserves effectA (offset := 280) (len := 32) (by decide) (Or.inr (by decide)) i hi
    simpa only [ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 280) state.rsp
      (by decide) (by decide),Nat.reduceSub,BitVec.ofNat_eq_ofNat] using h
  obtain ⟨m,u,runU,frameU,ripU,xU,effectU⟩ := transfer_x pre frameA ripA xA
  have yU : Field.MontgomeryAt u (stackPtr s - 632) y := by
    apply yA.of_bytes_eq
    intro i hi
    have h := x_preserves effectU (offset := 128) (len := 32) (by decide) (Or.inr (by decide)) i hi
    simpa only [ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 128) frameA.rsp
      (by decide) (by decide),Nat.reduceSub,BitVec.ofNat_eq_ofNat] using h
  refine ⟨n+m,u,runA.trans runU,frameU,ripU,xU,yU,?_⟩
  have rsp : stackPtr a = stackPtr t := frameA.rsp.trans state.rsp.symm
  have agrees := effectA.agrees.trans effectU.agrees
  have span : AgreesExcept [.mem (stackPtr t + 96) 64,.reg 0,.reg 1,.rip] t u := by
    apply stack_span agrees
    · intro c hc hm
      simp only [yEffect,xEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
        Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with (((rfl | rfl | rfl | rfl | rfl) | rfl) | ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl))
      all_goals simp_all [Component.isMem]
    · intro address count hc
      simp only [yEffect,xEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
        Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
        Component.mem.injEq,reduceCtorEq,Nat.reduceDiv,rsp] at hc
      rcases hc with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) |
        (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨128,rfl,by decide,by decide⟩
      · exact ⟨136,rfl,by decide,by decide⟩
      · exact ⟨144,rfl,by decide,by decide⟩
      · exact ⟨152,rfl,by decide,by decide⟩
      · exact ⟨96,rfl,by decide,by decide⟩
      · exact ⟨104,rfl,by decide,by decide⟩
      · exact ⟨112,rfl,by decide,by decide⟩
      · exact ⟨120,rfl,by decide,by decide⟩
  simpa only [ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 96) state.rsp
    (by decide) (by decide),Nat.reduceSub,BitVec.ofNat_eq_ofNat] using span

end P256.Proofs.Sec1.Affine.Compact.Copy
