import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.CopyArgs

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

structure WindowReady [Bindings] (s t : RamState) (x : Nat) : Prop where
  frame : ExponentFrame s t
  rip : t.RIP=0x1153d4
  table : ∀ i<16, Field.MontgomeryAt t
    (exponentFrameBase s+0x338+BitVec.ofNat 64 (32*i)) (x^i%P256.Spec.Operations.domain.p)
  exponent : Nat256At t (exponentFrameBase s+0x538) sqrtExponent
  bitCount : t.regValue .r14=254
  parameter : t.regValue .r15=s.regValue .rsi+32
  inverse : t.regValue .r12=0xffffffffffffffff
  negativeInverse : exponentWordAt t (exponentFrameBase s+0x2c8) 1

theorem initialize_window_ready [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ u fuel, Advances boundary fuel s u ∧ WindowReady s u x := by
  obtain ⟨t,fuel,run,state,rip,inverse⟩ := initialize_table ctx
  obtain ⟨v,setup,fv,ipv,di,si,dx,g⟩ := copy_arguments ctx state.frame rip
  obtain ⟨fc,u,called,fu,ipu,copied,regs,kept⟩ := copy_call ctx.toCalleePre fv ipv si di dx
  have memory : v.external=t.external := g.external (by simp [Component.Covers])
  have bytes {off len j : Nat} (hb : off+len≤1416) (ha : off+len≤824 ∨ 1336≤off) (hj : j<len) :
      u.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]?=
      t.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]? :=
    (kept off len hb ha j hj).trans (congrArg (fun m : Ram ↦ m[_]?) memory)
  have frameU : ExponentFrame s u := ExponentFrame.of_scalarFrame fu
    ((exponent_word_of_bytes (n := 64) (fun j hj ↦ bytes (off := 672) (by decide) (by decide) hj)).trans state.data.output)
  refine ⟨u,fuel+3+fc,(run.trans setup).trans called,frameU,ipu,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    apply (state.data.table i hi).of_bytes_eq
    intro j hj
    have h := copied (32*i+j) (by omega)
    have source : stackPtr s-1256#64=exponentFrameBase s+160#64 :=
      (ExponentTail.frame_address (off := 160) (by decide)).symm
    have destination : stackPtr s-592#64=exponentFrameBase s+824#64 :=
      (ExponentTail.frame_address (off := 824) (by decide)).symm
    change u.external[stackPtr s-592#64+BitVec.ofNat 64 (32*i+j)]?=
      v.external[stackPtr s-1256#64+BitVec.ofNat 64 (32*i+j)]? at h
    rw [source,destination,memory] at h
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using h
  · refine ⟨state.data.exponent.1,?_⟩
    intro j hj
    exact (bytes (off := 1336) (by omega) (by decide) hj).trans (state.data.exponent.2 j hj)
  · exact (regs .r14 (by simp)).trans ((g.read (n := 64) (r := 14) (by simp)).trans state.bitCount)
  · exact (regs .r15 (by simp)).trans ((g.read (n := 64) (r := 15) (by simp)).trans state.parameter)
  · exact (regs .r12 (by simp)).trans ((g.read (n := 64) (r := 12) (by simp)).trans state.inverse)
  · exact (exponent_word_of_bytes (n := 64) (fun j hj ↦ bytes (off := 712) (by decide) (by decide) hj)).trans inverse

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
