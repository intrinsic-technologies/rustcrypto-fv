import P256.Proofs.Signing.Core.Iteration.Point.Multiply.Correct
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks.B10123a
import P256.Proofs.Field.Inverse

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Standards.SECG.ECC P256.Spec.Operations
open Projective.Multiply Projective.Multiply.Machine
open Projective.Multiply.Machine.Basepoint (basePoint register_block)
open NextNonce (scalarFrame coreFrame)
open Blocks

structure Inverted [Bindings] (s t : RamState) (point : Projective) : Prop where
  frame : Frame s t
  projective : ProjectiveAt t (frameBase s+176) point
  inverse : Field.MontgomeryAt t (frameBase s+432) (Curve.inverse domain.p point.z)
  flag : t.external[frameBase s+464]? = some (if point.z = 0 then 0 else 1)
  rbp : t.regValue .rbp = frameBase s+528
  r13 : t.regValue .r13 = frameBase s+432
  r15 : t.regValue .r15 = frameBase s+1328
  rbx : t.regValue .rbx = frameBase s+240

def inverseSite : Loop.CallSite 0x114090 :=
  ⟨0xcf7d,0x710e,by decide,by decide +kernel,by decide +kernel⟩

theorem inverse_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (state : Multiply.Multiplied s t nonce) (rip : t.RIP = 0x10cf6f) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cf82 ∧
      Inverted s u (model basePoint nonce) ∧ Preserved s t u := by
  obtain ⟨n,v,run,sf,ef,memory⟩ := register_block (offset := 0xcf6f)
    (scalarFrame state.frame) (b10123a_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip
    (by simp [b10123aEffect,Effect.components,Component.Covers])
    (by simp [b10123aEffect,Effect.components]) (by simp [b10123aEffect,Effect.components])
    (by simp [b10123aEffect,Effect.components]) (by simp [b10123aEffect,Effect.components])
  have frame := coreFrame sf
  have src : v.regValue .rsi = frameBase s+240 :=
    ef.writes.2.2.trans (congrArg (·+240) state.frame.rsp)
  have dst : v.regValue .rdi = frameBase s+432 := ef.writes.1.trans state.registers.r13
  obtain ⟨w,called,ready,effect⟩ := call_site pre frame inverseSite
    (inProgram_of_textOffset 0x14090 (by decide)) ef.rip
  have cp : Field.Inverse.Pre w boundary :=
    local_call_pre pre frame ready effect (inProgram_of_textOffset 0xcf82 (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) src dst
  have srcW : w.regValue .rsi = frameBase s+240 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have dstW : w.regValue .rdi = frameBase s+432 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have z : Field.MontgomeryAt w (w.regValue .rsi) (model basePoint nonce).z := by
    rw [srcW]
    have original : Field.MontgomeryAt t (frameBase s+240) (model basePoint nonce).z := by
      simpa only [BitVec.add_assoc,show (176 : BitVec 64)+64 = 240 from rfl] using state.point.2.2
    apply original.of_bytes_eq
    intro i hi
    simpa only [memory,BitVec.ofNat_eq_ofNat] using local_call_copy frame effect (offset := 240) (len := 32) (by decide) i hi
  obtain ⟨u,result,value,flag⟩ := Field.Inverse.inverse_correct cp z
  obtain ⟨m,executed⟩ := result.execution
  have regs := call_registers effect result
  have kept : ∀ offset len, offset+len ≤ 2280 → (offset+len ≤ 432 ∨ 472 ≤ offset) →
      ∀ i < len, u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro offset len bound apart i hi
    simpa only [memory] using local_result_copy pre frame effect result dst bound (by decide) apart i hi
  refine ⟨n+1+m,u,(run.trans called).trans executed,result.rip.trans (callEffect_stack effect).1,
    ⟨after_call pre frame ready effect result (by decide) (by decide) dst,?_,dstW ▸ value,?_,?_,?_,?_,?_⟩,?_⟩
  · apply state.point.of_bytes_eq
    exact kept 176 96 (by decide) (.inl (by decide))
  · simpa only [dstW,BitVec.add_assoc,show (432 : BitVec 64)+32 = 464 from rfl] using flag
  · exact (regs .rbp (by simp)).trans ((ef.agrees.read (n := 64) (r := 5)
      (by simp [b10123aEffect,Effect.components])).trans state.registers.rbp)
  · exact (regs .r13 (by simp)).trans ((ef.agrees.read (n := 64) (r := 13)
      (by simp [b10123aEffect,Effect.components])).trans state.registers.r13)
  · exact (regs .r15 (by simp)).trans ((ef.agrees.read (n := 64) (r := 15)
      (by simp [b10123aEffect,Effect.components])).trans state.registers.r15)
  · exact (regs .rbx (by simp)).trans (ef.writes.2.1.trans (congrArg (·+240) state.frame.rsp))
  · intro i hi
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using kept i 1
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega) 0 (by decide)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize
