import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Result
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Memory
import P256.Proofs.Signing.Core.Iteration.Point.Call
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Registers
import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Standards.SECG.ECC
open NextNonce (scalarFrame coreFrame)
open Projective.Multiply.Machine.Basepoint (register_block)
open P256.Proofs.Common.Field (AdvanceTriple)

structure Affine [Bindings] (s t : RamState) (x y : Nat) : Prop where
  frame : Frame s t
  point : Sec1.AffineAt t (frameBase s+104) (.affine x y)
  rbp : t.regValue .rbp = frameBase s+528
  r13 : t.regValue .r13 = frameBase s+432
  r14 : t.regValue .r14 = frameBase s+8
  r15 : t.regValue .r15 = frameBase s+1328

def convertArguments (s : RamState) : Effect :=
  { rip := 0x10d14e
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩] }

theorem convert_arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d148)
      (codeRange 0x10d148 [0x48,0x89,0xef,0x4c,0x89,0xfe]) (Effect.post convertArguments) := by
  advance_begin (mov_r64_r64_effect_step 0x10d148 0x48 0xef (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd14b (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d14b 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d148 [0x48,0x89,0xef,0x4c,0x89,0xfe] 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd14e (by decide))⟩
  advance_finish [convertArguments]

def convertSite : Projective.Multiply.Machine.Loop.CallSite 0x107d00 :=
  ⟨0xd14e,0xffffabad,by decide,by decide +kernel,by decide +kernel⟩

theorem convert [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : SignPre s boundary) (state : Affine s t x y) (rip : t.RIP = 0x10d111) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d153 ∧
      Converted s u x y ∧ Preserved s t u := by
  have src : Copy.Result.source t = frameBase s+104 := congrArg (·+104) state.frame.rsp
  have dst : Copy.Result.destination t = frameBase s+1328 := congrArg (·+1328) state.frame.rsp
  obtain ⟨n1,v,run1,f1,rip1,value1,ag1⟩ := Copy.execute pre state.frame
    (codeOffset := 0xd111) (sourceOffset := 104) (destinationOffset := 1328)
    (Copy.Result.copy boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by decide) (by decide) (.inl (by decide)) src dst (src.symm ▸ state.point.1)
  rw [dst] at value1 ag1
  have point1 : Sec1.AffineAt v (frameBase s+104) (.affine x y) := state.point.of_bytes_eq (by
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
      Copy.byte (offset := 1328) ag1 (by decide) (i := 104+i) (by omega) (.inl (by omega)))
  have keep1 := Copy.preserved (offset := 1328) ag1 (by decide)
    (by intro i hi; rcases hi with h|h|h|h <;> omega)
  obtain ⟨n2,w,run2,sf2,ef2,mem2⟩ := register_block (offset := 0xd148)
    (scalarFrame f1) (convert_arguments boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip1
    (by simp [convertArguments,Effect.components,Component.Covers])
    (by simp [convertArguments,Effect.components]) (by simp [convertArguments,Effect.components])
    (by simp [convertArguments,Effect.components]) (by simp [convertArguments,Effect.components])
  have f2 := coreFrame sf2
  have source : w.regValue .rsi = frameBase s+1328 := ef2.writes.2.trans
    ((ag1.read (n := 64) (r := 15) (by simp [ScalarFrame.Copy32.components])).trans state.r15)
  have dest : w.regValue .rdi = frameBase s+528 := ef2.writes.1.trans
    ((ag1.read (n := 64) (r := 5) (by simp [ScalarFrame.Copy32.components])).trans state.rbp)
  obtain ⟨c,run3,ready,ef3⟩ := call_site pre f2 convertSite
    (inProgram_of_textOffset 0x7d00 (by decide)) ef2.rip
  have cp : CalleePre c boundary 0x107d00 32 32 40 :=
    local_call_pre pre f2 ready ef3 (inProgram_of_textOffset 0xd153 (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)) source dest
  have srcC : c.regValue .rsi = frameBase s+1328 :=
    (ef3.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dstC : c.regValue .rdi = frameBase s+528 :=
    (ef3.agrees.read (n := 64) (r := 7) (by simp)).trans dest
  have valueC : Field.MontgomeryAt c (c.regValue .rsi) x := by
    rw [srcC]
    apply value1.of_bytes_eq
    intro i hi
    simpa only [mem2,BitVec.ofNat_eq_ofNat] using
      local_call_copy f2 ef3 (offset := 1328) (len := 32) (by decide) i hi
  obtain ⟨u,result,valueU⟩ := Ecdh.Normalize.Conversion.callee_correct cp valueC
  obtain ⟨n4,run4⟩ := result.execution
  have regs := call_registers ef3 result
  have kept : ∀ offset len, offset+len ≤ 2280 → (offset+len ≤ 528 ∨ 560 ≤ offset) →
      ∀ i < len, u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        v.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro off len bound apart i hi
    simpa only [mem2] using local_result_copy pre f2 ef3 result dest bound (by decide) apart i hi
  refine ⟨n1+n2+1+n4,u,((run1.trans run2).trans run3).trans run4,
    result.rip.trans (callEffect_stack ef3).1,
    ⟨after_call pre f2 ready ef3 result (by decide) (by decide) dest,?_,dstC ▸ valueU,?_,?_,?_⟩,?_⟩
  · exact point1.of_bytes_eq (kept 104 65 (by decide) (.inl (by decide)))
  · exact (regs .rbp (by simp)).trans ((ef2.agrees.read (n := 64) (r := 5)
      (by simp [convertArguments,Effect.components])).trans
      ((ag1.read (n := 64) (r := 5) (by simp [ScalarFrame.Copy32.components])).trans state.rbp))
  · exact (regs .r13 (by simp)).trans ((ef2.agrees.read (n := 64) (r := 13)
      (by simp [convertArguments,Effect.components])).trans
      ((ag1.read (n := 64) (r := 13) (by simp [ScalarFrame.Copy32.components])).trans state.r13))
  · exact (regs .r15 (by simp)).trans ((ef2.agrees.read (n := 64) (r := 15)
      (by simp [convertArguments,Effect.components])).trans
      ((ag1.read (n := 64) (r := 15) (by simp [ScalarFrame.Copy32.components])).trans state.r15))
  · intro i hi
    have h := kept i 1 (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) 0 (by decide)
    simp only [BitVec.add_zero] at h
    exact h.trans (keep1 i hi)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize
