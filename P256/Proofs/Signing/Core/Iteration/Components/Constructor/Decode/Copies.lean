import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.CopyFrame
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Copy.FirstResult
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Copy.SecondResult
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Copy.RightInput
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Input

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program (CalleePre)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem save_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x109955 else 0x1098cc)
    (scalar : Nat256At t (stackPtr t + 8) value) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if second then 0x10997d else 0x1098f4) ∧
      Nat256At u (stackPtr u + (if second then 96 else 64)) value ∧
      AgreesExcept (P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components (stackPtr t + (if second then 96 else 64))) t u := by
  let off : Nat := if second then 96 else 64
  let src : RamState → BitVec 64 := fun v => stackPtr v + 8
  let dst : RamState → BitVec 64 := fun v => stackPtr v + BitVec.ofNat 64 off
  let ip : BitVec 64 := if second then 0x109955 else 0x1098cc
  let next : BitVec 64 := if second then 0x10997d else 0x1098f4
  let code := if second then codeRange ip Copy.SecondResult.bytes else codeRange ip Copy.FirstResult.bytes
  have readable : MemReadable t (src t) 32 := stack_readable pre state.toFrame (by decide)
  have apart : RangeApart (dst t) 32 (src t) 32 :=
    RangeApart.offsets (stackPtr t) (by cases second <;> decide) (by decide)
      (.inr (by cases second <;> decide))
  have cp := copy_stack_pre pre state.toFrame (offset := off)
    (by cases second <;> decide) rfl rip readable apart
  have block : AdvanceTriple boundary (Copy32.Pre ip src dst) code
      (Effect.post (P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.effect next src dst)) := by
    cases second
    · exact Copy.FirstResult.run boundary pre.outerBoundary
    · exact Copy.SecondResult.run boundary pre.outerBoundary
  have hc : CodeIn code t := by
    cases second
    · exact Copy.FirstResult.code state.loaded
    · exact Copy.SecondResult.code state.loaded
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block t
    (Program.readyToStep state.machine state.bindingsSupported) hc cp
  have agree := P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.frame effect
  have dst' : dst t = stackPtr s - BitVec.ofNat 64 (216-off) :=
    Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide)
      (by cases second <;> decide)
  have writes : WritesWithin (P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components (dst t))
      #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hmem a ha
    simp only [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [dst'] at ha
    exact ⟨workRegion s, by simp, Program.ScalarFrame.Work.contains pre
      (by cases second <;> decide) (by cases second <;> decide) ha⟩
  have ust := state.after pre run ready agree writes
    ((agree.read (n := 64) (r := 4) (by simp [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components])).trans state.rsp)
    (by simp [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components])
  have sp : stackPtr u = stackPtr t := agree.read (n := 64) (r := 4) (by simp [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components])
  have output : MemReadable u (dst t) 32 := by
    have h := stack_readable pre ust.toFrame (offset := off) (len := 32) (by cases second <;> decide)
    simpa [dst, sp] using h
  have payload := P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.copy_nat256 effect output scalar
  refine ⟨u, ust, effect.rip, ?_, ?_⟩
  · cases second <;> simpa [dst, off, sp] using payload
  · cases second <;> exact agree


theorem copy_right [Bindings] {s t : RamState} {boundary : ReturnBoundary} {b : Nat}
    (pre : ConstructorPre s boundary) (state : Stage s t boundary)
    (rip : t.RIP = 0x1098f4) (source : t.regValue .r14 = s.regValue .rdx)
    (scalar : Nat256At s (s.regValue .rdx) b) :
    ∃ u, Stage s u boundary ∧ u.RIP = 0x109923 ∧
      Nat256At u (stackPtr u + 128#64) b ∧
      AgreesExcept (Copy32.components (stackPtr t + 128#64)) t u := by
  have read : MemReadable t (t.regValue .r14) 32 := by
    rw [source]
    exact Program.readable_of_grow
      (P256.Proofs.Program.memoryRegion_memReadable pre.rightBounded pre.rightAllocated
        (Nat.le_refl _) (Nat.le_refl _)) state.allocated
  have apart : RangeApart (stackPtr t + 128#64) 32 (t.regValue .r14) 32 := by
    rw [source, Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (offset := 128) (by decide)]
    intro i hi j hj eq
    apply pre.rightStack _
      (P256.Proofs.Program.memoryRegion_contains_add pre.rightBounded
        (Nat.le_refl _) (Nat.le_refl _) hj)
    rw [← eq]
    exact Program.ScalarFrame.stack_contains pre.toCalleePre
      (offset := 88) (by decide) (by decide) ⟨i, hi, rfl⟩
  have cp := copy_stack_pre pre.toCalleePre state.toFrame (offset := 128)
    (source := fun v => v.regValue .r14) (destination := fun v => stackPtr v + 128#64)
    (by decide) rfl rip read apart
  obtain ⟨u, ust, effect⟩ := copy_execute pre.toCalleePre state
    (Copy.RightInput.run boundary pre.outerBoundary) (Copy.RightInput.code state.loaded) cp
    (offset := 128) (by decide) rfl
  have agree : AgreesExcept (Copy32.components (stackPtr t + 128#64)) t u := Copy32.frame effect
  have sp : stackPtr u = stackPtr t := agree.read (n := 64) (r := 4) (by simp [Copy32.components])
  have value : Nat256At t (t.regValue .r14) b := by
    rw [source]
    exact state.toFrame.right_scalar pre scalar
  have output : MemReadable u (stackPtr t + 128#64) 32 := by
    rw [← sp]
    exact stack_readable pre.toCalleePre ust.toFrame (by decide)
  have copied : Nat256At u (stackPtr t + 128#64) b :=
    ⟨value.1, fun i hi => (Copy32.copy_bytes effect read output i hi).trans (value.2 i hi)⟩
  exact ⟨u, ust, effect.rip, by rw [sp]; exact copied, agree⟩

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
