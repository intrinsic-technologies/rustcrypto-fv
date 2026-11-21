import P256.Proofs.Ecdh.Interface
import P256.Proofs.Ecdh.Prepare.RadixArgs
import P256.Proofs.Ecdh.Prepare.Radix
import P256.Proofs.Ecdh.Prepare.CopyArgs
import P256.Proofs.Ecdh.Prepare.Copy
import P256.Proofs.Ecdh.Prepare.MultiplyArgs
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Prepare
open Projective.Multiply

private theorem scalar_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 3464])
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d) :
    SecretKeyFromBytes.Scalar.Nat256At t (s.regValue .rsi) d := by
  refine ⟨scalar.1, fun i hi => (frame _ ?_).trans (scalar.2 i hi)⟩
  intro region hr hin
  have input := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 3464 := by simpa using hr
  rcases cases with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ input hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ input hin

theorem prepare_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    {point : Standards.SECG.ECC.Curve.Point}
    (pre : Pre s boundary) (prepared : Prepared s t point)
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d) :
    ∃ fuel u, Advances boundary fuel t u ∧ Ready s u d point := by
  have base : stackPtr t = frameBase s := prepared.rsp
  have digitAddress : frameBase s + 80 = stackPtr s - 1976 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have tableAddress : frameBase s + 1016 = stackPtr s - 1040 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have copiedAddress : frameBase s + 248 = stackPtr s - 1808 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  obtain ⟨n,a,runA,stA,effA⟩ := radixArgs_correct pre.toCalleePre prepared.toFrameState prepared.rip
  have memoryA : a.external = t.external := effA.agrees.external (by
    simp [radixArgsEffect,Effect.components,Component.Covers])
  have r14A : a.regValue .r14 = stackPtr s-1976 := by
    have h : a.regValue .r14 = stackPtr t+80 := effA.writes.1
    exact h.trans (scalar_stack_address prepared.rsp (by decide) (by decide))
  have dstA : a.regValue .rdi = stackPtr s-1976 := by
    have h : a.regValue .rdi = stackPtr t+80 := effA.writes.2.1
    exact h.trans (scalar_stack_address prepared.rsp (by decide) (by decide))
  have srcA : a.regValue .rsi = s.regValue .rsi := by
    have h : a.regValue .rsi = memLoad t.external (stackPtr t+8) 64 := effA.writes.2.2
    rw [base] at h
    exact h.trans prepared.scalar
  obtain ⟨m,b,runB,stB,ripB,digitsB,savedB,tableB⟩ := radix_call pre.toCalleePre stA effA.rip
    srcA dstA (scalar_of_frame pre.toCalleePre stA.frame scalar)
  have r14B : b.regValue .r14 = stackPtr s-1976 := (savedB .r14 (by simp)).trans r14A
  obtain ⟨k,c,runC,stC,effC⟩ := copyArgs_correct pre.toCalleePre stB ripB
  have memoryC : c.external = b.external := effC.agrees.external (by
    simp [copyArgsEffect,Effect.components,Component.Covers])
  have r15C : c.regValue .r15 = stackPtr s-1808 := by
    have h : c.regValue .r15 = stackPtr b+248 := effC.writes.1
    exact h.trans (scalar_stack_address stB.rsp (by decide) (by decide))
  have dstC : c.regValue .rdi = stackPtr s-1808 := by
    have h : c.regValue .rdi = stackPtr b+248 := effC.writes.2.2.1
    exact h.trans (scalar_stack_address stB.rsp (by decide) (by decide))
  have srcC : c.regValue .rsi = stackPtr s-1040 := by
    have h : c.regValue .rsi = stackPtr b+1016 := effC.writes.2.2.2
    exact h.trans (scalar_stack_address stB.rsp (by decide) (by decide))
  obtain ⟨l,e,runE,stE,ripE,tableE,savedE,digitsE⟩ :=
    copy_call pre.toCalleePre stC effC.rip srcC dstC effC.writes.2.1
  obtain ⟨j,u,runU,stU,effU⟩ := multiplyArgs_correct pre.toCalleePre stE ripE
  have memoryU : u.external = e.external := effU.agrees.external (by
    simp [multiplyArgsEffect,Effect.components,Component.Covers])
  refine ⟨n+m+k+l+j,u,(((runA.trans runB).trans runC).trans runE).trans runU,
    stU,effU.rip,?_,?_,?_,effU.writes.2.1,effU.writes.2.2.1,?_,?_,?_⟩
  · exact ((effU.agrees.read (n := 64) (r := 3)
      (by simp [multiplyArgsEffect,Effect.components])).trans
      ((savedE .rbx (by simp)).trans
        ((effC.agrees.read (n := 64) (r := 3)
          (by simp [copyArgsEffect,Effect.components])).trans
          ((savedB .rbx (by simp)).trans
            ((effA.agrees.read (n := 64) (r := 3)
              (by simp [radixArgsEffect,Effect.components])).trans prepared.output)))))
  · have h : u.regValue .rdi = stackPtr e+152 := effU.writes.1
    exact h.trans (congrArg (fun x : BitVec 64 => x+152) stE.rsp)
  · rw [copiedAddress]
    exact effU.writes.2.2.2.1.trans ((savedE .r15 (by simp)).trans r15C)
  · rw [digitAddress]
    exact effU.writes.2.2.2.2.trans ((savedE .r14 (by simp)).trans
      ((effC.agrees.read (n := 64) (r := 14)
        (by simp [copyArgsEffect,Effect.components])).trans r14B))
  · intro index
    apply (prepared.table index).of_bytes_eq
    intro i hi
    rw [copiedAddress,tableAddress,memoryU,BitVec.add_assoc,← BitVec.ofNat_add,
      tableE _ (by have := index.isLt; omega),memoryC,
      tableB _ (by have := index.isLt; omega),memoryA]
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
  · intro i hi
    rw [digitAddress,memoryU,digitsE i hi,memoryC]
    exact digitsB i hi

end P256.Proofs.Ecdh
