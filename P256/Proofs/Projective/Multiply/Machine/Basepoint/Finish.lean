import P256.Proofs.Projective.Multiply.Machine.Basepoint.Prepared
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Registers
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish.RadixArgs
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish.Radix
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish.CopyArgs
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish.Copy
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish.MultiplyArgs
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Finish

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (prepared : Prepared s t boundary)
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d) :
    ∃ u, Ready s u boundary d := by
  obtain ⟨n,a,runA,stA,effA⟩ := radixArgs_correct pre prepared.toFrameState prepared.rip
  have memoryA : a.external = t.external := effA.agrees.external (by
    simp [radixArgsEffect,Effect.components,Component.Covers])
  have r14A : a.regValue .r14 = stackPtr s-1784 := by
    have h : a.regValue .r14 = stackPtr t+160 := effA.writes.1
    exact h.trans (scalar_stack_address prepared.rsp (by decide) (by decide))
  have dstA : a.regValue .rdi = stackPtr s-1784 := by
    have h : a.regValue .rdi = stackPtr t+160 := effA.writes.2.1
    exact h.trans (scalar_stack_address prepared.rsp (by decide) (by decide))
  have srcA : a.regValue .rsi = s.regValue .rsi := effA.writes.2.2.trans prepared.scalar
  obtain ⟨m,b,runB,stB,ripB,digitsB,savedB,tableB⟩ := radix_call pre stA effA.rip
    srcA dstA (scalar_of_frame pre stA.frame scalar)
  have r14B : b.regValue .r14 = stackPtr s-1784 :=
    (savedB .r14 (by simp)).trans r14A
  obtain ⟨k,c,runC,stC,effC⟩ := copyArgs_correct pre stB ripB
  have memoryC : c.external = b.external := effC.agrees.external (by
    simp [copyArgsEffect,Effect.components,Component.Covers])
  have r15C : c.regValue .r15 = stackPtr s-912 := by
    have h : c.regValue .r15 = stackPtr b+1032 := effC.writes.1
    exact h.trans (scalar_stack_address stB.rsp (by decide) (by decide))
  have dstC : c.regValue .rdi = stackPtr s-912 := by
    have h : c.regValue .rdi = stackPtr b+1032 := effC.writes.2.2.1
    exact h.trans (scalar_stack_address stB.rsp (by decide) (by decide))
  have srcC : c.regValue .rsi = stackPtr s-1680 := by
    have h : c.regValue .rsi = stackPtr b+264 := effC.writes.2.2.2
    exact h.trans (scalar_stack_address stB.rsp (by decide) (by decide))
  obtain ⟨l,e,runE,stE,ripE,tableE,savedE,digitsE⟩ :=
    copy_call pre stC effC.rip srcC dstC effC.writes.2.1
  obtain ⟨j,u,runU,stU,effU⟩ := multiplyArgs_correct pre stE ripE
  have memoryU : u.external = e.external := effU.agrees.external (by
    simp [multiplyArgsEffect,Effect.components,Component.Covers])
  refine ⟨u,stU,?_,effU.rip,?_,?_,effU.writes.2.2.2.1.trans
    ((savedE .r15 (by simp)).trans r15C),effU.writes.2.1,?_,effU.writes.2.2.1,?_,?_⟩
  · obtain ⟨fuel,run⟩ := prepared.execution
    exact ⟨fuel+n+m+k+l+j,((((run.trans runA).trans runB).trans runC).trans runE).trans runU⟩
  · exact ((effU.agrees.read (n := 64) (r := 3)
      (by simp [multiplyArgsEffect,Effect.components])).trans
      ((savedE .rbx (by simp)).trans
        ((effC.agrees.read (n := 64) (r := 3)
          (by simp [copyArgsEffect,Effect.components])).trans
          ((savedB .rbx (by simp)).trans
            ((effA.agrees.read (n := 64) (r := 3)
              (by simp [radixArgsEffect,Effect.components])).trans prepared.output)))))
  · have h : u.regValue .rdi = stackPtr e+64 := effU.writes.1
    exact h.trans (scalar_stack_address stE.rsp (by decide) (by decide))
  · exact effU.writes.2.2.2.2.trans ((savedE .r14 (by simp)).trans
      ((effC.agrees.read (n := 64) (r := 14)
        (by simp [copyArgsEffect,Effect.components])).trans r14B))
  · intro index
    apply (prepared.table index).of_bytes_eq
    intro i hi
    rw [memoryU,BitVec.add_assoc,← BitVec.ofNat_add,
      tableE _ (by have := index.isLt; omega),memoryC,
      tableB _ (by have := index.isLt; omega),memoryA]
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
  · intro i hi
    rw [memoryU,digitsE i hi,memoryC]
    exact digitsB i hi

end P256.Proofs.Projective.Multiply.Machine.Basepoint
