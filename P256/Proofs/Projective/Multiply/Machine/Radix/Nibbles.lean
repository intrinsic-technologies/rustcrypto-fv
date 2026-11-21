import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Sequence
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.SpecialRun
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.FinishRun

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix
open Recenter (rawDigit)

theorem nibbles_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t)
    (rip : t.RIP = 0x10b77f)
    (bytes : X86Proofs.Bytes t.external (stackPtr s - 40) 32
      (fun i => UInt8.ofNat (d / 256 ^ (31-i) % 256)))
    (last : (Operand.mem (stackPtr s - 48) : Operand 8).read t = 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ NibbleState s u d ∧
      AgreesExcept (digitComponents s) t u := by
  have initial : ExtractionState s t d 0 := ⟨state,bytes,by intro i hi; omega,last,by omega⟩
  obtain ⟨n1,t1,r1,s1,ip1,a1⟩ := firstPair_run pre initial rip
  have code1 : ∀ i : Fin 4, Extracted.textBytes.toListFrom (0xb793+21*i.val) 21 =
      pairBytes (BitVec.ofNat 8 (111-(1+i.val))) (BitVec.ofNat 8 (8+2*(1+i.val)))
        (BitVec.ofNat 8 (9+2*(1+i.val))) := by decide +kernel
  obtain ⟨n2,t2,r2,s2,ip2,a2⟩ := pairs_run (pc := 0xb793) pre s1 (by decide) 4 (by decide) ip1
    (fun i hi => code1 ⟨i,hi⟩) (by decide)
  obtain ⟨n3,t3,r3,s3,ip3,a3⟩ := doublePair_run (pc := 0xb7e7) pre s2 (by decide) (by decide) ip2
    (by decide +kernel) (by decide)
  have code2 : ∀ i : Fin 4, Extracted.textBytes.toListFrom (0xb813+21*i.val) 21 =
      pairBytes (BitVec.ofNat 8 (111-(7+i.val))) (BitVec.ofNat 8 (8+2*(7+i.val)))
        (BitVec.ofNat 8 (9+2*(7+i.val))) := by decide +kernel
  obtain ⟨n4,t4,r4,s4,ip4,a4⟩ := pairs_run (pc := 0xb813) pre s3 (by decide) 4 (by decide) ip3
    (fun i hi => code2 ⟨i,hi⟩) (by decide)
  obtain ⟨n5,t5,r5,s5,ip5,a5⟩ := doublePair_run (pc := 0xb867) pre s4 (by decide) (by decide) ip4
    (by decide +kernel) (by decide)
  have code3 : ∀ i : Fin 19, Extracted.textBytes.toListFrom (0xb893+21*i.val) 21 =
      pairBytes (BitVec.ofNat 8 (111-(13+i.val))) (BitVec.ofNat 8 (8+2*(13+i.val)))
        (BitVec.ofNat 8 (9+2*(13+i.val))) := by decide +kernel
  obtain ⟨n6,t6,r6,s6,ip6,a6⟩ := pairs_run (pc := 0xb893) pre s5 (by decide) 19 (by decide) ip5
    (fun i hi => code3 ⟨i,hi⟩) (by decide)
  obtain ⟨n7,u,r7,result,a7⟩ := extraction_finish pre s6 ip6
  refine ⟨n1+n2+n3+n4+n5+n6+n7,u,
    (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7,result,?_⟩
  exact ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).mono (by simp)

end P256.Proofs.Projective.Multiply.Machine.Radix
