import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Select.Prefix
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Dead
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Select.Limbs

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem select_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {a r : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} {high b : BitVec 64}
    (he : Entry entry) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (memory : MemoryPre s)
    (rip : s.RIP = entry + 0x509#64) (input : Input s a high)
    (difference : Difference s r b) (hb : b = 0 ∨ b = 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = entry + 0x5ab#64 ∧
      Nat256At t (s.regValue .rdi) (selectLimbs a r (selector high b)).toNat ∧
      AgreesExcept (components s) s t := by
  obtain ⟨n1,s1,run1,ready1,loaded1,rip1,byte1,frame1⟩ :=
    prefix_correct he ready loaded hout memory rip input.hi difference.negBorrow
  have wide1 := prefix_frame frame1
  obtain ⟨s2,run2,ready2,loaded2,memory2,rip2,frame2⟩ :=
    dead_correct he ready1 loaded1 hout (memory.of_scratch wide1) rip1
  have frames12 := frame1.trans frame2
  have wide12 := scratch_trans wide1 (dead_wide frame2)
  have input2 : Input s2 a ((Operand.reg 15 : Operand 64).read s2) := by
    refine ⟨?_,?_,?_,?_,rfl⟩
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans input.l0
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans input.l1
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans input.l2
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans input.l3
  have difference2 : Difference s2 r b := by
    constructor
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans difference.l0
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans difference.l1
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans difference.l2
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans difference.l3
    · exact (frames12.read (by simp [prefixComponents, deadComponents])).trans difference.negBorrow
  have byte2 : (Operand.reg 5 : Operand 8).read s2 =
      (if high = 0 then 1 else 0) &&& (-b).setWidth 8 :=
    (frame2.read (by simp [deadComponents])).trans byte1
  obtain ⟨n3,s3,run3,ready3,loaded3,rip3,selected3,frame3⟩ :=
    select_limbs_correct he ready2 loaded2 hout memory2 rip2 input2 difference2 byte2
  rw [selector_byte high b hb] at selected3
  have wide123 := scratch_trans wide12 frame3
  obtain ⟨n4,s4,run4,ready4,loaded4,rip4,output4,frame4⟩ :=
    stores_correct he ready3 loaded3 hout (memory.of_scratch wide123) rip3 selected3
  have wide4 : AgreesExcept (components s3) s3 s4 :=
    frame4.mono (by simp [components, scratchComponents])
  refine ⟨n1+10+n3+n4,s4,((run1.trans run2).trans run3).trans run4,
    ready4,loaded4,rip4,?_,scratch_then_components wide123 wide4⟩
  simpa only [scratch_rdi wide123] using output4

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
