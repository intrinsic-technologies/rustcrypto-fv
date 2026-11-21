import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Constants
import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Entry
import P256.Proofs.Field.Subtract.Correct

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Negate

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Field

theorem negate_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : CalleePre s boundary 0x1137d0 32 32 24)
    (input : MontgomeryAt s (s.regValue .rsi) value) :
    ∃ t, CalleeResult s t boundary 32 24 ∧
      MontgomeryAt t (s.regValue .rdi) ((P256.Spec.Operations.domain.p-value) %
        P256.Spec.Operations.domain.p) := by
  obtain ⟨t,run,ready,rip,right,left,ag⟩ := entry_correct pre
  have memory : t.external = s.external := ag.external (by simp [Component.Covers])
  have rsp : t.regValue .rsp = s.regValue .rsp := ag.read (n := 64) (r := 4) (by simp)
  have dest : t.regValue .rdi = s.regValue .rdi := ag.read (n := 64) (r := 7) (by simp)
  have ins : registerRegion t .rsi 32 = (⟨0x202620,32⟩ : MemoryRegion) := by
    simp only [registerRegion,left]; rfl
  have outs : registerRegion t .rdi 32 = registerRegion s .rdi 32 := by
    simp only [registerRegion,dest]
  have rhs : registerRegion t .rdx 32 = registerRegion s .rsi 32 := by
    simp only [registerRegion,right]
  have stack : Stack.region t 24 = Stack.region s 24 := by simp only [Stack.region,rsp]
  have loaded : ProgramLoaded t := by simpa only [ProgramLoaded,memory] using pre.loaded
  have avoids := pre.avoids
  have body : BinaryFieldPre t boundary 0x113f20 24 := by
    refine ⟨⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready ag,
      supportedMachine_of_ready_agrees pre.machine ready ag,
      ag.directionFlagClear (by simp) pre.directionFlag, loaded, rip,
      ?_,?_,?_,?_,?_,?_,?_,pre.outerBoundary,?_⟩,?_,?_,?_,?_⟩
    · rw [ins]; unfold MemoryRegion.Bounded; decide +kernel
    · rw [ins]; exact zero_allocated loaded
    · simpa only [outs] using pre.outputBounded
    · simpa only [outs,memory] using pre.outputAllocated
    · simpa only [Stack.Valid,stack,Stack.returnSlot,Stack.NoUnderflow,rsp,memory] using pre.stack
    · intro i j hij
      have cases : (i=0 ∧ j=1) ∨ (i=0 ∧ j=2) ∨ (i=1 ∧ j=2) := by
        have := i.isLt; have := j.isLt
        simp only [Fin.lt_def, Fin.ext_iff] at *
        omega
      rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · change (registerRegion t .rsi 32).Disjoint (registerRegion t .rdi 32)
        rw [ins,outs]
        exact zero_disjoint (avoids _ (by simp))
      · change (registerRegion t .rsi 32).Disjoint (Stack.region t 24)
        rw [ins,stack]
        exact zero_disjoint (avoids _ (by simp))
      · change (registerRegion t .rdi 32).Disjoint (Stack.region t 24)
        rw [outs,stack]
        exact pre.separation 1 2 (by decide)
    · simpa only [outs,stack] using avoids
    · change InProgram (memLoad t.external (stackPtr t) 64)
      rw [memory, show stackPtr t = stackPtr s from rsp]
      exact pre.returnInProgram
    · simpa only [rhs] using pre.inputBounded
    · simpa only [rhs,memory] using pre.inputAllocated
    · rw [rhs,outs]; exact pre.separation 0 1 (by decide)
    · rw [rhs,stack]; exact pre.separation 0 2 (by decide)
  have lp : MontgomeryAt t (t.regValue .rsi) 0 := left ▸ zero_at loaded
  have rp : MontgomeryAt t (t.regValue .rdx) value := by
    simpa only [MontgomeryAt,SecretKeyFromBytes.Scalar.Nat256At,memory,right] using input
  obtain ⟨u,result,output⟩ := field_subtract_body_correct body lp rp
  refine ⟨u,?_,?_⟩
  · apply result.prepend_registers run memory rsp dest ?_ (ag.mxcsr (by simp)) (ag.fcw (by simp))
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ag.read (n := 64) (r := 3) (by simp)
    · exact ag.read (n := 64) (r := 5) (by simp)
    · exact ag.read (n := 64) (r := 12) (by simp)
    · exact ag.read (n := 64) (r := 13) (by simp)
    · exact ag.read (n := 64) (r := 14) (by simp)
    · exact ag.read (n := 64) (r := 15) (by simp)
  · simpa only [dest,Nat.zero_add] using output

end P256.Proofs.Projective.Multiply.Machine.Lookup.Negate
