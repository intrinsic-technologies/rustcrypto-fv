import P256.Proofs.Generate.Scalar.Compare
import P256.Proofs.Generate.Scalar.Finish

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

variable [Bindings]
theorem from_repr_correct {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : Pre s boundary) (input : (registerRegion s .rsi 32).HasBytes s.external bytes) :
    ∃ t, CalleeResult s t boundary 33 72 ∧
      SecretKeyFromBytes.Scalar.Nat256At t (s.regValue .rdi) (Arith.uint bytes) ∧
      t.external[s.regValue .rdi + 32]? =
        some (if Arith.uint bytes < Operations.domain.n then 1 else 0) ∧
      t.regValue .rax = s.regValue .rdi := by
  have bound : Arith.uint bytes < 2^256 := by
    have size : bytes.size = 32 := input.1
    simpa only [Arith.uint, Arith.decodeBigEndian, size,
      show (256:Nat)^32 = 2^256 by decide +kernel] using SecretKeyFromBytes.Encoding.octetsToNat_lt bytes
  obtain ⟨n, t, run, state, rip, rsp, output, decoded⟩ := entry_correct pre input
  have slot : stackPtr t + 8 = stackPtr s - 48 := by
    rw [rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have comparePre : ComparePre 0x112efb t := by
    refine ⟨rip, ?_, ?_⟩
    · rw [slot]
      exact writable_of_grow
        (stack_sub_writable8 pre.stack (fun a ha h => pre.avoids _ (by simp) a ha (.inr h))
          (offset := 48) (by decide) (by decide)) state.allocated
    · intro a ha
      rw [slot] at ha
      exact fun h => pre.avoids _ (by simp) a
        (ScalarFrame.stack_contains pre (by decide) (by decide) ha) (.inl h)
  obtain ⟨m, u, runU, readyU, _, preU, ag, flag⟩ :=
    compare_correct pre.outerBoundary (readyToStep state.machine state.bindingsSupported) state.loaded comparePre
  have stateU := state.after_agrees pre readyU ag (by
    apply ag.memoryWriteFrame
    intro c hc a ha
    simp only [compareFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    rw [slot] at ha
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩)
    (by simp [compareFrame])
  have decodedU := decoded.of_agrees ag (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [compareFrame])
  have value : (compareInput t).toNat = Arith.uint bytes := by
    unfold compareInput
    rw [decoded.1, decoded.2.1, decoded.2.2.1, decoded.2.2.2]
    exact SecretKeyFromBytes.Scalar.limbs_ofNat_toNat _ bound
  rw [value] at flag
  exact finish_correct pre stateU preU.rip
    ((compare_stack ag).trans rsp)
    ((ag.read (n := 64) (r := 3) (by simp [compareFrame])).trans output)
    bound decodedU flag ⟨n+m, run.trans runU⟩

end P256.Proofs.Generate.Scalar
