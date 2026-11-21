import P256.Proofs.Generate.Sampler.Nonzero.ClearBlock
import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

def clearClobbers (t : RamState) : List Component :=
  [.mem (stackPtr t+104) 8,.mem (stackPtr t+96) 8,
    .mem (stackPtr t+88) 8,.mem (stackPtr t+80) 8,.rip]

theorem clear [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c48) :
    ∃ n u, Advances boundary n t u ∧ State s u ∧ u.RIP = 0x100c6c ∧
      Nat256At u (stackPtr u+80) 0 ∧ AgreesExcept (clearClobbers t) t u := by
  have hp : ClearBlock.ClearPre t := by
    refine ⟨rip,?_,?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact (state.stack_writable pre (by decide)).crossPage (by decide)
    · intro i hi off len bound
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact state.stack_code pre (by decide) bound
  obtain ⟨n,u,run,ready,_,effect⟩ := ClearBlock.clear_words boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (ClearBlock.clear_loaded state.loaded) hp
  have g : AgreesExcept (clearClobbers t) t u := by
    simpa [clearClobbers,ClearBlock.clearEffect,Effect.components] using effect.agrees
  have sp : stackPtr u = stackPtr t := g.read (n := 64) (r := 4) (by simp [clearClobbers])
  have su := state.after pre ready g (by
    intro c hc a ha
    simp only [clearClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals exact ⟨workRegion s 3624,by simp [bodyWrites],state.work_writes pre (by decide) ha⟩) sp
  refine ⟨n,u,run,su,effect.rip,?_,g⟩
  apply Field.Inverse.nat256At_zero_limbs
  · exact (su.stack_readable pre (offset := 80) (len := 32) (by decide)).mem
  · have words := effect.writes
    change memLoad u.external (stackPtr t+104) 64 = 0 ∧
      memLoad u.external (stackPtr t+96) 64 = 0 ∧
      memLoad u.external (stackPtr t+88) 64 = 0 ∧
      memLoad u.external (stackPtr t+80) 64 = 0 at words
    rw [sp]
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using
      And.intro words.2.2.2 (And.intro words.2.2.1 (And.intro words.2.1 words.1))

end P256.Proofs.Generate.Sampler.Nonzero
