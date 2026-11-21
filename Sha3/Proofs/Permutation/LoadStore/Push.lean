import Sha3.Proofs.Permutation.LoadStore.Memory
import Sha3.Proofs.Machine

namespace X86Proofs

open X86 X86.Machine X86.UserProcess Sha3.Spec.Program

def PushPreReadable (p : BitVec 64) (s : RamState) : Prop :=
  StorePreReadable p pushAddr 8 s ∧ (pushAddr s).toNat % 4096 + 8 ≤ 4096

theorem push_r64_encoded_effect_step_of_readable [Bindings] (p : BitVec 64)
    (src : BitVec 4) :
    StepEffect (PushPreReadable p) (codeRange p (encodePushR64 src))
      (pushR64Effect p (encodePushR64 src).length (src.setWidth 5)) := by
  intro s hready hcode hpre
  have hlen : 0 < (encodePushR64 src).length ∧ (encodePushR64 src).length ≤ 15 := by
    rcases encodePushR64_spec src with ⟨_, hbytes, _⟩ | ⟨_, _, hbytes, _⟩ <;>
      simp only [hbytes, List.length_cons, List.length_nil] <;> decide
  have hp := hpre.1.1.rip
  have hstep := Sha3.Proofs.push_r64_step_of_register_readable s hready src
    (hp ▸ hcode.bytesAt) (hp ▸ hcode.low hlen.1 (by omega)) hpre.1.1.read hpre.2
  refine ⟨pushAfter s src, hstep, ?_, ?_⟩
  · apply hready.of_agreesExcept (AgreesExcept.afterStep_push s _ _ _)
    rw [afterStep_push_external]
    exact identityPageTableMemory_memStore_of_notInPageTables s _ _
      hready.memory.tables hpre.1.2
  · refine ⟨?_, ?_, trivial, ?_⟩
    · exact (afterStep_push_rip hready _ _ _).trans
        (congrArg (· + BitVec.ofNat 64 (encodePushR64 src).length) hp)
    · exact ⟨Operand.read_afterStep_push_rsp s _ _ _,
        Operand.read_afterStep_push_mem s _ _ _⟩
    · exact (pushR64Effect_components _ _ _ s).symm ▸ AgreesExcept.afterStep_push s _ _ _

end X86Proofs
