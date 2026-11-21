import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_compose] def forgetFlags (e : RamState → Effect) (s : RamState) : Effect :=
  { e s with flags := some ⟨none, none, none, none, none, none⟩ }

theorem forgetFlags_step [Bindings] {P : RamState → Prop} {code : CodeMap}
    {e : RamState → Effect} (h : StepEffect P code e) :
    StepEffect P code (forgetFlags e) := by
  intro s hReady hCode hPre
  obtain ⟨t, hStep, hReady', hEffect⟩ := h s hReady hCode hPre
  refine ⟨t, hStep, hReady', hEffect.rip, hEffect.writes, ?_, hEffect.agrees.mono ?_⟩
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · intro c hc
    cases hf : (e s).flags <;>
      simp only [Effect.components, forgetFlags, hf, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc ⊢
    · rcases hc with hc | hc
      · exact Or.inl (Or.inl hc)
      · exact Or.inr hc
    · exact hc

@[x86_local] theorem forgetFlags_local {e : RamState → Effect} (h : Effect.Local e) :
    Effect.Local (forgetFlags e) := by
  refine ⟨h.rip, h.writes, fun _ _ _ ↦ rfl, ?_, h.full⟩
  intro t t' ho i hi
  cases i <;> rfl

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
