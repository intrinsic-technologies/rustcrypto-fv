import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

@[x86_compose] def Effect.forgetFlags (e : Effect) : Effect :=
  { e with flags := some ⟨none, none, none, none, none, none⟩ }

theorem Effect.Holds.forgetFlags {e : Effect} {s t : RamState} (h : e.Holds s t) :
    (P256.Proofs.Common.Instructions.Effect.forgetFlags (e := e)).Holds s t := by
  refine ⟨h.rip, h.writes, ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, ?_⟩
  apply h.agrees.mono
  cases he : e.flags <;> simp only [Effect.components, Effect.forgetFlags, he,
    List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  · intro c hc
    rcases hc with hc | hc
    · exact Or.inl (Or.inl hc)
    · exact Or.inr hc
  · intro c hc
    exact hc

theorem Effect.Avoids.forgetFlags {e : Effect} {code : CodeMap} (h : e.Avoids code) :
    (P256.Proofs.Common.Instructions.Effect.forgetFlags (e := e)).Avoids code := by
  intro x hx c hc hcov
  apply h x hx c _ hcov
  cases hf : e.flags <;> cases c <;>
    simp_all [Effect.components, Effect.forgetFlags, Component.Covers]

@[x86_local] theorem Effect.Local.forgetFlags {e : RamState → Effect} (h : Effect.Local e) :
    Effect.Local (fun s => (P256.Proofs.Common.Instructions.Effect.forgetFlags (e := (e s)))) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t ho
    simp only [Effect.forgetFlags, h.rip s t ho, h.writes s t ho]
  · exact h.full

theorem StepEffect.forgetFlags [Bindings] {pre : RamState → Prop} {code : CodeMap}
    {e : RamState → Effect} (h : StepEffect pre code e) :
    StepEffect pre code (fun s => (P256.Proofs.Common.Instructions.Effect.forgetFlags (e := (e s)))) := by
  intro s ready loaded pre
  obtain ⟨t, step, ht, he⟩ := h s ready loaded pre
  exact ⟨t, step, ht, (P256.Proofs.Common.Instructions.Effect.Holds.forgetFlags (h := he))⟩

end P256.Proofs.Common.Instructions
