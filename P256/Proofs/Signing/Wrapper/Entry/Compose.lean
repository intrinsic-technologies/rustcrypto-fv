import P256.Proofs.Signing.Wrapper.Entry.Stages

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

theorem correct_of_contracts (decode : DecodeContract) (construct : ConstructContract)
    (hashCall : HashCallContract) : EntryContract := by
  intro bindings initial secret message context
  obtain ⟨slices, call⟩ := context.call
  obtain ⟨s, guarded⟩ := guards_correct context.bindingsSupported context.machine call
  obtain ⟨_, t, _, decoded⟩ := decode context guarded
  obtain ⟨_, u, _, constructed⟩ := construct context decoded
  obtain ⟨_, v, _, entered⟩ := hashCall context constructed
  exact ⟨v, entered⟩

end P256.Proofs.Signing.Wrapper.Entry
