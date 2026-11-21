import K256.Proofs.Generate.Wrapper.Frame

namespace K256.Proofs.Generate.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Refine

variable {s : RamState} {random : ByteArray} {mem : Ram}

theorem image_of_frame (call : ValidCall signingKeyGenerateFromRng s [random])
    (frame : RamWriteFrame s.external mem (regions s).toList) :
    ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2 := by
  let t := { s with external := mem }
  have writes : MemoryWriteFrame s t (regions s) :=
    frame.memoryWriteFrame fun _ h r hr => h r (Vector.mem_toList_iff.mp hr)
  have loaded := Common.programLoaded_of_memoryWriteFrame writes call.programLoaded (by
    intro r hr a ha hp
    apply (call.separation.2 r (show r ∈ (regions s).toList from Vector.mem_toList_iff.mpr hr)).1 a ha
    exact Or.inl hp)
  exact fun x hx => loaded x.1 x.2 (Common.programSections_fetchByte_of_mem hx)

theorem output_stack_apart (call : ValidCall signingKeyGenerateFromRng s [random]) :
    (s.regValue .rdi).toNat + 97 ≤ (s.regValue .rsp).toNat - 10584 ∨
      (s.regValue .rsp).toNat + 8 ≤ (s.regValue .rdi).toNat := by
  have sep : (outputRegion signingKeyGenerateFromRng s).Disjoint
      (Stack.region s signingKeyGenerateFromRng.minStackBytes) :=
    (List.pairwise_cons.mp call.separation.1).1 _ List.mem_cons_self
  have pos : 0 < (Stack.region s signingKeyGenerateFromRng.minStackBytes).size := by
    change 0 < (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10584)
    omega
  have bounds := apart_of_disjoint sep (by decide : 0 < 97) pos
  change (s.regValue .rdi).toNat + 97 ≤ (s.regValue .rsp).toNat - 10584 ∨ (s.regValue .rsp).toNat - 10584 + ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10584)) ≤ (s.regValue .rdi).toNat at bounds
  omega

end K256.Proofs.Generate.Wrapper
