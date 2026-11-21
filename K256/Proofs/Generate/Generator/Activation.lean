import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.Generator.Sample.State

namespace K256.Proofs.Generate.Generator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def activation (s : RamState) : Activation :=
  let sp := s.regValue .rsp
  { Activation.ofEntry s 10584 0x102539 with
    original := entryMemory s
    rsp := sp - 288
    low := sp - 10584
    rbx := s.regValue .rdi
    rsi := sp - 208
    rdi := sp - 192
    r14 := sp - 192 }

theorem loaded_of_stackFrame {s : RamState} {random : ByteArray} {mem : Ram}
    (call : ValidCall signingKeyGenerateFromRng s [random])
    (frame : RamWriteFrame s.external mem [Stack.region s signingKeyGenerateFromRng.minStackBytes]) :
    ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2 := by
  let stk := Stack.region s signingKeyGenerateFromRng.minStackBytes
  have avoid := (call.separation.2 stk (by simp [stk, writtenRegions])).1
  have writes : MemoryWriteFrame s {s with external := mem} #v[stk] :=
    RamWriteFrame.memoryWriteFrame frame (fun _ none _ hr => none _ (by simpa only [List.mem_singleton,
      Vector.mem_singleton] using hr))
  have loaded := Common.programLoaded_of_memoryWriteFrame writes call.programLoaded (by
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact fun a hs h => avoid a hs (Or.inl h))
  exact fun x hx => loaded x.1 x.2 (Common.programSections_fetchByte_of_mem hx)

theorem sampleEntry {s : RamState} {random : ByteArray} (call : ValidCall signingKeyGenerateFromRng s [random]) :
    Sample.Entry s (activation s) (entryArgs s) := by
  let sp := s.regValue .rsp
  let stk := Stack.region s signingKeyGenerateFromRng.minStackBytes
  obtain ⟨base, len, ret, _⟩ := entryMemory_load s
  have frame := entryMemory_frame call
  refine ⟨?_, rfl, rfl, rfl, base, ?_, frame⟩
  · have hr : rodataSection ∈ Extracted.programSections := by simp [rodataSection, Extracted.programSections]
    have slots := Fn105f30.callSlots_loaded hr (loaded_of_stackFrame call frame)
    obtain ⟨read1, val1⟩ := slots (0x203de0, 0x129770) (by decide)
    obtain ⟨read2, val2⟩ := slots (0x203e20, 0x100a20) (by decide)
    have depth : 10584 ≤ sp.toNat := call.stackAvailable.2.2.1
    have hs : stk ∈ writtenRegions signingKeyGenerateFromRng s := by simp [stk, writtenRegions]
    have pos : 0 < stk.size := by change 0 < sp.toNat + 8 - (sp.toNat - 10584); omega
    have apart := apart_of_avoids (call.separation.2 stk hs).1
      (lo := 0x203de0) (hi := 0x203e28) (by
        intro a ha hb
        obtain ⟨b, hb⟩ := Fn105f30.callSlots_span hr a ha hb
        exact Or.inl ⟨b, Common.programSections_fetchByte_of_mem hb⟩) pos (by decide) (by decide)
    change sp.toNat - 10584 + (sp.toNat + 8 - (sp.toNat - 10584)) ≤ _ ∨ _ ≤ sp.toNat - 10584 at apart
    have rsp := stackOffset (off := 288) call (by decide)
    have low := stackOffset (off := 10584) call (by decide)
    change (sp - 288).toNat = sp.toNat - 288 at rsp
    change (sp - 10584).toNat = sp.toNat - 10584 at low
    have read := ((stackWritable (off := 288) (len := 8) call (by decide) (by decide) (by decide)).of_frame frame).readable
    have writable := (stackWritable (off := 10456) (len := 10168) call (by decide) (by decide) (by decide)).of_frame frame
    have df := Reg.read_df_iff.mpr call.directionFlagUnset
    have align : sp.toNat % 16 = 8 := call.stackAvailable.2.2.2
    change Atom.All _ _ _ (Fn105f30.frameAtG0 .l105f30 _)
    simp only [Fn105f30.frameAtG0, Atom.All, Atom.Holds, activation, Activation.ofEntry]
    simp only [entryArgs, Fin.getElem_fin, Vector.getElem_set, Lifted.locationOf, Vector.getElem_ofFn]
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      read, ret, by decide, ?_, ?_, ?_, read1, val1, read2, val2, ?_, trivial⟩
    · change (Reg.ofIndex 22).read s = _
      exact df
    · rw [BitVec.sub_sub]
      exact writable
    · change (sp - 10584).toNat + 10168 ≤ (sp - 288).toNat
      omega
    · change (sp - 288).toNat % 16 = 8
      omega
    · change 0x2065e0 ≤ (sp - 288).toNat ∨ (sp - 288).toNat ≤ 0x203de0
      omega
  · change memLoad _ (sp - 208 + 8) 64 = _
    rw [show sp - 208 + 8 = sp - 200 by bv_omega]
    exact len

end K256.Proofs.Generate.Generator
