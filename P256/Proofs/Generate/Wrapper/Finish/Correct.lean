import P256.Proofs.Generate.Wrapper.Finish.ZeroRun
import P256.Proofs.Generate.Wrapper.Finish.Control
import P256.Proofs.Generate.Wrapper.Finish.Store
import P256.Proofs.Generate.Wrapper.Finish.Restore
import P256.Proofs.Generate.Wrapper.Tail.Capacity

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem work_output_byte [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (memory : MemoryWriteFrame s t #v[workRegion initial]) (i : Nat) (hi : i < 97) :
    t.external[initial.regValue .rcx+8+BitVec.ofNat 64 i]? =
      s.external[initial.regValue .rcx+8+BitVec.ofNat 64 i]? := by
  apply memory
  intro r hr hit
  have eq : r = workRegion initial := by simpa using hr
  subst r
  exact output_stack_disjoint call _
    (output_contains call draw (off := 8) (len := 97) (by decide) ⟨i,hi,rfl⟩)
    (work_in_stack call.stackAvailable.1 hit)

theorem finish [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (state : OutputState initial s input) (rip : s.RIP = 0x106e7c)
    (count : s.regValue .r15 = 65)
    (payload : (MemoryRegion.mk (initial.regValue .rcx+8).toNat 97).HasBytes
      s.external (Spec.Generate.generatedSigningKey #[input])) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (outputRegions initial input) ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Spec.Generate.generatedSigningKey #[input]) := by
  have boundary := initial_boundary call hm hb
  obtain ⟨ret,eq,low,outside⟩ := call.returnAddress
  rw [boundary] at eq
  cases eq
  obtain ⟨a,sa,ipa,fa,ca⟩ := zero_run call state rip outside
  obtain ⟨b,sb,ipb,cb,fb⟩ := add_length sa ipa outside (ca.trans count)
  obtain ⟨c,sc,ipc,fc⟩ := success_branch sb ipb outside
  obtain ⟨e,_,se,ipe,fe⟩ := capacity_length call draw outside sc ipc
  have ce : e.regValue .r15 = 97 :=
    ((fc.trans fe).read (n := 64) (r := 15) (by simp)).trans cb
  obtain ⟨g,sg,ipg,_,length,fg⟩ := finish_store call draw se ipe ce outside
  have unchanged : e.external = a.external :=
    ((fb.trans fc).trans fe).external (by simp [Component.Covers])
  have bytesG (i : Nat) (hi : i < (Spec.Generate.generatedSigningKey #[input]).size) :
      g.external[initial.regValue .rcx+8+BitVec.ofNat 64 i]? =
        some (Spec.Generate.generatedSigningKey #[input]).data[i]! := by
    rw [fg.byte ?_,unchanged,work_output_byte call draw fa i (by rw [generated_key_size draw] at hi; exact hi)]
    · have h := payload.2 ⟨i,hi⟩
      change s.external[BitVec.ofNat 64 ((initial.regValue .rcx+8).toNat+i)]? = _ at h
      simpa only [ByteArray.getElem_eq_getElem_data,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
        getElem!_pos (Spec.Generate.generatedSigningKey #[input]).data i
          (by simpa only [ByteArray.size_data] using hi)] using h
    · intro comp hc cover
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> try exact cover.elim
      obtain ⟨j,hj,eq⟩ := cover
      apply (show OffsetsApart 0 8 8 97 by unfold OffsetsApart; decide +kernel).ne
        (initial.regValue .rcx) hj (by rw [generated_key_size draw] at hi; exact hi) (by decide)
      change initial.regValue .rcx + (0 : BitVec 64) + BitVec.ofNat 64 j =
        initial.regValue .rcx + 8 + BitVec.ofNat 64 i
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm
  obtain ⟨final,run,machine,bindingsSupported,saved,df,memory,_⟩ :=
    restore call.stackAvailable.1 sg ipg outside low
  obtain ⟨n,execution⟩ := sg.execution
  obtain ⟨fuel,unique⟩ := (execution.returns run).unique_of_boundary boundary
  refine ⟨fuel,final,unique,machine,bindingsSupported,saved,df,?_,?_⟩
  · intro x hx
    rw [memory]
    exact sg.frame x hx
  · apply readOutput_of_bytes (by rw [generated_key_size draw]; decide)
    · change Bytes final.external (initial.regValue .rcx) 8
        (storedByte (BitVec.ofNat 64 (Spec.Generate.generatedSigningKey #[input]).size))
      rw [memory,generated_key_size draw]
      have allocated := (output_writable call draw sg.allocated).add 0 (len := 8) (by decide)
      have bytes := Bytes.of_memLoad (n := 64) (by
        intro i hi
        simpa only [BitVec.add_zero] using allocated.mem i hi)
      rw [length] at bytes
      exact bytes
    · intro i hi
      change final.external[initial.regValue .rcx+8+BitVec.ofNat 64 i]? = _
      rw [memory]
      exact bytesG i hi

end P256.Proofs.Generate.Wrapper.Finish
