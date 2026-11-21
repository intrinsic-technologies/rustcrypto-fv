import P256.Proofs.EcdhWrapper.Finish.Copy.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t : RamState} {secret peer : ByteArray} {slices : Array Input}

theorem payload_frame (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (ag : AgreesExcept (components initial) s t) :
    MemoryWriteFrame s t #v[MemoryRegion.mk (initial.regValue .rcx+8).toNat 32] := by
  apply ag.memoryWriteFrame
  intro c hc a cover
  simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  obtain ⟨i,hi,rfl⟩ := cover
  refine ⟨MemoryRegion.mk (initial.regValue .rcx+8).toNat 32,by simp,?_⟩
  have low := (output_writable call (s := initial) (fun _ h ↦ h)).add 8 (len := 32) (by decide) |>.low
  change (initial.regValue .rcx+8).toNat≤_ ∧ _<(initial.regValue .rcx+8).toNat+32
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.reduceToNat] at low ⊢
  constructor <;> omega

theorem final_frame (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (ag : AgreesExcept (components initial) s t) :
    MemoryWriteFrame initial t #v[outputRegion ecdhDiffieHellman initial [secret,peer],
      allocatorStateRegion,randomSourceRegion,callStack ecdhDiffieHellman initial] := by
  apply memoryWriteFrame_trans (regions := #v[outputRegion ecdhDiffieHellman initial [secret,peer],
      allocatorStateRegion,randomSourceRegion,callStack ecdhDiffieHellman initial])
  · intro a ha
    apply frame a
    intro r hr hc
    exact ha r (by simpa [wrapperRegions] using Or.inr hr) hc
  · apply ag.memoryWriteFrame
    intro c hc a cover
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    refine ⟨outputRegion ecdhDiffieHellman initial [secret,peer],by simp,?_⟩
    rw [output_eq]
    exact output_contains call (off := 8) (len := 32) (by decide) cover

omit [Bindings] in
theorem registers_preserved (ag : AgreesExcept (components initial) s t) :
    CalleeSavedRegistersUnchanged s t := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ag.read (n := 64) (r := 3) (by simp [components])
  · exact ag.read (n := 64) (r := 5) (by simp [components])
  · exact ag.read (n := 64) (r := 12) (by simp [components])
  · exact ag.read (n := 64) (r := 13) (by simp [components])
  · exact ag.read (n := 64) (r := 14) (by simp [components])
  · exact ag.read (n := 64) (r := 15) (by simp [components])

end P256.Proofs.EcdhWrapper.Finish.Copy
