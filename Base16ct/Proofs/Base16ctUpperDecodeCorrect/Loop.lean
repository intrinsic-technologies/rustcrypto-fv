import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopIteration

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
variable {lengthWritten : Prop}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode_machine_loop [Bindings]
    {initial s : RamState} {input processed rest : List UInt8}
    {regions : Vector MemoryRegion n} {components : List Component} {capacity : Nat}
    {boundary : ReturnBoundary}
    (hstep : DecodeLoopStep (lengthWritten := lengthWritten) routine alphabets exitOffset steps)
    (hstack : 16 ≤ routine.minStackBytes)
    (hvalid : ValidCall routine initial input capacity lengthWritten)
    (hentry : EntryReady programImage s)
    (h : DecodeMachineLoopInvariant alphabets routine.entryAddress exitOffset initial input processed rest regions components s)
    (heven : input.length % 2 = 0) (hcapacity : input.length / 2 ≤ capacity)
    (hret : ¬ InProgram boundary.rip)
    (hregion : outputRegion initial (input.length / 2) ∈ regions)
    (hallowed : ∀ c ∈ decodeLoopEffects initial (input.length / 2), c ∈ components) :
    ∃ t, Advances boundary (steps * (rest.length / 2)) s t ∧ EntryReady programImage t ∧
      DecodeMachineLoopInvariant alphabets routine.entryAddress exitOffset initial input input [] regions components t := by
  induction rest using RFC4648.decode.induct generalizing processed s with
  | case1 =>
    have heq : input = processed := by simpa only [List.append_nil] using h.split
    subst processed
    exact ⟨s, by simp, hentry, h⟩
  | case2 high low rest ih =>
    obtain ⟨u, hau, heu, hu⟩ := decode_machine_loop_preserves
      hstep hstack hvalid hentry h heven hcapacity hret hregion hallowed
    obtain ⟨t, hat, het, ht⟩ := ih heu hu
    refine ⟨t, ?_, het, ht⟩
    have hn : steps * ((high :: low :: rest).length / 2) = steps + steps * (rest.length / 2) := by
      simp only [List.length_cons]
      rw [show (rest.length + 1 + 1) / 2 = 1 + rest.length / 2 by omega, Nat.mul_add, Nat.mul_one]
    rw [hn]
    exact hau.trans hat
  | case3 byte =>
    have hlen := congrArg List.length h.split
    have hp := h.processedEven
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
