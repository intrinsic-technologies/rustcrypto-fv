import P256.Proofs.Sec1.SquareRoot.Square.Wide.CrossStage
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Diagonals

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec)
open P256.Proofs.Common.Instructions.ShiftLeft (shldOneResult)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def diagonalStageEffect (s : RamState) : Effect :=
  let v111b66 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111b66 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111b74 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let hv111b74 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let v111b86 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111b86 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111b92 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let hv111b92 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let v111b9e := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111b9e := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111ba7 := addSpec v111b74 hv111b66
  let v111baa := adcSpec v111b86 hv111b74 (BitVec.ofBool (v111ba7.2.CF))
  let v111baf := adcSpec v111b9e hv111b86 (BitVec.ofBool (v111baa.2.CF))
  let v111bb2 := adcSpec hv111b9e (0 : BitVec 64) (BitVec.ofBool (v111baf.2.CF))
  let v111bb6 := addSpec v111baa.1 v111b92
  let v111bb9 := adcSpec v111baf.1 hv111b92 (BitVec.ofBool (v111bb6.2.CF))
  let v111bbc := adcSpec v111bb2.1 (0 : BitVec 64) (BitVec.ofBool (v111bb9.2.CF))
  let v111bc3 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  let hv111bc3 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  let v111bcc := addSpec v111bc3 v111bbc.1
  let v111bcf := adcSpec hv111bc3 (0 : BitVec 64) (BitVec.ofBool (v111bcc.2.CF))
  let v111bd6 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)
  let hv111bd6 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)
  let v111be4 := shldOneResult v111bcc.1 v111bb9.1
  let v111bec := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  let hv111bec := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  let v111bfa := shldOneResult v111bb6.1 v111ba7.1
  let v111c02 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111c02 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111c0e := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let hv111c0e := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let v111c19 := v111bcf.1 >>> 63
  let v111c22 := shldOneResult v111ba7.1 v111b66
  { rip := 0x11cc87
    writes := [
      ⟨(.reg 0 : Operand 64), v111b66⟩,
      ⟨(.reg 1 : Operand 64), v111bb6.1⟩,
      ⟨(.reg 2 : Operand 64), hv111c0e⟩,
      ⟨(.reg 3 : Operand 64), v111bcf.1⟩,
      ⟨(.reg 5 : Operand 64), v111c02⟩,
      ⟨(.reg 6 : Operand 64), v111be4⟩,
      ⟨(.reg 8 : Operand 64), v111bb9.1⟩,
      ⟨(.reg 9 : Operand 64), v111c19⟩,
      ⟨(.reg 10 : Operand 64), v111bfa⟩,
      ⟨(.reg 11 : Operand 64), hv111c02⟩,
      ⟨(.reg 12 : Operand 64), v111bcc.1⟩,
      ⟨(.reg 13 : Operand 64), v111c22⟩,
      ⟨(.reg 14 : Operand 64), hv111bec⟩,
      ⟨(.reg 15 : Operand 64), hv111bd6⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64), v111bd6⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 16) : Operand 64), v111c0e⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 24) : Operand 64), v111bec⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64), v111b66⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1000000 in
theorem diagonalStage_merge {s t u : RamState} (_hp : BodyPre s)
    (h1 : (crossStageEffect s).Holds s t) (h2 : (diagonalsEffect t).Holds t u) :
    (diagonalStageEffect s).Holds s u := by
  have rsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    h1.agrees.read (by simp [crossStageEffect, Effect.components])
  have rdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    h1.agrees.read (by simp [crossStageEffect, Effect.components])
  rcases h1.writes with ⟨or0, or1, or2, or3, or5, or6, or8, or9, or10, or11, or12, or13, or14, or15, om4_8, om4_32⟩
  simp only [Write.AllHold] at or0 or1 or2 or3 or5 or6 or8 or9 or10 or11 or12 or13 or14 or15 om4_8 om4_32
  have ws := h2.writes
  simp only [diagonalsEffect, Write.AllHold] at ws
  simp only [rsp, or1, or3, or8, or9, or11, or12, or13, or14, or15, om4_32] at ws
  rcases ws with ⟨nr0, nr2, nr5, nr6, nr9, nr10, nr11, nr13, nr14, nr15, nm4_8, nm4_16, nm4_24⟩
  have kr1 : (Operand.reg 1 : Operand 64).read u = (Operand.reg 1 : Operand 64).read t :=
    h2.agrees.read (by simp [diagonalsEffect, Effect.components])
  have kr3 : (Operand.reg 3 : Operand 64).read u = (Operand.reg 3 : Operand 64).read t :=
    h2.agrees.read (by simp [diagonalsEffect, Effect.components])
  have kr8 : (Operand.reg 8 : Operand 64).read u = (Operand.reg 8 : Operand 64).read t :=
    h2.agrees.read (by simp [diagonalsEffect, Effect.components])
  have kr12 : (Operand.reg 12 : Operand 64).read u = (Operand.reg 12 : Operand 64).read t :=
    h2.agrees.read (by simp [diagonalsEffect, Effect.components])
  have km4_32 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [diagonalsEffect, Effect.components, List.map_cons, List.map_nil, Write.component_reg, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, false_or, Nat.reduceDiv, rsp] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact (show OffsetsApart 8 8 32 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 4 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 16 8 32 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 4 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 24 8 32 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 4 : Operand 64).read s) hi hj (by decide) he
  refine ⟨h2.rip, ?_, ?_, ?_⟩
  · simp only [diagonalStageEffect, Write.AllHold]
    refine ⟨nr0, (kr1).trans or1, nr2, (kr3).trans or3, nr5, nr6, (kr8).trans or8, nr9, nr10, nr11, (kr12).trans or12, nr13, nr14, nr15, nm4_8, nm4_16, nm4_24, (km4_32).trans om4_32⟩
  · simp [diagonalStageEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply (h1.agrees.trans h2.agrees).mono
    simp only [crossStageEffect, diagonalsEffect, diagonalStageEffect, Effect.components, rsp]
    simp

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
theorem diagonalStage_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BodyPre (codeRange 0x11cbb8 bodyBytes)
      (Effect.post diagonalStageEffect) := by
  intro s ready loaded hp
  obtain ⟨n1, t, run1, ready1, loaded1, h1⟩ := crossStage_correct boundary hout s ready loaded hp
  have rsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    h1.agrees.read (by simp [crossStageEffect, Effect.components])
  have rdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    h1.agrees.read (by simp [crossStageEffect, Effect.components])
  have pb : DiagonalsPre t := by
    refine ⟨h1.rip, ?_, ?_, ?_⟩
    · intro i hi
      rw [rsp]
      exact (hp.stackRead i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl <;> simp)).of_holds h1
    · intro i hi
      rw [rsp]
      exact (hp.stackWrite i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl <;> simp)).of_holds h1
    · intro i hi o n hn
      rw [rsp]
      exact hp.stackCode i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl <;> simp) o n hn
  obtain ⟨n2, u, run2, ready2, _, h2⟩ := diagonals_correct boundary hout t ready1
    (loaded1.mono (codeRange_slice_subset 0x11cbb8 bodyBytes 123 84)) pb
  have hm := diagonalStage_merge hp h1 h2
  have av : (diagonalStageEffect s).Avoids (codeRange 0x11cbb8 bodyBytes) := by
    apply Effect.avoids_codeRange
    x86_norm [diagonalStageEffect]
    exact ⟨hp.stackCode 8 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 16 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 24 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 32 (by simp) 0x1cbb8 297 (by decide)⟩
  exact ⟨n1+n2, u, run1.trans run2, ready2, hm.codeIn av loaded, hm⟩

end P256.Proofs.Sec1.SquareRoot.Square.Wide
