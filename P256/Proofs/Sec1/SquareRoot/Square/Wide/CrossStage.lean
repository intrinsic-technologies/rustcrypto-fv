import P256.Proofs.Sec1.SquareRoot.Square.Wide.ProductsCombined
import P256.Proofs.Sec1.SquareRoot.Square.Wide.CrossSums

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def crossStageEffect (s : RamState) : Effect :=
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
  { rip := 0x11cc33
    writes := [
      ⟨(.reg 0 : Operand 64), v111bc3⟩,
      ⟨(.reg 1 : Operand 64), v111bb6.1⟩,
      ⟨(.reg 2 : Operand 64), hv111bc3⟩,
      ⟨(.reg 3 : Operand 64), v111bcf.1⟩,
      ⟨(.reg 5 : Operand 64), v111bbc.1⟩,
      ⟨(.reg 6 : Operand 64), hv111b86⟩,
      ⟨(.reg 8 : Operand 64), v111bb9.1⟩,
      ⟨(.reg 9 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)⟩,
      ⟨(.reg 10 : Operand 64), hv111b66⟩,
      ⟨(.reg 11 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)⟩,
      ⟨(.reg 12 : Operand 64), v111bcc.1⟩,
      ⟨(.reg 13 : Operand 64), v111ba7.1⟩,
      ⟨(.reg 14 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)⟩,
      ⟨(.reg 15 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64), hv111b74⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64), v111b66⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1000000 in
theorem crossStage_merge {s t u : RamState} (_hp : BodyPre s)
    (h1 : (productsEffect s).Holds s t) (h2 : (crossSumsEffect t).Holds t u) :
    (crossStageEffect s).Holds s u := by
  have rsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    h1.agrees.read (by simp [productsEffect, Effect.components])
  have rdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    h1.agrees.read (by simp [productsEffect, Effect.components])
  rcases h1.writes with ⟨or0, or1, or2, or3, or5, or6, or8, or9, or10, or11, or12, or13, or14, or15, om4_8, om4_32⟩
  have ws := h2.writes
  simp only [crossSumsEffect, Write.AllHold] at ws
  simp only [*] at ws
  rcases ws with ⟨nr0, nr1, nr2, nr3, nr5, nr8, nr12, nr13⟩
  have kr6 : (Operand.reg 6 : Operand 64).read u = (Operand.reg 6 : Operand 64).read t :=
    h2.agrees.read (by simp [crossSumsEffect, Effect.components])
  have kr9 : (Operand.reg 9 : Operand 64).read u = (Operand.reg 9 : Operand 64).read t :=
    h2.agrees.read (by simp [crossSumsEffect, Effect.components])
  have kr10 : (Operand.reg 10 : Operand 64).read u = (Operand.reg 10 : Operand 64).read t :=
    h2.agrees.read (by simp [crossSumsEffect, Effect.components])
  have kr11 : (Operand.reg 11 : Operand 64).read u = (Operand.reg 11 : Operand 64).read t :=
    h2.agrees.read (by simp [crossSumsEffect, Effect.components])
  have kr14 : (Operand.reg 14 : Operand 64).read u = (Operand.reg 14 : Operand 64).read t :=
    h2.agrees.read (by simp [crossSumsEffect, Effect.components])
  have kr15 : (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read t :=
    h2.agrees.read (by simp [crossSumsEffect, Effect.components])
  have km4_8 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64).read t := by
    have he := h2.agrees.external (by simp [crossSumsEffect, Effect.components, Component.Covers])
    change memLoad u.external _ 64 = memLoad t.external _ 64
    rw [he]
  have km4_32 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64).read t := by
    have he := h2.agrees.external (by simp [crossSumsEffect, Effect.components, Component.Covers])
    change memLoad u.external _ 64 = memLoad t.external _ 64
    rw [he]
  refine ⟨h2.rip, ?_, ?_, ?_⟩
  · simp only [crossStageEffect, Write.AllHold]
    refine ⟨nr0, nr1, nr2, nr3, nr5, (kr6).trans or6, nr8, (kr9).trans or9, (kr10).trans or10, (kr11).trans or11, nr12, nr13, (kr14).trans or14, (kr15).trans or15, (km4_8).trans om4_8, (km4_32).trans om4_32⟩
  · simp [crossStageEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply (h1.agrees.trans h2.agrees).mono
    simp [productsEffect, crossSumsEffect, crossStageEffect, Effect.components]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
theorem crossStage_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BodyPre (codeRange 0x11cbb8 bodyBytes)
      (Effect.post crossStageEffect) := by
  intro s ready loaded hp
  obtain ⟨n1, t, run1, ready1, loaded1, h1⟩ := products_correct boundary hout s ready loaded hp
  have rsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    h1.agrees.read (by simp [productsEffect, Effect.components])
  have rdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    h1.agrees.read (by simp [productsEffect, Effect.components])
  have pb : CrossSumsPre t := by
    refine ⟨h1.rip, ?_⟩
    · intro i hi
      rw [rsp]
      exact (hp.stackRead i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl <;> simp)).of_holds h1
  obtain ⟨n2, u, run2, ready2, _, h2⟩ := crossSums_correct boundary hout t ready1
    (loaded1.mono (codeRange_slice_subset 0x11cbb8 bodyBytes 79 44)) pb
  have hm := crossStage_merge hp h1 h2
  have av : (crossStageEffect s).Avoids (codeRange 0x11cbb8 bodyBytes) := by
    apply Effect.avoids_codeRange
    x86_norm [crossStageEffect]
    exact ⟨hp.stackCode 8 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 32 (by simp) 0x1cbb8 297 (by decide)⟩
  exact ⟨n1+n2, u, run1.trans run2, ready2, hm.codeIn av loaded, hm⟩

end P256.Proofs.Sec1.SquareRoot.Square.Wide
