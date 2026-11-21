import P256.Proofs.Sec1.SquareRoot.Square.Wide.StoreLowStage
import P256.Proofs.Sec1.SquareRoot.Square.Wide.StoresHigh

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec)
open P256.Proofs.Common.Instructions.ShiftLeft (shldOneResult)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def storeHighStageEffect (s : RamState) : Effect :=
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
  let v111c27 := addSpec v111b66 v111b66
  let v111c2a := addSpec v111c27.1 hv111c0e
  let v111c2d := adcSpec v111c22 v111c02 (BitVec.ofBool (v111c2a.2.CF))
  let v111c30 := adcSpec hv111c02 (0 : BitVec 64) (BitVec.ofBool (v111c2d.2.CF))
  let v111c34 := shldOneResult v111bb9.1 v111bb6.1
  let v111c39 := addSpec v111c30.1 v111bfa
  let v111c3c := adcSpec v111c34 v111bec (BitVec.ofBool (v111c39.2.CF))
  let v111c41 := adcSpec hv111bec (0 : BitVec 64) (BitVec.ofBool (v111c3c.2.CF))
  let v111c45 := shldOneResult v111bcf.1 v111bcc.1
  let v111c4a := addSpec v111c45 v111bd6
  let v111c4f := adcSpec hv111bd6 (0 : BitVec 64) (BitVec.ofBool (v111c4a.2.CF))
  let v111c53 := addSpec v111c41.1 v111be4
  let v111c56 := adcSpec v111c4a.1 (0 : BitVec 64) (BitVec.ofBool (v111c53.2.CF))
  let v111c5a := adcSpec v111c4f.1 v111c19 (BitVec.ofBool (v111c56.2.CF))
  { rip := 0x11cce1
    writes := [
      ⟨(.reg 0 : Operand 64), v111c2a.1⟩,
      ⟨(.reg 1 : Operand 64), v111c0e⟩,
      ⟨(.reg 2 : Operand 64), hv111c0e⟩,
      ⟨(.reg 3 : Operand 64), v111c56.1⟩,
      ⟨(.reg 5 : Operand 64), v111c02⟩,
      ⟨(.reg 6 : Operand 64), v111be4⟩,
      ⟨(.reg 8 : Operand 64), v111c3c.1⟩,
      ⟨(.reg 9 : Operand 64), v111c19⟩,
      ⟨(.reg 10 : Operand 64), v111bfa⟩,
      ⟨(.reg 11 : Operand 64), v111c39.1⟩,
      ⟨(.reg 12 : Operand 64), v111bcc.1⟩,
      ⟨(.reg 13 : Operand 64), v111c2d.1⟩,
      ⟨(.reg 14 : Operand 64), v111c53.1⟩,
      ⟨(.reg 15 : Operand 64), v111c5a.1⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64), v111bd6⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 16) : Operand 64), v111c0e⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 24) : Operand 64), v111bec⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64), v111b66⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 0) : Operand 64), v111c0e⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 8) : Operand 64), v111c2a.1⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 16) : Operand 64), v111c2d.1⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 24) : Operand 64), v111c39.1⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 32) : Operand 64), v111c3c.1⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 40) : Operand 64), v111c53.1⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 48) : Operand 64), v111c56.1⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 56) : Operand 64), v111c5a.1⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1000000 in
theorem storeHighStage_merge {s t u : RamState} (hp : BodyPre s)
    (h1 : (storeLowStageEffect s).Holds s t) (h2 : (storesHighEffect t).Holds t u) :
    (storeHighStageEffect s).Holds s u := by
  have rsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    h1.agrees.read (by simp [storeLowStageEffect, Effect.components])
  have rdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    h1.agrees.read (by simp [storeLowStageEffect, Effect.components])
  rcases h1.writes with ⟨or0, or1, or2, or3, or5, or6, or8, or9, or10, or11, or12, or13, or14, or15, om4_8, om4_16, om4_24, om4_32, om7_0, om7_8, om7_16, om7_24⟩
  simp only [Write.AllHold] at or0 or1 or2 or3 or5 or6 or8 or9 or10 or11 or12 or13 or14 or15 om4_8 om4_16 om4_24 om4_32 om7_0 om7_8 om7_16 om7_24
  have ws := h2.writes
  simp only [storesHighEffect, Write.AllHold] at ws
  simp only [rdi, or3, or8, or14, or15] at ws
  rcases ws with ⟨nm7_32, nm7_40, nm7_48, nm7_56⟩
  have kr0 : (Operand.reg 0 : Operand 64).read u = (Operand.reg 0 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr1 : (Operand.reg 1 : Operand 64).read u = (Operand.reg 1 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr2 : (Operand.reg 2 : Operand 64).read u = (Operand.reg 2 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr3 : (Operand.reg 3 : Operand 64).read u = (Operand.reg 3 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr5 : (Operand.reg 5 : Operand 64).read u = (Operand.reg 5 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr6 : (Operand.reg 6 : Operand 64).read u = (Operand.reg 6 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr8 : (Operand.reg 8 : Operand 64).read u = (Operand.reg 8 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr9 : (Operand.reg 9 : Operand 64).read u = (Operand.reg 9 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr10 : (Operand.reg 10 : Operand 64).read u = (Operand.reg 10 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr11 : (Operand.reg 11 : Operand 64).read u = (Operand.reg 11 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr12 : (Operand.reg 12 : Operand 64).read u = (Operand.reg 12 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr13 : (Operand.reg 13 : Operand 64).read u = (Operand.reg 13 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr14 : (Operand.reg 14 : Operand 64).read u = (Operand.reg 14 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have kr15 : (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read t :=
    h2.agrees.read (by simp [storesHighEffect, Effect.components])
  have km4_8 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact hp.stackOutput 8 (by simp) 32 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 8 (by simp) 40 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 8 (by simp) 48 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 8 (by simp) 56 (by simp) j hj i hi he.symm
  have km4_16 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+16) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+16) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact hp.stackOutput 16 (by simp) 32 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 16 (by simp) 40 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 16 (by simp) 48 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 16 (by simp) 56 (by simp) j hj i hi he.symm
  have km4_24 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+24) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+24) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact hp.stackOutput 24 (by simp) 32 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 24 (by simp) 40 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 24 (by simp) 48 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 24 (by simp) 56 (by simp) j hj i hi he.symm
  have km4_32 : (Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64).read u =
      (Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact hp.stackOutput 32 (by simp) 32 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 32 (by simp) 40 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 32 (by simp) 48 (by simp) j hj i hi he.symm
    · intro i hi j hj he
      exact hp.stackOutput 32 (by simp) 56 (by simp) j hj i hi he.symm
  have km7_0 : (Operand.mem ((Operand.reg 7 : Operand 64).read s+0) : Operand 64).read u =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s+0) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact (show OffsetsApart 32 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 40 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 48 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 56 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
  have km7_8 : (Operand.mem ((Operand.reg 7 : Operand 64).read s+8) : Operand 64).read u =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s+8) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact (show OffsetsApart 32 8 8 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 40 8 8 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 48 8 8 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 56 8 8 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
  have km7_16 : (Operand.mem ((Operand.reg 7 : Operand 64).read s+16) : Operand 64).read u =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s+16) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact (show OffsetsApart 32 8 16 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 40 8 16 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 48 8 16 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 56 8 16 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
  have km7_24 : (Operand.mem ((Operand.reg 7 : Operand 64).read s+24) : Operand 64).read u =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s+24) : Operand 64).read t := by
    apply memory_read_eq h2
    intro b n hm
    simp only [storesHighEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.mem.injEq, Nat.reduceDiv, rdi] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro i hi j hj he
      exact (show OffsetsApart 32 8 24 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 40 8 24 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 48 8 24 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
    · intro i hi j hj he
      exact (show OffsetsApart 56 8 24 8 from by unfold OffsetsApart; decide +kernel).ne
        ((Operand.reg 7 : Operand 64).read s) hi hj (by decide) he
  refine ⟨h2.rip, ?_, ?_, ?_⟩
  · simp only [storeHighStageEffect, Write.AllHold]
    refine ⟨(kr0).trans or0, (kr1).trans or1, (kr2).trans or2, (kr3).trans or3, (kr5).trans or5, (kr6).trans or6, (kr8).trans or8, (kr9).trans or9, (kr10).trans or10, (kr11).trans or11, (kr12).trans or12, (kr13).trans or13, (kr14).trans or14, (kr15).trans or15, (km4_8).trans om4_8, (km4_16).trans om4_16, (km4_24).trans om4_24, (km4_32).trans om4_32, (km7_0).trans om7_0, (km7_8).trans om7_8, (km7_16).trans om7_16, (km7_24).trans om7_24, nm7_32, nm7_40, nm7_48, nm7_56⟩
  · simp [storeHighStageEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply (h1.agrees.trans h2.agrees).mono
    simp only [storeLowStageEffect, storesHighEffect, storeHighStageEffect, Effect.components, rdi]
    simp

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
theorem storeHighStage_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BodyPre (codeRange 0x11cbb8 bodyBytes)
      (Effect.post storeHighStageEffect) := by
  intro s ready loaded hp
  obtain ⟨n1, t, run1, ready1, loaded1, h1⟩ := storeLowStage_correct boundary hout s ready loaded hp
  have rsp : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    h1.agrees.read (by simp [storeLowStageEffect, Effect.components])
  have rdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    h1.agrees.read (by simp [storeLowStageEffect, Effect.components])
  have pb : StoresHighPre t := by
    refine ⟨h1.rip, ?_, ?_⟩
    · intro i hi
      rw [rdi]
      exact (hp.output i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp)).of_holds h1
    · intro i hi o n hn
      rw [rdi]
      exact hp.outputCode i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp) o n hn
  obtain ⟨n2, u, run2, ready2, _, h2⟩ := storesHigh_correct boundary hout t ready1
    (loaded1.mono (codeRange_slice_subset 0x11cbb8 bodyBytes 281 16)) pb
  have hm := storeHighStage_merge hp h1 h2
  have av : (storeHighStageEffect s).Avoids (codeRange 0x11cbb8 bodyBytes) := by
    apply Effect.avoids_codeRange
    x86_norm [storeHighStageEffect]
    exact ⟨hp.stackCode 8 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 16 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 24 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 32 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 0 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 8 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 16 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 24 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 32 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 40 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 48 (by simp) 0x1cbb8 297 (by decide), hp.outputCode 56 (by simp) 0x1cbb8 297 (by decide)⟩
  exact ⟨n1+n2, u, run1.trans run2, ready2, hm.codeIn av loaded, hm⟩

end P256.Proofs.Sec1.SquareRoot.Square.Wide
