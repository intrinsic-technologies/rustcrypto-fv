import Sha3.Proofs.Permutation.Layout
import Sha3.Proofs.Permutation.RoundAlgebra
import X86Proofs.Program.Compose

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86Proofs RoundAlgebra

def operand (sp : BitVec 64) : Location → Operand 64
  | .reg i => .reg (BitVec.ofNat 5 i.val)
  | .stack offset => .mem (sp + BitVec.ofNat 64 offset)

def ValidLocation : Location → Prop
  | .reg _ => True
  | .stack offset => offset % 8 = 0 ∧ offset < 272

instance (loc : Location) : Decidable (ValidLocation loc) := by
  cases loc <;> unfold ValidLocation <;> infer_instance

def Models (sp : BitVec 64) (a : RoundAlgebra.State) (s : RamState) : Prop :=
  ∀ loc, ValidLocation loc → (operand sp loc).read s = read a loc

def model (sp : BitVec 64) (s : RamState) : RoundAlgebra.State where
  regs := fun i ↦ (operand sp (.reg i)).read s
  stack := fun offset ↦ (operand sp (.stack offset)).read s

theorem models_model (sp : BitVec 64) (s : RamState) : Models sp (model sp s) s := by
  intro loc _
  cases loc <;> rfl

theorem regNumber_inj (i j : Fin 16) :
    BitVec.ofNat 5 i.val = BitVec.ofNat 5 j.val ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    have := i.isLt
    have := j.isLt
    omega
  · rintro rfl
    rfl

theorem stackBytes_ne (sp : BitVec 64) {a b i j : Nat}
    (ha : a % 8 = 0 ∧ a < 272) (hb : b % 8 = 0 ∧ b < 272)
    (hne : a ≠ b) (hi : i < 8) (hj : j < 8) :
    sp + BitVec.ofNat 64 a + BitVec.ofNat 64 i ≠
      sp + BitVec.ofNat 64 b + BitVec.ofNat 64 j := by
  intro h
  rw [BitVec.add_assoc, BitVec.add_assoc] at h
  have hv := congrArg BitVec.toNat ((BitVec.add_right_inj sp).mp h)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hv
  omega

def writeEffect (sp next : BitVec 64) (dst : Location) (value : BitVec 64)
    (flags : Option StatusFlagsOutcome) : Effect where
  rip := next
  writes := [⟨operand sp dst, value⟩]
  flags := flags

theorem read_writeEffect_of_ne {sp next : BitVec 64} {dst loc : Location}
    {value : BitVec 64} {flags : Option StatusFlagsOutcome} {s t : RamState}
    (h : (writeEffect sp next dst value flags).Holds s t)
    (hdst : ValidLocation dst) (hloc : ValidLocation loc) (hne : loc ≠ dst) :
    (operand sp loc).read t = (operand sp loc).read s := by
  cases dst with
  | reg rd =>
    cases loc with
    | reg r =>
      apply h.agrees.read
      cases flags <;>
        simpa [writeEffect, Effect.components, operand, Operand.component, regNumber_inj] using hne
    | stack off =>
      change memLoad t.external _ 64 = memLoad s.external _ 64
      rw [h.agrees.external]
      intro c hc x
      cases c <;> cases flags <;>
        simp_all [writeEffect, Effect.components, operand, Component.Covers]
  | stack off =>
    cases loc with
    | reg r =>
      apply h.agrees.read
      cases flags <;> simp [writeEffect, Effect.components, operand]
    | stack offset =>
      change memLoad t.external _ 64 = memLoad s.external _ 64
      apply memLoad_congr
      intro j hj
      unfold memByte
      change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
      rw [h.agrees.byte]
      intro c hc hcov
      have hc' : c = .mem (sp + BitVec.ofNat 64 off) 8 ∨ c = .flags ∨ c = .rip := by
        cases flags with
        | none =>
          have hc' : c = .mem (sp + BitVec.ofNat 64 off) 8 ∨ c = .rip := by
            simpa [writeEffect, Effect.components, operand] using hc
          exact hc'.elim Or.inl (fun h ↦ Or.inr (Or.inr h))
        | some f =>
          simpa [writeEffect, Effect.components, operand] using hc
      rcases hc' with rfl | rfl | rfl
      · obtain ⟨i, hi, heq⟩ := hcov
        exact stackBytes_ne sp hdst hloc (by simpa using Ne.symm hne) hi hj heq.symm
      · exact hcov
      · exact hcov

theorem models_writeEffect {sp next : BitVec 64} {dst : Location}
    {value : BitVec 64} {flags : Option StatusFlagsOutcome} {s t : RamState}
    {a : RoundAlgebra.State} (hm : Models sp a s)
    (hdst : ValidLocation dst)
    (h : (writeEffect sp next dst value flags).Holds s t) :
    Models sp (write a dst value) t := by
  intro loc hloc
  by_cases heq : loc = dst
  · subst loc
    have hw : (operand sp dst).read t = value := h.writes
    rw [hw]
    cases dst <;> simp [RoundAlgebra.read, write]
  · rw [read_writeEffect_of_ne h hdst hloc heq, hm loc hloc]
    cases dst <;> cases loc <;> simp_all [RoundAlgebra.read, write]

theorem models_lanes {sp : BitVec 64} {a : RoundAlgebra.State} {s : RamState}
    (h : Models sp a s) : readLanes sp s = lanes a := by
  funext i
  have hl : ValidLocation laneLocations[i.val] := by
    exact (by decide : ∀ j : Fin 25, ValidLocation laneLocations[j.val]) i
  have hv := h laneLocations[i.val] hl
  have ho : operand sp laneLocations[i.val] = (laneOperands sp)[i] := by
    have he : laneLocations.map (operand sp) = laneOperands sp := by
      simp only [Vector.map, laneLocations, Fin.isValue, List.map_toArray, List.map_cons,
        operand, Fin.val_zero, List.map_nil, laneOperands, BitVec.ofNat_eq_ofNat,
        Vector.eq_mk, Array.mk.injEq, List.cons.injEq, Operand.reg.injEq, and_true, true_and, BitVec.add_zero]
      decide +kernel
    simpa only [Vector.getElem_map, Fin.getElem_fin] using
      congrArg (fun v : Vector (Operand 64) 25 ↦ v[i.val]) he
  change (laneOperands sp)[i].read s = read a laneLocations[i.val]
  rw [← ho]
  exact hv

end Sha3.Proofs.Permutation.RoundMachine
