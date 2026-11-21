import P256.Proofs.Sec1Serialize.Conversion.Stage
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Conversion

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Sec1Serialize.Conversion (carry_extract setb_zero)

def registers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip]

def inputRegisters : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip]

theorem agrees_trans {a b c : RamState} {cs : List Component} (ha : AgreesExcept cs a b)
    (hb : AgreesExcept cs b c) : AgreesExcept cs a c :=
  (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id

theorem read_mem_of_agrees {a b : RamState} (h : AgreesExcept registers a b)
    (addr : BitVec 64) :
    (Operand.mem addr : Operand 64).read b = (Operand.mem addr : Operand 64).read a := by
  change memLoad b.external _ _ = memLoad a.external _ _
  rw [h.external (by simp [registers, Component.Covers])]

structure Stage [Bindings] (s start t : RamState) (boundary : ReturnBoundary) : Prop where
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  input : MemReadable t (s.regValue .rsi) 32
  execution : ∃ fuel, Advances boundary fuel start t

theorem Stage.readable_offset [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (stage : Stage s start t boundary) (offset : Nat) (h : offset + 8 ≤ 32) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) 8 := by
  have hl := stage.input.low
  have ho : offset < 2^64 := by omega
  refine ⟨?_, ?_⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    have ha : (s.regValue .rsi).toNat + offset < 2^64 := by omega
    rw [Nat.mod_eq_of_lt ha]
    omega
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using stage.input.mem (offset+i) (by omega)

theorem Stage.step_registers [Bindings] {s start t u : RamState}
    {boundary : ReturnBoundary} {effect : Effect}
    (stage : Stage s start t boundary) (outside : ¬ InProgram boundary.rip)
    (step : Machine.step t = some (.next u)) (ready : ReadyToStep u)
    (holds : effect.Holds t u)
    (hcs : ∀ c ∈ effect.components, (∃ r : BitVec 5, c = .reg r ∧ r.toNat < 16) ∨
      c = .flags ∨ c = .rip)
    (next : InProgram effect.rip) : Stage s start u boundary := by
  have memory : u.external = t.external := holds.agrees.external (by
    intro c hc a
    rcases hcs c hc with ⟨r,rfl,_⟩ | rfl | rfl <;> exact id)
  obtain ⟨n,run⟩ := stage.execution
  refine ⟨ready, ?_, readable_of_grow stage.input holds.agrees.grow, n+1, ?_⟩
  · intro a b hb
    rw [memory]
    exact stage.loaded a b hb
  · exact run.trans (Advances.of_step step (.inl (holds.rip ▸ boundary_ne_program outside next)))

end P256.Proofs.Ecdh.Normalize.Conversion
