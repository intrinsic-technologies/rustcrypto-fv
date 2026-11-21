import P256.Proofs.HMAC.Pad.Control

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem xor_four [Bindings] {loop : Loop} {s : RamState} {boundary : ReturnBoundary}
    {n : Nat} {f : Nat → UInt8} (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (state : Position loop s n 0 f) (hn : n < 16) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      Position loop t n 4 f ∧ AgreesExcept (footprint loop s) s t := by
  obtain ⟨a, runA, readyA, loadedA, stateA, agreesA⟩ := xor_step ready loaded outside state hn (by decide)
  obtain ⟨b, runB, readyB, loadedB, stateB, agreesB⟩ := xor_step readyA loadedA outside stateA hn (by decide)
  obtain ⟨c, runC, readyC, loadedC, stateC, agreesC⟩ := xor_step readyB loadedB outside stateB hn (by decide)
  obtain ⟨t, runD, readyD, loadedD, stateD, agreesD⟩ := xor_step readyC loadedC outside stateC hn (by decide)
  exact ⟨t, ((runA.trans runB).trans runC).trans runD, readyD, loadedD, stateD,
    footprint_trans (footprint_trans (footprint_trans agreesA agreesB) agreesC) agreesD⟩

theorem loop_from [Bindings] {loop : Loop} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (remaining : Nat) :
    ∀ (s : RamState) (n : Nat) (f : Nat → UInt8),
      n + remaining = 16 → n < 16 → ReadyToStep s → ProgramLoaded s →
      Position loop s n 0 f →
      ∃ t, Advances boundary (7 * remaining) s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
        t.RIP = BitVec.ofNat 64 (loop.entry + loop.length) ∧ t.regValue .rax = 67 ∧
        AgreesExcept (footprint loop s) s t ∧
        Bytes t.external (buffer loop s) 64 (fun i => f i ^^^ loop.mask) := by
  induction remaining with
  | zero =>
    intro s n f bound hn
    omega
  | succ remaining ih =>
    intro s n f bound hn ready loaded state
    obtain ⟨u, runU, readyU, loadedU, stateU, agreesU⟩ := xor_four ready loaded outside state hn
    obtain ⟨v, runV, readyV, loadedV, ripV, counterV, control⟩ :=
      advance readyU loadedU outside stateU.rip stateU.counter hn
    have agreesV : AgreesExcept (footprint loop u) u v := control.mono (by simp [footprint])
    have total := footprint_trans agreesU agreesV
    have memory := stateU.toMemory.after agreesV
    have bytes : Bytes v.external (buffer loop v) 64 (xorPrefix f loop.mask (4 * (n + 1))) := by
      rw [buffer_of_agrees agreesV, control.external (by simp [Component.Covers])]
      have eq : 4 * n + 4 = 4 * (n + 1) := by omega
      simpa only [eq] using stateU.bytes
    by_cases done : remaining = 0
    · subst remaining
      have eq : n + 1 = 16 := by omega
      have out : Bytes v.external (buffer loop s) 64 (fun i => f i ^^^ loop.mask) := by
        rw [eq] at bytes
        have beq := buffer_of_agrees total
        rw [beq] at bytes
        apply bytes.congr
        intro i hi
        exact ite_eq_left hi
      refine ⟨v, ?_, readyV, loadedV, ?_, ?_, total, out⟩
      · exact runU.trans runV
      · simpa only [eq, Nat.lt_irrefl, reduceIte] using ripV
      · simpa only [eq, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using counterV
    · have more : n + 1 < 16 := by omega
      have stateV : Position loop v (n + 1) 0 f := by
        refine ⟨memory, ?_, counterV, ?_⟩
        · rw [ite_eq_left more] at ripV
          have pc : loop.address 0 = BitVec.ofNat 64 loop.entry := by cases loop <;> rfl
          exact ripV.trans pc.symm
        · simpa only [Nat.add_zero] using bytes
      obtain ⟨t, runT, readyT, loadedT, ripT, counterT, agreesT, bytesT⟩ :=
        ih v (n + 1) f (by omega) more readyV loadedV stateV
      refine ⟨t, ?_, readyT, loadedT, ripT, counterT, footprint_trans total agreesT, ?_⟩
      · have run := (runU.trans runV).trans runT
        have eq : 4 + 3 + 7 * remaining = 7 * (remaining + 1) := by omega
        simpa only [eq] using run
      · rwa [buffer_of_agrees total] at bytesT

theorem loop_correct [Bindings] {loop : Loop} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : Pre loop s) :
    ∃ t, Advances boundary 112 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ Post loop s t := by
  let f := fun i => memByte s.external (buffer loop s + BitVec.ofNat 64 i)
  have state : Position loop s 0 0 f := by
    refine ⟨pre.toMemory, ?_, pre.counter, ?_⟩
    · have pc : loop.address 0 = BitVec.ofNat 64 loop.entry := by cases loop <;> rfl
      exact pre.rip.trans pc.symm
    · intro i hi
      simpa only [xorPrefix, Nat.mul_zero, Nat.zero_add, Nat.not_lt_zero, reduceIte]
        using (Bytes.of_isSome pre.writable.mem) i hi
  obtain ⟨t, run, readyT, loadedT, ripT, counterT, agreesT, bytesT⟩ :=
    loop_from outside 16 s 0 f (by decide) (by decide) ready loaded state
  exact ⟨t, run, readyT, loadedT, ripT, counterT, agreesT, bytesT⟩

end P256.Proofs.HMAC.Pad
