import Hkdf.Proofs.Common.Pad.Control
import Hkdf.Proofs.Common.Pad.Interface
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine

theorem xor_step [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    {n i : Nat} {bytes : Vector UInt8 64}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (state : Position v s n i bytes)
    (hn : n < 16) (hi : i < 4) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      Position v t n (i + 1) bytes ∧ AgreesExcept (footprint v s) s t := by
  have index : 4 * n + i < 64 := by omega
  have addr := mode_address v i n hi state.counter
    (address v i + BitVec.ofNat 64 (3 + (v.am (fin4 i hi)).tail.length))
  have length : (layout v).positions[i] +
      (3 + (v.am (fin4 i hi)).tail.length) ≤ (layout v).positions[4] + 10 := by
    have next := xor_length v i hi
    have posnext : (layout v).positions[i + 1] ≤ (layout v).positions[4] := by
      simpa only [Fin.getElem_fin] using (layout_valid v).positions ⟨i + 1, by omega⟩
    omega
  obtain ⟨t, run, readyT, effect⟩ :=
    (xor_m8_imm8_effect_step (address v i) (v.am (fin4 i hi))
      (mode_valid v i hi) (mode_rexX v i hi) (mode_rexB v i hi) (layout v).mask).advances ready
      (xor_code loaded v i hi)
      ⟨state.rip, by rw [addr]; exact state.toMemory.byte_writable _ index,
        by
          rw [addr]
          have code := state.toMemory.byte_code _ _ _ index length
          rw [address_entry_offset v i (by omega)]
          exact code⟩
      (by
        change address v i + BitVec.ofNat 64 (3 + (v.am (fin4 i hi)).tail.length) ≠ _
        rw [xor_next v i hi]
        exact boundary_ne_program outside (address_inProgram_index v (i + 1) (by omega)))
  have single : AgreesExcept
      [.mem (buffer v s + BitVec.ofNat 64 (4 * n + i)) 1, .flags, .rip] s t := by
    have h := effect.agrees
    rw [xorM8Imm8Effect_components, addr] at h
    exact h
  have agrees := byte_agrees index single
  have written :
      (Operand.mem (buffer v s + BitVec.ofNat 64 (4 * n + i)) : Operand 8).read t =
        (Operand.mem (buffer v s + BitVec.ofNat 64 (4 * n + i)) : Operand 8).read s ^^^
          (layout v).mask.toBitVec := by
    have word := effect.writes
    change memLoad t.external ((v.am (fin4 i hi)).addr s _) 8 =
      memLoad s.external ((v.am (fin4 i hi)).addr s _) 8 ^^^ (layout v).mask.toBitVec at word
    rw [addr] at word
    have original : s.external[buffer v s + BitVec.ofNat 64 (4 * n + i)]? =
        some bytes[(⟨4 * n + i, index⟩ : Fin 64)] := by
      simpa only [Nat.lt_irrefl, ↓reduceIte, Stored] using state.stored ⟨4 * n + i, index⟩
    change (Operand.mem (buffer v s + BitVec.ofNat 64 (4 * n + i)) : Operand 8).read t =
      (Operand.mem (buffer v s + BitVec.ofNat 64 (4 * n + i)) : Operand 8).read s ^^^
        (layout v).mask.toBitVec at word
    rw [read_byte original] at word
    rw [read_byte original]
    exact word
  have stored := state.stored.xor index single written
  have stored' : Stored t (buffer v t) bytes (layout v).mask (4 * n + i + 1) := by
    rw [buffer_of_agrees agrees]
    exact stored
  refine ⟨t, run, readyT, state.toMemory.loaded_after loaded agrees, ?_, agrees⟩
  refine ⟨state.toMemory.after agrees, effect.rip.trans (xor_next v i hi), ?_, stored'⟩
  exact (single.read (n := 64) (r := 0) (by simp)).trans state.counter

theorem xor_four [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    {n : Nat} {bytes : Vector UInt8 64}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (state : Position v s n 0 bytes) (hn : n < 16) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      Position v t n 4 bytes ∧ AgreesExcept (footprint v s) s t := by
  obtain ⟨a, runA, readyA, loadedA, stateA, agreesA⟩ := xor_step ready loaded outside state hn (by decide)
  obtain ⟨b, runB, readyB, loadedB, stateB, agreesB⟩ := xor_step readyA loadedA outside stateA hn (by decide)
  obtain ⟨c, runC, readyC, loadedC, stateC, agreesC⟩ := xor_step readyB loadedB outside stateB hn (by decide)
  obtain ⟨t, runD, readyD, loadedD, stateD, agreesD⟩ := xor_step readyC loadedC outside stateC hn (by decide)
  exact ⟨t, ((runA.trans runB).trans runC).trans runD, readyD, loadedD, stateD,
    footprint_trans (footprint_trans (footprint_trans agreesA agreesB) agreesC) agreesD⟩

theorem loop_from_layout [Bindings] {v : Variant} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (remaining : Nat) :
    ∀ (s : RamState) (n : Nat) (bytes : Vector UInt8 64),
      n + remaining = 16 → n < 16 → ReadyToStep s → ProgramLoaded s →
      Position v s n 0 bytes →
      ∃ t, Advances boundary (7 * remaining) s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
        t.RIP = (if n + remaining = 16 then v.exit else v.entry) ∧
        t.regValue .rax = BitVec.ofNat 64 (4 * (n + remaining) + (layout v).first) ∧
        AgreesExcept (footprint v s) s t ∧
        Stored t (buffer v s) bytes (layout v).mask (4 * (n + remaining)) := by
  induction remaining with
  | zero =>
      intro s n bytes bound hn
      omega
  | succ remaining ih =>
      intro s n bytes bound hn ready loaded state
      obtain ⟨u, runU, readyU, loadedU, stateU, agreesU⟩ := xor_four ready loaded outside state hn
      obtain ⟨v', runV, readyV, loadedV, ripV, counterV, control⟩ :=
        advance_of_layout readyU loadedU outside stateU.rip stateU.counter hn
      have agreesV : AgreesExcept [.reg 0, .flags, .rip] u v' := control.mono (by simp)
      have total := footprint_trans agreesU (agreesV.mono (by simp [footprint]))
      have memory := stateU.toMemory.after (agreesV.mono (by simp [footprint]))
      have storedU := stateU.stored.of_agrees agreesV (by simp [Component.Covers])
      have stored : Stored v' (buffer v v') bytes (layout v).mask (4 * (n + 1)) := by
        rw [buffer_of_agrees (agreesV.mono (by simp [footprint]))]
        have count : 4 * n + 4 = 4 * (n + 1) := by omega
        rw [← count]
        exact storedU
      have storedS : Stored v' (buffer v s) bytes (layout v).mask (4 * (n + 1)) := by
        rw [← buffer_of_agrees total]
        exact stored
      by_cases done : remaining = 0
      · subst remaining
        have eq : n + 1 = 16 := by omega
        refine ⟨v', runU.trans runV, readyV, loadedV, ?_, ?_, total, ?_⟩
        · simpa [eq] using ripV
        · simpa [eq] using counterV
        · simpa [eq] using storedS
      · have more : n + 1 < 16 := by omega
        have stateV : Position v v' (n + 1) 0 bytes := by
          refine ⟨memory, ?_, counterV, stored⟩
          have ripEntry : v'.RIP = v.entry := by simpa [more] using ripV
          rw [ripEntry]
          rfl
        obtain ⟨t, runT, readyT, loadedT, ripT, counterT, agreesT, storedT⟩ :=
          ih v' (n + 1) bytes (by omega) more readyV loadedV stateV
        refine ⟨t, ?_, readyT, loadedT, ?_, ?_, footprint_trans total agreesT, ?_⟩
        · have run := (runU.trans runV).trans runT
          have eq : 4 + 3 + 7 * remaining = 7 * (remaining + 1) := by omega
          simpa [eq] using run
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ripT
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using counterT
        · have storedFinal := storedT
          rw [buffer_of_agrees total] at storedFinal
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using storedFinal

theorem loop_correct_of_layout [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) {bytes : Vector UInt8 64}
    (initial : Position v s 0 0 bytes) :
    ∃ t, Advances boundary 112 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = v.exit ∧
      t.regValue .rax = BitVec.ofNat 64 ((layout v).first + 64) ∧
      AgreesExcept (footprint v s) s t ∧
      Stored t (buffer v s) bytes (layout v).mask 64 := by
  obtain ⟨t, run, readyT, loadedT, ripT, counterT, agreesT, storedT⟩ :=
    loop_from_layout outside 16 s 0 bytes (by decide) (by decide) ready loaded initial
  refine ⟨t, run, readyT, loadedT, ?_, ?_, agreesT, storedT⟩
  · simpa using ripT
  · simpa only [Nat.zero_add, Nat.reduceMul, Nat.add_comm] using counterT

theorem contract_of_layout [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    {pointer : BitVec 64} {raw : ByteArray}
    (pre : Hkdf.Proofs.Common.Pad.Pre v boundary s pointer raw)
    (ready : ReadyToStep s) (outside : ¬ InProgram boundary.rip) :
    Contract v boundary s pointer raw := by
  have buffer_eq : buffer v s = pointer := by
    change s.regValue .rsp + BitVec.ofNat 64 (layout v).bufferOffset = pointer
    exact pre.base.symm
  have writable : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (buffer v s) 64 := by
    rw [buffer_eq]
    exact ⟨⟨pre.writable.readable.low, pre.writable.readable.present⟩, pre.writable.tables⟩
  have memory : Memory v s := by
    refine ⟨writable, ?_⟩
    rw [buffer_eq]
    intro i hi forbidden
    obtain ⟨byte, code⟩ := forbidden
    exact pre.writable.notCode (pointer + BitVec.ofNat 64 i, byte) code i hi rfl
  have stored : Stored s (buffer v s)
      (⟨raw.data, pre.bytes.1⟩ : Vector UInt8 64) (layout v).mask 0 := by
    rw [buffer_eq]
    exact Stored.initial pre.bytes (layout v).mask
  have initial : Position v s 0 0 (⟨raw.data, pre.bytes.1⟩ : Vector UInt8 64) := by
    refine ⟨memory, ?_, ?_, stored⟩
    · simpa [address] using pre.rip
    · simpa only [Nat.mul_zero, Nat.zero_add] using pre.index
  obtain ⟨t, run, readyT, loadedT, ripT, counterT, frameT, storedT⟩ :=
    loop_correct_of_layout ready pre.loaded outside initial
  have frame : AgreesExcept (components pointer) s t := by
    apply frameT.mono
    simp [buffer_eq, footprint, components]
  refine ⟨112, t, run, readyT, ?_, ?_, frame, ?_⟩
  · exact ripT
  · exact counterT
  · rw [buffer_eq] at storedT
    exact Stored.hasBytes pre.bytes.1 (layout v).mask storedT

theorem loop_from [Bindings] {v : Variant} {boundary : ReturnBoundary}
    (first : (layout v).first = 3) (outside : ¬ InProgram boundary.rip) (remaining : Nat) :
    ∀ (s : RamState) (n : Nat) (bytes : Vector UInt8 64),
      n + remaining = 16 → n < 16 → ReadyToStep s → ProgramLoaded s →
      Position v s n 0 bytes →
      ∃ t, Advances boundary (7 * remaining) s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
        t.RIP = (if n + remaining = 16 then v.exit else v.entry) ∧
        t.regValue .rax = BitVec.ofNat 64 (4 * (n + remaining) + (layout v).first) ∧
        AgreesExcept (footprint v s) s t ∧
        Stored t (buffer v s) bytes (layout v).mask (4 * (n + remaining)) := by
  have _ := first
  exact loop_from_layout outside remaining

theorem loop_correct [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    (first : (layout v).first = 3) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) {bytes : Vector UInt8 64}
    (initial : Position v s 0 0 bytes) :
    ∃ t, Advances boundary 112 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = v.exit ∧
      t.regValue .rax = BitVec.ofNat 64 ((layout v).first + 64) ∧
      AgreesExcept (footprint v s) s t ∧
      Stored t (buffer v s) bytes (layout v).mask 64 := by
  have _ := first
  exact loop_correct_of_layout ready loaded outside initial

theorem contract_of_loop [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    {pointer : BitVec 64} {raw : ByteArray}
    (first : (layout v).first = 3)
    (pre : Hkdf.Proofs.Common.Pad.Pre v boundary s pointer raw)
    (ready : ReadyToStep s) (outside : ¬ InProgram boundary.rip) :
    Contract v boundary s pointer raw := by
  have _ := first
  exact contract_of_layout pre ready outside

end Hkdf.Proofs.Common.Pad
