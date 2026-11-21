import Sha3.Proofs.Permutation.Code
import Sha3.Proofs.Permutation.RoundMachine.Instructions.Control
import Sha3.Proofs.Permutation.RoundMachine.Instructions.Bytes
import Sha3.Proofs.Run

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program Prelude

def controlEffect (copy : Copy) (n : Nat) : Effect where
  rip := roundPC copy (n + 1)
  writes := [⟨(.reg 2 : Operand 64), BitVec.ofNat 64 (8 * (n + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec (BitVec.ofNat 64 (8 * (n + 1))) 192))

theorem counter_add_eight (n : Nat) :
    BitVec.ofNat 64 (8 * n) + 8 = BitVec.ofNat 64 (8 * (n + 1)) := by
  simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
  rfl

theorem control_branch_target (copy : Copy) {n : Nat} (hn : n < 24) :
    (branchEffect (condHolds 5 (cmpSpec (BitVec.ofNat 64 (8 * (n + 1))) 192))
      (storeAddress copy) (roundAddress copy)).rip = roundPC copy (n + 1) := by
  have h : ∀ i : Fin 24,
      (branchEffect (condHolds 5 (cmpSpec (BitVec.ofNat 64 (8 * (i.val + 1))) 192))
        (storeAddress copy) (roundAddress copy)).rip = roundPC copy (i.val + 1) := by
    cases copy <;> decide +kernel
  exact h ⟨n, hn⟩

theorem control_pc_in_program (copy : Copy) {p : BitVec 64}
    (hp : p ∈ [entryAddress copy + 0x4fe, entryAddress copy + 0x505,
      roundAddress copy, storeAddress copy]) : InProgram p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    apply inProgram_permutation_address <;> cases copy <;> decide +kernel

theorem control_pc_ne_boundary (copy : Copy) {boundary : ReturnBoundary}
    (hb : ¬ InProgram boundary.rip) {p : BitVec 64}
    (hp : p ∈ [entryAddress copy + 0x4fe, entryAddress copy + 0x505,
      roundAddress copy, storeAddress copy]) : p ≠ boundary.rip := by
  intro heq
  exact hb (heq ▸ control_pc_in_program copy hp)

theorem roundPC_ne_boundary (copy : Copy) {boundary : ReturnBoundary}
    (hb : ¬ InProgram boundary.rip) (n : Nat) : roundPC copy n ≠ boundary.rip := by
  apply control_pc_ne_boundary copy hb
  unfold roundPC
  split <;> simp

theorem control_add_code (copy : Copy) :
    ∀ x ∈ codeRange (entryAddress copy + 0x4fa) [0x48, 0x83, 0xc2, 0x08],
      x ∈ roundCode copy :=
  instructionCode_subset_roundCode copy (by cases copy <;> decide +kernel)

theorem control_cmp_code (copy : Copy) :
    ∀ x ∈ codeRange (entryAddress copy + 0x4fe) [0x48, 0x81, 0xfa, 0xc0, 0, 0, 0],
      x ∈ roundCode copy :=
  instructionCode_subset_roundCode copy (by cases copy <;> decide +kernel)

theorem control_jne_code (copy : Copy) :
    ∀ x ∈ codeRange (entryAddress copy + 0x505) [0x0f, 0x85, 0xe5, 0xfb, 0xff, 0xff],
      x ∈ roundCode copy :=
  instructionCode_subset_roundCode copy (by cases copy <;> decide +kernel)

theorem roundCode_subset_programImage (copy : Copy) :
    ∀ x ∈ roundCode copy, x ∈ Extracted.programImage := by
  intro x hx
  exact imageSections_mem_toCodeMap_of_fetchByte (roundCode_image copy x hx).2

theorem control_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {code : CodeMap}
    (hcode : ∀ x ∈ roundCode copy, x ∈ code) (hb : ¬ InProgram boundary.rip)
    {n : Nat} (hn : n < 24) :
    AdvanceTriple boundary 3
      (fun s ↦ s.RIP = (entryAddress copy + 0x4fa : BitVec 64) ∧
        s.regValue .rdx = BitVec.ofNat 64 (8 * n))
      code (fun s t ↦ (controlEffect copy n).Holds s t) := by
  intro s hs hc hp
  obtain ⟨s₁, hrun₁, hs₁, he₁⟩ := (control_add_step copy).advances hs
    (hc.mono (fun x hx ↦ hcode x (control_add_code copy x hx))) hp.1
    (control_pc_ne_boundary copy hb (by simp [addR64Imm8Effect, BitVec.add_assoc]))
  have hc₁ := he₁.codeIn (addR64Imm8Effect_avoids _ _ _ _ _) hc
  have hcounter : (Operand.reg 2 : Operand 64).read s₁ =
      BitVec.ofNat 64 (8 * (n + 1)) := by
    have hw := he₁.writes
    change (Operand.reg 2 : Operand 64).read s₁ = s.regValue .rdx + 8 at hw
    rw [hp.2, counter_add_eight] at hw
    exact hw
  obtain ⟨s₂, hrun₂, hs₂, he₂⟩ := (control_cmp_step copy).advances hs₁
    (hc₁.mono (fun x hx ↦ hcode x (control_cmp_code copy x hx)))
    (by simpa only [addR64Imm8Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceAdd] using he₁.rip)
    (control_pc_ne_boundary copy hb (by simp [cmpR64Imm32Effect, BitVec.add_assoc]))
  have hc₂ := he₂.codeIn (cmpR64Imm32Effect_avoids _ _ _ _ _) hc₁
  have hflags : StatusFlags.ofRFLAGS s₂.RFLAGS =
      cmpSpec (BitVec.ofNat 64 (8 * (n + 1))) 192 := by
    have hf := he₂.flags
    change (StatusFlagsOutcome.ofStatusFlags (cmpSpec
      ((Operand.reg 2 : Operand 64).read s₁) 192)).Allows _ at hf
    rw [hcounter] at hf
    cases hleft : StatusFlags.ofRFLAGS s₂.RFLAGS
    cases hright : cmpSpec (BitVec.ofNat 64 (8 * (n + 1))) 192
    rw [hleft, hright] at hf
    rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl
  have htarget :
      (jccEffect (entryAddress copy + 0x505) 6 5 0xfffffffffffffbe5 s₂).rip =
        roundPC copy (n + 1) := by
    simp only [jccEffect, branchTarget, BitVec.add_assoc]
    change (branchEffect (condHolds 5 (StatusFlags.ofRFLAGS s₂.RFLAGS))
      (storeAddress copy) (roundAddress copy)).rip = _
    rw [hflags]
    exact control_branch_target copy hn
  obtain ⟨t, hrun₃, ht, he₃⟩ := (control_jne_step copy).advances hs₂
    (hc₂.mono (fun x hx ↦ hcode x (control_jne_code copy x hx)))
    (by simpa only [cmpR64Imm32Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceAdd] using he₂.rip)
    (htarget ▸ roundPC_ne_boundary copy hb (n + 1))
  refine ⟨t, (hrun₁.trans hrun₂).trans hrun₃, ht,
    he₃.codeIn (branchEffect_avoids _ _ _ _) hc₂, ?_⟩
  refine ⟨he₃.rip.trans htarget, ?_, ?_, ?_⟩
  · change (Operand.reg 2 : Operand 64).read t = _
    rw [he₃.agrees.read (by simp [jccEffect]),
      he₂.agrees.read (by simp), hcounter]
  · change (StatusFlagsOutcome.ofStatusFlags
      (cmpSpec (BitVec.ofNat 64 (8 * (n + 1))) 192)).Allows _
    rw [he₃.agrees.rflags (by simp [jccEffect]) (by simp [jccEffect]), hflags]
    exact StatusFlagsOutcome.allows_ofStatusFlags _
  · apply ((he₁.agrees.trans he₂.agrees).trans he₃.agrees).mono
    intro c hc'
    change c ∈ ([.reg 2, .flags, .rip] ++ [.flags, .rip]) ++ [.rip] at hc'
    change c ∈ [.reg 2, .flags, .rip]
    simpa [or_assoc, or_left_comm, or_comm] using hc'

theorem control_advance_image [Bindings] (copy : Copy) {boundary : ReturnBoundary}
    (hb : ¬ InProgram boundary.rip) {n : Nat} (hn : n < 24) :
    AdvanceTriple boundary 3
      (fun s ↦ s.RIP = (entryAddress copy + 0x4fa : BitVec 64) ∧
        s.regValue .rdx = BitVec.ofNat 64 (8 * n))
      Extracted.programImage (fun s t ↦ (controlEffect copy n).Holds s t) :=
  control_advance copy (roundCode_subset_programImage copy) hb hn

theorem controlEffect_external {copy : Copy} {n : Nat} {s t : RamState}
    (he : (controlEffect copy n).Holds s t) : t.external = s.external :=
  he.agrees.external (by
    simp only [controlEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component_reg]
    rintro c (rfl | rfl | rfl) x <;> exact id)

theorem controlEffect_read {copy : Copy} {n : Nat} {s t : RamState} {r : BitVec 5}
    (he : (controlEffect copy n).Holds s t) (hr : r ≠ 2) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
  he.agrees.read (by
    change Component.reg r ∉ [.reg 2, .flags, .rip]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      Component.reg.injEq] using hr)

theorem controlEffect_callFrame {copy : Copy} {n : Nat} {initial s t : RamState}
    (he : (controlEffect copy n).Holds s t) (hf : CallFrame initial s) : CallFrame initial t := by
  have hm := controlEffect_external he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (he.agrees.scalarFrame_eq (by simp [controlEffect, Effect.components])).trans hf.rest⟩
  · exact (controlEffect_read he (r := 4) (by decide)).trans hf.stack
  · change memLoad t.external _ 64 = _
    rw [hm]
    exact hf.pointer
  · intro i
    change memLoad t.external _ 64 = _
    rw [hm]
    exact hf.saved i
  · change memLoad t.external _ 64 = _
    rw [hm]
    exact hf.returnSlot
  · unfold MemoryWriteFrame
    rw [hm]
    exact hf.memory
  · rw [hm]
    exact hf.grows

theorem controlEffect_lanes {copy : Copy} {n : Nat} {s t : RamState} (sp : BitVec 64)
    (he : (controlEffect copy n).Holds s t) : readLanes sp t = readLanes sp s := by
  apply funext
  intro (i : Fin 25)
  finite_cases i <;> dsimp [readLanes, laneOperands] <;>
    first
    | exact controlEffect_read he (by decide)
    | change memLoad t.external _ 64 = memLoad s.external _ 64
      rw [controlEffect_external he]

theorem controlEffect_roundInvariant {copy : Copy} {n : Nat} {initial s t : RamState}
    {a : Keccak.Lanes}
    (he : (controlEffect copy n).Holds s t) (hf : CallFrame initial s)
    (hl : readLanes (frameBase initial) s = a) : RoundInvariant copy initial (n + 1) a t :=
  ⟨controlEffect_callFrame he hf, he.rip, he.writes,
    (controlEffect_lanes (frameBase initial) he).trans hl⟩

end Sha3.Proofs.Permutation.RoundMachine
