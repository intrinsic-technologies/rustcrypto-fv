import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Progress
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Pair

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix
open Recenter (rawDigit)

theorem extraction_address {s t : RamState} (rsp : stackPtr t = stackPtr s - 120)
    (i : Nat) :
    stackPtr t + BitVec.ofNat 64 (8+i) = stackPtr s - 112 + BitVec.ofNat 64 i := by
  rw [rsp,BitVec.ofNat_add,← BitVec.add_assoc]
  congr 1
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem pair_progress [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {d n : Nat} {p : BitVec 64} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : ExtractionState s t d n) (positive : 0 < n) (hn : n < 32) (ready : ReadyToStep u)
    (effect : (pairEffect p (BitVec.ofNat 8 (111-n)) (BitVec.ofNat 8 (8+2*n))
      (BitVec.ofNat 8 (9+2*n)) t).Holds t u) :
    ExtractionState s u d (n+1) ∧ AgreesExcept (digitComponents s) t u := by
  have src := byteOffset_signExtend (n := 111-n) (by omega)
  have lo := byteOffset_signExtend (n := 8+2*n) (by omega)
  have hi := byteOffset_signExtend (n := 9+2*n) (by omega)
  have lowAddr : (Operand.reg 4 : Operand 64).read t + (BitVec.ofNat 8 (8+2*n)).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 (2*n) := by
    rw [lo]
    exact extraction_address state.rsp _
  have highAddr : (Operand.reg 4 : Operand 64).read t + (BitVec.ofNat 8 (9+2*n)).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 (2*n+1) := by
    rw [hi,show 9+2*n = 8+(2*n+1) by omega]
    exact extraction_address state.rsp _
  have agrees : AgreesExcept (extractionComponents s (2*n) 2) t u := by
    apply effect.agrees.widen
    · intro c hc hm
      simp only [pairEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component,
        Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [extractionComponents,Component.isMem]
    · intro a c hc covered
      simp only [pairEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component,
        Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) 2,
          by simp [extractionComponents],0,by decide,?_⟩
        simpa only [lowAddr,BitVec.add_zero] using he
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) 2,
          by simp [extractionComponents],1,by decide,?_⟩
        rw [highAddr] at he
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero] using he
  refine ⟨state.after pre (by omega) ready agrees ?_ ?_, extraction_agrees (by omega) agrees⟩
  · intro i lower upper
    have cases : i = 2*n ∨ i = 2*n+1 := by omega
    rcases cases with rfl | rfl
    · have h := effect.writes.2.2.1
      simp only [lowAddr, src] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 (111-n)) : Operand 8).read t &&& 15 at h
      rw [state.byte hn,byte_low_nibble] at h
      simpa only [rawDigit,ite_eq_left (show 2*n < 64 by omega)] using h
    · have h := effect.writes.2.2.2
      change (Operand.mem _ : Operand 8).read u = _ at h
      simp only [highAddr, src] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n+1)) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 (111-n)) : Operand 8).read t >>> 4 at h
      rw [state.byte hn,byte_high_nibble] at h
      simpa only [rawDigit,ite_eq_left (show 2*n+1 < 64 by omega)] using h
  · intro positive
    exact (effect.agrees.read (n := 8) (r := 0) (by simp [pairEffect,Effect.components])).trans
      (state.rax (by omega))

theorem pair_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d n pc : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : ExtractionState s t d n)
    (positive : 0 < n) (hn : n < 32)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (code : Extracted.textBytes.toListFrom pc 21 =
      pairBytes (BitVec.ofNat 8 (111-n)) (BitVec.ofNat 8 (8+2*n)) (BitVec.ofNat 8 (9+2*n)))
    (bound : pc + 21 < 118431) :
    ∃ fuel u, Advances boundary fuel t u ∧ ExtractionState s u d (n+1) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc+21) ∧
      AgreesExcept (digitComponents s) t u := by
  let p := Extracted.textAddress + BitVec.ofNat 64 pc
  have next : ∀ offset ∈ ([5,7,10,14,17,21] : List Nat), p + BitVec.ofNat 64 offset ≠ boundary.rip := by
    intro offset ho
    have hle : offset ≤ 21 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
    have addr : p + BitVec.ofNat 64 offset = Extracted.textAddress + BitVec.ofNat 64 (pc+offset) := by
      simp only [p,BitVec.ofNat_add,BitVec.add_assoc]
    rw [addr]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ (by omega))
  have hp : PairPre p (BitVec.ofNat 8 (111-n)) (BitVec.ofNat 8 (8+2*n))
      (BitVec.ofNat 8 (9+2*n)) t := by
    have sign (i : Nat) (h : i < 128) := byteOffset_signExtend h
    refine ⟨rip,?_,?_,?_,?_⟩
    · rw [sign _ (by omega)]
      exact state.toState.stack_readable (frameOffset := 120) pre (by decide) (by omega)
    · intro offset ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl
      all_goals rw [sign _ (by omega)]
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 8+2*n) (len := 1) (by decide) (by omega) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 9+2*n) (len := 1) (by decide) (by omega) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
    · rw [sign _ (by omega),sign _ (by omega)]
      have hn1 : BitVec.ofNat 64 (9+2*n) - BitVec.ofNat 64 (8+2*n) = 1 := by
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
        rw [show 9+2*n-(8+2*n) = 1 by omega]
        rfl
      have hn2 : BitVec.ofNat 64 (8+2*n) - BitVec.ofNat 64 (9+2*n) = -1 := by
        rw [← hn1]
        simp only [BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.neg_neg,BitVec.add_comm]
      simp [OffsetsApart,hn1,hn2]
    · intro offset ho start len hlen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl
      all_goals rw [sign _ (by omega)]
      all_goals
        have addr : p + BitVec.ofNat 64 start = Extracted.textAddress + BitVec.ofNat 64 (pc+start) := by
          simp only [p,BitVec.ofNat_add,BitVec.add_assoc]
        rw [addr]
        exact state.toState.stack_code (frameOffset := 120) pre (by decide) (by omega) (by omega)
  obtain ⟨fuel,u,run,ready,_,effect⟩ := pair_block boundary p _ _ _ next t
    (state.ready)
    (programText_slice (programLoaded_codeIn (state.toState.loaded pre)) pc _ (by simpa [pairBytes] using Nat.le_of_lt bound) code) hp
  have result := pair_progress pre state positive hn ready effect
  refine ⟨fuel,u,run,result.1,?_,result.2⟩
  exact effect.rip.trans (by simp only [pairEffect,p,BitVec.ofNat_add,BitVec.add_assoc]; rfl)

end P256.Proofs.Projective.Multiply.Machine.Radix
