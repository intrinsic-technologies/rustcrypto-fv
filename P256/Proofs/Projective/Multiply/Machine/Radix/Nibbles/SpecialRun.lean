import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Run
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Special

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix
open Recenter (rawDigit)

theorem firstPair_progress [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {d : Nat} {p : BitVec 64} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : ExtractionState s t d 0) (ready : ReadyToStep u)
    (effect : (firstPairEffect p (BitVec.ofNat 8 111) (BitVec.ofNat 8 8)
      (BitVec.ofNat 8 9) t).Holds t u) :
    ExtractionState s u d 1 ∧ AgreesExcept (digitComponents s) t u := by
  have src := byteOffset_signExtend (n := 111) (by omega)
  have lo := byteOffset_signExtend (n := 8) (by omega)
  have hi := byteOffset_signExtend (n := 9) (by omega)
  have lowAddr : (Operand.reg 4 : Operand 64).read t + (BitVec.ofNat 8 8).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 0 := by
    rw [lo]
    exact extraction_address state.rsp 0
  have highAddr : (Operand.reg 4 : Operand 64).read t + (BitVec.ofNat 8 9).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 1 := by
    rw [hi]
    exact extraction_address state.rsp 1
  have agrees : AgreesExcept (extractionComponents s 0 2) t u := by
    apply effect.agrees.widen
    · intro c hc hm
      simp only [firstPairEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component,
        Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [extractionComponents,Component.isMem]
    · intro a c hc covered
      simp only [firstPairEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component,
        Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 0) 2,
          by simp [extractionComponents],0,by decide,?_⟩
        simpa only [lowAddr,BitVec.add_zero] using he
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 0) 2,
          by simp [extractionComponents],1,by decide,?_⟩
        rw [highAddr] at he
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero] using he
  refine ⟨state.after pre (k := 1) (by omega) ready agrees ?_ ?_, extraction_agrees (by omega) agrees⟩
  · intro i lower upper
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · have h := effect.writes.2.2.1
      simp only [lowAddr, src] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 0) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 111) : Operand 8).read t &&& 15 at h
      rw [state.byte (i := 0) (by decide),byte_low_nibble] at h
      simpa only [rawDigit,ite_eq_left (show (0 : Nat) < 64 by omega)] using h
    · have h := effect.writes.2.2.2
      change (Operand.mem _ : Operand 8).read u = _ at h
      simp only [highAddr, src] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 1) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 111) : Operand 8).read t >>> 4 at h
      rw [state.byte (i := 0) (by decide),byte_high_nibble] at h
      simpa only [rawDigit,ite_eq_left (show (1 : Nat) < 64 by omega)] using h
  · intro positive
    have h := congrArg (BitVec.setWidth 8) effect.writes.2.1
    change (Operand.reg 0 : Operand 8).read u =
      (mergeGPR 8 ((Operand.mem ((Operand.reg 4 : Operand 64).read t + (111 : BitVec 8).signExtend 64) : Operand 8).read t &&& 15)
        (((Operand.mem ((Operand.reg 4 : Operand 64).read t + (111 : BitVec 8).signExtend 64) : Operand 8).read t).setWidth 64)).setWidth 8 at h
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at h
    change (Operand.reg 0 : Operand 8).read u =
      (Operand.mem (stackPtr t + BitVec.ofNat 64 111) : Operand 8).read t &&& 15 at h
    rw [state.byte (i := 0) (by decide),byte_low_nibble] at h
    exact h

theorem firstPair_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : ExtractionState s t d 0)
    (rip : t.RIP = 0x10b77f) :
    ∃ fuel u, Advances boundary fuel t u ∧ ExtractionState s u d 1 ∧
      u.RIP = 0x10b793 ∧ AgreesExcept (digitComponents s) t u := by
  have next : ∀ offset ∈ ([5,7,9,13,16,20] : List Nat),
      (0x10b77f : BitVec 64) + BitVec.ofNat 64 offset ≠ boundary.rip := by
    intro offset ho
    have hle : offset ≤ 20 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
    have addr : (0x10b77f : BitVec 64) + BitVec.ofNat 64 offset =
        Extracted.textAddress + BitVec.ofNat 64 (0xb77f+offset) := by
      simp only [BitVec.ofNat_add,← BitVec.add_assoc]
      rfl
    rw [addr]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ (by omega))
  have hp : FirstPairPre 0x10b77f 111 8 9 t := by
    refine ⟨rip,?_,?_,by simp [OffsetsApart],?_⟩
    · exact state.toState.stack_readable (frameOffset := 120) pre (offset := 111) (by decide) (by decide)
    · intro offset ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 8) (len := 1) (by decide) (by decide) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 9) (len := 1) (by decide) (by decide) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
    · intro offset ho start len hlen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl
      all_goals
        have addr : (0x10b77f : BitVec 64) + BitVec.ofNat 64 start =
            Extracted.textAddress + BitVec.ofNat 64 (0xb77f+start) := by
          simp only [BitVec.ofNat_add,← BitVec.add_assoc]
          rfl
        rw [addr]
      · exact state.toState.stack_code (frameOffset := 120) pre (offset := 8) (by decide) (by decide) (by omega)
      · exact state.toState.stack_code (frameOffset := 120) pre (offset := 9) (by decide) (by decide) (by omega)
  obtain ⟨fuel,u,run,ready,_,effect⟩ := firstPair_block boundary 0x10b77f 111 8 9 next t
    (state.ready)
    (programText_slice (programLoaded_codeIn (state.toState.loaded pre)) 0xb77f _ (by decide) (by decide +kernel)) hp
  have result := firstPair_progress pre state ready effect
  exact ⟨fuel,u,run,result.1,effect.rip,result.2⟩

private theorem byteOffsets_apart {a b : Nat} (ha : a < 128) (hb : b < 128) (hne : a ≠ b) :
    OffsetsApart ((BitVec.ofNat 8 a).signExtend 64) 1 ((BitVec.ofNat 8 b).signExtend 64) 1 := by
  rw [byteOffset_signExtend ha,byteOffset_signExtend hb]
  simp only [OffsetsApart,BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

theorem doublePair_progress [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {d n : Nat} {p : BitVec 64} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : ExtractionState s t d n) (positive : 0 < n) (hn : n+1 < 32)
    (ready : ReadyToStep u)
    (effect : (doublePairEffect p (BitVec.ofNat 8 (111-n)) (BitVec.ofNat 8 (110-n))
      (BitVec.ofNat 8 (8+2*n)) (BitVec.ofNat 8 (9+2*n))
      (BitVec.ofNat 8 (10+2*n)) (BitVec.ofNat 8 (11+2*n)) t).Holds t u) :
    ExtractionState s u d (n+2) ∧ AgreesExcept (digitComponents s) t u := by
  have src0 := byteOffset_signExtend (n := 111-n) (by omega)
  have src1 := byteOffset_signExtend (n := 110-n) (by omega)
  have addr0 : (Operand.reg 4 : Operand 64).read t +
      (BitVec.ofNat 8 (8+2*n)).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 (2*n) := by
    rw [byteOffset_signExtend (by omega),show 8+2*n = 8+(2*n) by omega]
    exact extraction_address state.rsp _
  have addr1 : (Operand.reg 4 : Operand 64).read t +
      (BitVec.ofNat 8 (9+2*n)).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 (2*n+1) := by
    rw [byteOffset_signExtend (by omega),show 9+2*n = 8+(2*n+1) by omega]
    exact extraction_address state.rsp _
  have addr2 : (Operand.reg 4 : Operand 64).read t +
      (BitVec.ofNat 8 (10+2*n)).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 (2*n+2) := by
    rw [byteOffset_signExtend (by omega),show 10+2*n = 8+(2*n+2) by omega]
    exact extraction_address state.rsp _
  have addr3 : (Operand.reg 4 : Operand 64).read t +
      (BitVec.ofNat 8 (11+2*n)).signExtend 64 =
      stackPtr s - 112 + BitVec.ofNat 64 (2*n+3) := by
    rw [byteOffset_signExtend (by omega),show 11+2*n = 8+(2*n+3) by omega]
    exact extraction_address state.rsp _
  have agrees : AgreesExcept (extractionComponents s (2*n) 4) t u := by
    apply effect.agrees.widen
    · intro c hc hm
      simp only [doublePairEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component,
        Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [extractionComponents,Component.isMem]
    · intro a c hc covered
      simp only [doublePairEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component,
        Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) 4,
          by simp [extractionComponents],0,by decide,?_⟩
        rw [addr0] at he
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero] using he
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) 4,
          by simp [extractionComponents],1,by decide,?_⟩
        rw [addr1] at he
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero] using he
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) 4,
          by simp [extractionComponents],2,by decide,?_⟩
        rw [addr2] at he
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero] using he
      · obtain ⟨j,hj,he⟩ := covered
        have hz : j = 0 := by omega
        subst j
        refine ⟨.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) 4,
          by simp [extractionComponents],3,by decide,?_⟩
        rw [addr3] at he
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero] using he
  refine ⟨state.after pre (k := 2) (by omega) ready agrees ?_ ?_, extraction_agrees (by omega) agrees⟩
  · intro i lower upper
    have cases : i = 2*n ∨ i = 2*n+1 ∨ i = 2*n+2 ∨ i = 2*n+3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h := effect.writes.2.2.2.1
      change (Operand.mem _ : Operand 8).read u = _ at h
      simp only [addr0,src0] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n)) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 (111-n)) : Operand 8).read t &&& 15 at h
      rw [state.byte (i := n) (by omega),byte_low_nibble] at h
      simpa only [rawDigit,ite_eq_left (show 2*n < 64 by omega)] using h
    · have h := effect.writes.2.2.2.2.1
      change (Operand.mem _ : Operand 8).read u = _ at h
      simp only [addr1,src0] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n+1)) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 (111-n)) : Operand 8).read t >>> 4 at h
      rw [state.byte (i := n) (by omega),byte_high_nibble] at h
      simpa only [rawDigit,ite_eq_left (show 2*n+1 < 64 by omega)] using h
    · have h := effect.writes.2.2.2.2.2.1
      change (Operand.mem _ : Operand 8).read u = _ at h
      simp only [addr2,src1] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n+2)) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 (110-n)) : Operand 8).read t &&& 15 at h
      rw [show 110-n = 111-(n+1) by omega,state.byte (i := n+1) (by omega),byte_low_nibble] at h
      simpa only [rawDigit,ite_eq_left (show 2*n+2 < 64 by omega),show 2*(n+1) = 2*n+2 by omega] using h
    · have h := effect.writes.2.2.2.2.2.2
      change (Operand.mem _ : Operand 8).read u = _ at h
      simp only [addr3,src1] at h
      change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*n+3)) : Operand 8).read u =
        (Operand.mem (stackPtr t + BitVec.ofNat 64 (110-n)) : Operand 8).read t >>> 4 at h
      rw [show 110-n = 111-(n+1) by omega,state.byte (i := n+1) (by omega),byte_high_nibble] at h
      simpa only [rawDigit,ite_eq_left (show 2*n+3 < 64 by omega),show 2*(n+1)+1 = 2*n+3 by omega] using h
  · intro positive
    exact (effect.agrees.read (n := 8) (r := 0) (by simp [doublePairEffect,Effect.components])).trans
      (state.rax (by omega))

theorem doublePair_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d n pc : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : ExtractionState s t d n)
    (positive : 0 < n) (hn : n+1 < 32)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (code : Extracted.textBytes.toListFrom pc 44 =
      doublePairBytes (BitVec.ofNat 8 (111-n)) (BitVec.ofNat 8 (110-n))
        (BitVec.ofNat 8 (8+2*n)) (BitVec.ofNat 8 (9+2*n))
        (BitVec.ofNat 8 (10+2*n)) (BitVec.ofNat 8 (11+2*n)))
    (bound : pc+44 < 118431) :
    ∃ fuel u, Advances boundary fuel t u ∧ ExtractionState s u d (n+2) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc+44) ∧
      AgreesExcept (digitComponents s) t u := by
  let p := Extracted.textAddress + BitVec.ofNat 64 pc
  have next : ∀ offset ∈ ([5,10,12,16,21,24,28,30,33,37,40,44] : List Nat),
      p + BitVec.ofNat 64 offset ≠ boundary.rip := by
    intro offset ho
    have hle : offset ≤ 44 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
    have addr : p + BitVec.ofNat 64 offset = Extracted.textAddress + BitVec.ofNat 64 (pc+offset) := by
      simp only [p,BitVec.ofNat_add,BitVec.add_assoc]
    rw [addr]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ (by omega))
  have hp : DoublePairPre p (BitVec.ofNat 8 (111-n)) (BitVec.ofNat 8 (110-n))
      (BitVec.ofNat 8 (8+2*n)) (BitVec.ofNat 8 (9+2*n))
      (BitVec.ofNat 8 (10+2*n)) (BitVec.ofNat 8 (11+2*n)) t := by
    have sign (i : Nat) (h : i < 128) := byteOffset_signExtend h
    refine ⟨rip,?_,?_,?_,?_⟩
    · intro offset ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl
      all_goals rw [sign _ (by omega)]
      all_goals exact state.toState.stack_readable (frameOffset := 120) pre (by decide) (by omega)
    · intro offset ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      all_goals rw [sign _ (by omega)]
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 8+2*n) (len := 1) (by decide) (by omega) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 9+2*n) (len := 1) (by decide) (by omega) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 10+2*n) (len := 1) (by decide) (by omega) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
      · have h := state.toState.stack_writable (frameOffset := 120) pre (offset := 11+2*n) (len := 1) (by decide) (by omega) (by decide)
        exact ⟨h.low, h.mem, h.tables⟩
    · refine ⟨?_,?_,?_,?_,?_,?_⟩
      all_goals exact byteOffsets_apart (by omega) (by omega) (by omega)
    · intro offset ho start len hlen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      all_goals rw [sign _ (by omega)]
      all_goals
        have addr : p + BitVec.ofNat 64 start = Extracted.textAddress + BitVec.ofNat 64 (pc+start) := by
          simp only [p,BitVec.ofNat_add,BitVec.add_assoc]
        rw [addr]
        exact state.toState.stack_code (frameOffset := 120) pre (by decide) (by omega) (by omega)
  obtain ⟨fuel,u,run,ready,_,effect⟩ := doublePair_block boundary p _ _ _ _ _ _ next t
    (state.ready)
    (programText_slice (programLoaded_codeIn (state.toState.loaded pre)) pc _
      (by simpa [doublePairBytes] using Nat.le_of_lt bound) code) hp
  have result := doublePair_progress pre state positive hn ready effect
  refine ⟨fuel,u,run,result.1,?_,result.2⟩
  exact effect.rip.trans (by simp only [doublePairEffect,p,BitVec.ofNat_add,BitVec.add_assoc]; rfl)

end P256.Proofs.Projective.Multiply.Machine.Radix
