import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.TailRun
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix

structure LoopState [Bindings] (s t : RamState) (d k : Nat) : Prop
    extends State s t, Progress (stackPtr s-112) t d (2*k) 0 where
  rip : t.RIP = if k < 32 then 0x10ba30 else 0x10ba6c
  counter : (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (2*k+2)
  stored : (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*k)) : Operand 8).read t =
    rawDigit d (2*k) + BitVec.ofNat 8 (carry d (2*k))

theorem half_next {boundary : ReturnBoundary} (hout : ¬ InProgram boundary.rip)
    (codeOffset : Nat) (hcode : codeOffset+23 < 118431) :
    ∀ offset ∈ ([3,5,9,12,16,19,23] : List Nat),
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro offset ho
  have bound : offset ≤ 23 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact boundary_ne_program hout (inProgram_of_textOffset (codeOffset+offset) (by omega))

theorem loop_iteration [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d k : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : LoopState s t d k) (hk : k < 32) :
    ∃ fuel u, Advances boundary fuel t u ∧ LoopState s u d (k+1) ∧
      AgreesExcept (Radix.digitComponents s) t u := by
  have a1 := half_address state.toState state.counter (offset := 6) (i := 2*k) (by omega)
  have hp1 := half_pre pre state.toState (i := 2*k) (codeOffset := 0xba30) (by omega)
    (by change t.RIP = 0x10ba30; simpa only [ite_eq_left hk] using state.rip) (by decide) a1
  have code1 := programText_slice (programLoaded_codeIn (state.toState.loaded pre)) 0xba30 firstHalfBytes
    (by decide +kernel) (by decide +kernel)
  obtain ⟨f1,v1,run1,ready1,_,e1⟩ := first_half_block boundary 0x10ba30
    (half_next pre.outerBoundary 0xba30 (by decide)) t (state.ready) code1 hp1
  have progress1 := progress_half state.toProgress (by omega) (.inl rfl) (.inr rfl) a1 e1
  have c1 := (half_counter (.inl rfl) (.inr rfl) e1).trans state.counter
  have g1 := byte_agrees (by omega : 2*k < 65) (half_agrees (.inl rfl) (.inr rfl) a1 e1)
  have frame1 := frame_after_digits pre state.toState ready1 g1
  have a2 := half_address frame1 c1 (offset := 7) (i := 2*k+1) (by omega)
  have hp2 := half_pre pre frame1 (i := 2*k+1) (codeOffset := 0xba47) (by omega)
    e1.rip (by decide) a2
  have code2 := programText_slice (programLoaded_codeIn (frame1.loaded pre)) 0xba47 secondHalfBytes
    (by decide +kernel) (by decide +kernel)
  obtain ⟨f2,v2,run2,ready2,_,e2⟩ := second_half_block boundary 0x10ba47
    (half_next pre.outerBoundary 0xba47 (by decide)) v1 ready1 code2 hp2
  have progress2 := progress_half progress1 (by omega) (.inr rfl) (.inl rfl) a2 e2
  have c2 := (half_counter (.inr rfl) (.inl rfl) e2).trans c1
  have g2 := byte_agrees (by omega : 2*k+1 < 65) (half_agrees (.inr rfl) (.inl rfl) a2 e2)
  have frame2 := frame_after_digits pre frame1 ready2 g2
  have index : 2*k+1+1 = 2*(k+1) := by omega
  rw [index] at progress2
  have a3 := half_address frame2 c2 (offset := 8) (i := 2*(k+1)) (by omega)
  simp only [BitVec.ofNat_eq_ofNat] at a3
  have hp3 := tail_pre pre frame2 (by omega) e2.rip a3
  have code3 := programText_slice (programLoaded_codeIn (frame2.loaded pre)) 0xba5e tailBytes
    (by decide +kernel) (by decide +kernel)
  obtain ⟨f3,v3,run3,ready3,_,e3⟩ := tail_block boundary pre.outerBoundary v2 ready2 code3 hp3
  have progress3 := progress_tail progress2 (by omega) a3 e3
  have g3 := byte_agrees (by omega : 2*(k+1) < 65) (tail_agrees a3 e3)
  have frame3 := frame_after_digits pre frame2 ready3 g3
  have counter3 : (Operand.reg 1 : Operand 64).read v3 = BitVec.ofNat 64 (2*(k+1)+2) := by
    have h := e3.writes.1
    change (Operand.reg 1 : Operand 64).read v3 = (Operand.reg 1 : Operand 64).read v2 + 2 at h
    rw [h,c2,show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    congr 1
  have zero3 : (StatusFlags.ofRFLAGS v3.RFLAGS).ZF = decide (k+1 = 32) := by
    have h := e3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS v3.RFLAGS).ZF = ((Operand.reg 1 : Operand 64).read v2 + 2 - 66 == 0) at h
    rw [h,c2]
    have finite : ∀ k : Fin 32, (BitVec.ofNat 64 (2*k.val+2) + 2 - 66 == 0) = decide (k.val+1 = 32) := by
      decide +kernel
    exact finite ⟨k,hk⟩
  have branchRip : (jccEffect 0x10ba6a 2 5 ((0xc4 : BitVec 8).signExtend 64) v3).rip =
      if k+1 < 32 then 0x10ba30 else 0x10ba6c := by
    simp only [jccEffect, branchEffect, condHolds, zero3]
    by_cases hlt : k+1 < 32
    · have hn : k+1 ≠ 32 := by omega
      simp [hlt,hn,branchTarget]
    · have he : k+1 = 32 := by omega
      simp [he]
  have code4 := programText_slice (programLoaded_codeIn (frame3.loaded pre)) 0xba6a [0x75,0xc4]
    (by decide +kernel) (by decide +kernel)
  obtain ⟨u,run4,ready4,e4⟩ := (jcc_rel8_effect_step 0x10ba6a 5 0xc4).advances ready3 code4
    ⟨e3.rip, fun _ => by decide⟩ (by
      rw [branchRip]
      split
      · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xba30 (by decide))
      · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xba6c (by decide)))
  have g4 : AgreesExcept [.rip] v3 u := e4.agrees
  have progress4 := progress_branch progress3 g4
  have frame4 := frame_after_digits pre frame3 ready4 (g4.mono (by simp [Radix.digitComponents]))
  have stored3 : (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 (2*(k+1))) : Operand 8).read v3 =
      rawDigit d (2*(k+1)) + BitVec.ofNat 8 (carry d (2*(k+1))) := by
    have h := e3.writes.2
    change (Operand.mem (halfAddress v2 8) : Operand 8).read v3 = (Operand.reg 0 : Operand 8).read v2 at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [a3] at h
    exact h.trans progress2.accumulator
  refine ⟨_,u,((run1.trans run2).trans run3).trans run4, ?_, ?_⟩
  · refine ⟨frame4,progress4,e4.rip.trans branchRip, ?_, ?_⟩
    · exact (g4.read (n := 64) (r := 1) (by simp)).trans counter3
    · have memory := g4.external (by simp [Component.Covers])
      change memLoad u.external _ 8 = _
      rw [memory]
      exact stored3
  · exact (((g1.trans g2).trans g3).trans g4).mono
      (by simp [digitComponents,Radix.digitComponents])

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
