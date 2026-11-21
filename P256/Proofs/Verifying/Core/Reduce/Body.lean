import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Verifying.Core.Reduce.Values
import P256.Proofs.Verifying.Core.Reduce.Prologue

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset
  programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_reduction [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) :
    ∃ t, Advances boundary 8 s t ∧ FrameState s t ∧ t.RIP = 0x113133 ∧
      t.regValue .rsi = s.regValue .rsi ∧
      (Operand.mem (stackPtr t + 32) : Operand 64).read t = s.regValue .rdi := by
  obtain ⟨u,run,ready,loaded,rip,rsp,memory,agrees⟩ := prologue pre
  have state := ScalarFrame.prologue_frame pre (by decide) ready loaded rsp memory agrees
  have rsi : u.regValue .rsi = s.regValue .rsi := agrees.read (n := 64) (r := 6) (by simp [saveFrame])
  have rdi : u.regValue .rdi = s.regValue .rdi := agrees.read (n := 64) (r := 7) (by simp [saveFrame])
  have bp := block_pre pre state rsi rip
  obtain ⟨t,step,tready,effect⟩ :=
    (mov_m64_r64_effect_step 0x11312e 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x1312e _ (by decide) (by decide +kernel))
      ⟨rip, bp.writable 32 (by decide), bp.apart 32 8 (by decide) 0x1312e 5 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13133 (by decide)))
  change (movM64R64Effect 0x11312e 7 (.sib 4 none 0 (.d8 32)) u).Holds u t at effect
  have frame : AgreesExcept (blockFrame u) u t := effect.agrees.mono (by
    simp [movM64R64Effect, storeEffect, Effect.components, storeAddrAt, AddrMode.addr,
      AddrMode.reg64, Disp.value, blockFrame, stackPtr])
  have final := state.after_effect pre (by decide) tready frame (block_writes pre state) (by simp [blockFrame])
  refine ⟨t,run.trans step,final,effect.rip,
    (frame.read (n := 64) (r := 6) (by simp [blockFrame])).trans rsi, ?_⟩
  rw [show stackPtr t = stackPtr u from final.rsp.trans state.rsp.symm]
  exact effect.writes.trans rdi

theorem low_outputPointer {s t : RamState} (effect : (lowEffect s).Holds s t) :
    (Operand.mem (stackPtr s + 32) : Operand 64).read t =
      (Operand.mem (stackPtr s + 32) : Operand 64).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effect.agrees
  intro i hi c hc ha
  simp only [lowEffect, Effect.components, List.mem_cons, List.not_mem_nil, or_false,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, Write.component_reg,
    Write.component_mem] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j,hj,he⟩ := ha
  · exact OffsetsApart.ne (c₁ := 24) (c₂ := 32) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide) he.symm
  · exact OffsetsApart.ne (c₁ := 16) (c₂ := 32) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide) he.symm
  · exact OffsetsApart.ne (c₁ := 8) (c₂ := 32) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide) he.symm

theorem subtract_body [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) :
    ∃ fuel t, Advances boundary fuel s t ∧ Subtracted s t (Field.readLimbs s (s.regValue .rsi)) := by
  obtain ⟨t0,run0,state0,rip0,rsi0,ptr0⟩ := initialize_reduction pre
  obtain ⟨n1,t1,run1,state1,rip1,rsi1,e1⟩ := block_run (offset := 0x13133) pre state0 rsi0 rip0
    (low_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [lowEffect, Effect.components, blockFrame])
  obtain ⟨n2,t2,run2,state2,rip2,rsi2,e2⟩ := block_run (offset := 0x1316a) pre state1 rsi1 rip1
    (second_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [secondEffect, Effect.components, blockFrame])
  obtain ⟨n3,t3,run3,state3,rip3,rsi3,e3⟩ := block_run (offset := 0x13199) pre state2 rsi2 rip2
    (third_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [thirdEffect, Effect.components, blockFrame])
  obtain ⟨n4,t4,run4,state4,rip4,rsi4,e4⟩ := block_run (offset := 0x131c0) pre state3 rsi3 rip3
    (high_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [highEffect, Effect.components, blockFrame])
  let a := Field.readLimbs s (s.regValue .rsi)
  have x0 : (Operand.mem (t0.regValue .rsi) : Operand 64).read t0 = a.l0 := by
    rw [rsi0]
    change (Operand.mem (s.regValue .rsi) : Operand 64).read t0 =
      (Operand.mem (s.regValue .rsi) : Operand 64).read s
    simpa only [BitVec.add_zero] using input_word pre state0 (offset := 0) (by decide)
  have x1 : (Operand.mem (t1.regValue .rsi + 8) : Operand 64).read t1 = a.l1 := by
    rw [rsi1]
    exact input_word pre state1 (offset := 8) (by decide)
  have x2 : (Operand.mem (t2.regValue .rsi + 16) : Operand 64).read t2 = a.l2 := by
    rw [rsi2]
    exact input_word pre state2 (offset := 16) (by decide)
  have x3 : (Operand.mem (t3.regValue .rsi + 24) : Operand 64).read t3 = a.l3 := by
    rw [rsi3]
    exact input_word pre state3 (offset := 24) (by decide)
  have c1 := e1.writes.2.1
  change t1.regValue .rcx = -((~~~(Operand.mem (t0.regValue .rsi) : Operand 64).read t0 |||
    (0x0c46353d039cdaaf + (Operand.mem (t0.regValue .rsi) : Operand 64).read t0)) >>> 63) at c1
  rw [x0] at c1
  have d1 := e2.writes.2.1
  change t2.regValue .r13 = 0x4319055258e8617c +
    (Operand.mem (t1.regValue .rsi + 8) : Operand 64).read t1 + (t1.regValue .rcx).sshiftRight 63 at d1
  rw [x1,c1] at d1
  change t2.regValue .r13 = (subtractOrder a).l1 at d1
  have b1 := e2.writes.2.2.2.1
  change t2.regValue .r15 = (~~~(Operand.mem (t1.regValue .rsi + 8) : Operand 64).read t1 |||
    (0x4319055258e8617c + (Operand.mem (t1.regValue .rsi + 8) : Operand 64).read t1 +
      (t1.regValue .rcx).sshiftRight 63)) >>> 63 at b1
  rw [x1,c1] at b1
  have d2 := e3.writes.2.1
  change t3.regValue .r15 = ((t2.regValue .r15 - 1) >>> 63) +
    (Operand.mem (t2.regValue .rsi + 16) : Operand 64).read t2 at d2
  rw [x2,b1] at d2
  change t3.regValue .r15 = (subtractOrder a).l2 at d2
  have c3 := e3.writes.2.2.1
  change t3.regValue .rcx = -((~~~(Operand.mem (t2.regValue .rsi + 16) : Operand 64).read t2 |||
    (((t2.regValue .r15 - 1) >>> 63) + (Operand.mem (t2.regValue .rsi + 16) : Operand 64).read t2)) >>> 63) at c3
  rw [x2,b1] at c3
  have d3 := e4.writes.2.1
  change t4.regValue .r14 = 0x100000000 +
    (Operand.mem (t3.regValue .rsi + 24) : Operand 64).read t3 + (t3.regValue .rcx).sshiftRight 63 at d3
  rw [x3,c3] at d3
  change t4.regValue .r14 = (subtractOrder a).l3 at d3
  have zero : t3.regValue .rdi = 0 :=
    (e3.agrees.read (n := 64) (r := 7) (by simp [thirdEffect,Effect.components])).trans
    ((e2.agrees.read (n := 64) (r := 7) (by simp [secondEffect,Effect.components])).trans e1.writes.2.2.1)
  have b3 := e4.writes.2.2.2.1
  change t4.regValue .rdi = (t3.regValue .rdi -
    ((~~~(Operand.mem (t3.regValue .rsi + 24) : Operand 64).read t3 |||
      (0x100000000 + (Operand.mem (t3.regValue .rsi + 24) : Operand 64).read t3 +
        (t3.regValue .rcx).sshiftRight 63)) >>> 63)) >>> 63 at b3
  rw [x3,c3,zero] at b3
  change t4.regValue .rdi = (0#64 - SecretKeyFromBytes.Scalar.orderBorrow a) >>> 63 at b3
  rw [BitVec.zero_sub] at b3
  have f2 : AgreesExcept (borrowFrame t1) t1 t2 := e2.agrees.mono (by simp [secondEffect,Effect.components,borrowFrame])
  have f3 : AgreesExcept (borrowFrame t2) t2 t3 := e3.agrees.mono (by simp [thirdEffect,Effect.components,borrowFrame])
  have f4 : AgreesExcept (borrowFrame t3) t3 t4 := e4.agrees.mono (by simp [highEffect,Effect.components,borrowFrame])
  have slots (offset : Nat) (ho : offset = 16 ∨ offset = 24 ∨ offset = 32) :
      (Operand.mem (stackPtr t4 + BitVec.ofNat 64 offset) : Operand 64).read t4 =
        (Operand.mem (stackPtr t1 + BitVec.ofNat 64 offset) : Operand 64).read t1 := by
    rw [state4.rsp, ← state3.rsp, borrow_slot f4 ho,
      state3.rsp, ← state2.rsp, borrow_slot f3 ho,
      state2.rsp, ← state1.rsp, borrow_slot f2 ho]
  refine ⟨8+n1+n2+n3+n4,t4,((((run0.trans run1).trans run2).trans run3).trans run4),
    { toFrameState := state4
      rip := rip4
      original0 := ?_
      original1 := ?_
      original2 := ?_
      original3 := ?_
      difference0 := ?_
      difference1 := ?_
      difference2 := ?_
      difference3 := d3
      borrow := b3
      outputPointer := ?_ }⟩
  · change (Operand.mem (stackPtr t4 + BitVec.ofNat 64 24) : Operand 64).read t4 = a.l0
    rw [slots 24 (by simp),state1.rsp,← state0.rsp]
    exact e1.writes.2.2.2.1.trans x0
  · exact (e4.agrees.read (n := 64) (r := 12) (by simp [highEffect,Effect.components])).trans
      ((e3.agrees.read (n := 64) (r := 12) (by simp [thirdEffect,Effect.components])).trans
        (e2.writes.1.trans x1))
  · exact (e4.agrees.read (n := 64) (r := 5) (by simp [highEffect,Effect.components])).trans (e3.writes.1.trans x2)
  · exact e4.writes.1.trans x3
  · change (Operand.mem (stackPtr t4 + BitVec.ofNat 64 16) : Operand 64).read t4 = (subtractOrder a).l0
    rw [slots 16 (by simp),state1.rsp,← state0.rsp]
    exact e1.writes.2.2.2.2.1.trans (congrArg (0x0c46353d039cdaaf + ·) x0)
  · exact (e4.agrees.read (n := 64) (r := 13) (by simp [highEffect,Effect.components])).trans
      ((e3.agrees.read (n := 64) (r := 13) (by simp [thirdEffect,Effect.components])).trans d1)
  · exact (e4.agrees.read (n := 64) (r := 15) (by simp [highEffect,Effect.components])).trans d2
  · change (Operand.mem (stackPtr t4 + BitVec.ofNat 64 32) : Operand 64).read t4 = s.regValue .rdi
    rw [slots 32 (by simp),state1.rsp,← state0.rsp]
    exact (low_outputPointer e1).trans ptr0

end P256.Proofs.Verifying.Core.Reduce
