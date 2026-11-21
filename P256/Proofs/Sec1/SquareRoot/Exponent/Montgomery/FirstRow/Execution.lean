import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem scratch_loaded {s t : RamState} (memory : Reduction.MemoryPre s)
    (ag : AgreesExcept (Reduction.scratchComponents s) s t) (loaded : ProgramLoaded s) :
    ProgramLoaded t :=
  memory.loaded (ag.mono (by intro c hc; exact List.mem_append_left _ hc)) loaded

private theorem scratch_apart {s : RamState} {entry : BitVec 64} (he : Entry entry)
    (memory : Reduction.MemoryPre s) (offset size : Nat) (hb : offset+size ≤ 1469) :
    RangeApart (stackPtr s) 112 (entry+BitVec.ofNat 64 offset) size := by
  have h := memory.scratch_apart he 0 112 offset size (by decide) hb
  rw [BitVec.add_zero] at h
  exact h

theorem firstRow_execution [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} (he : Entry entry) (hout : ¬ InProgram boundary.rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : InitializePre (entry+14#64) s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      AgreesExcept (Reduction.scratchComponents s) s t ∧ Nonempty (FirstRowTrace entry s t) := by
  have next (offset size : Nat) (hb : offset+size < 1469) :
      ∀ n : Nat, 0 < n → n ≤ size →
        (entry+BitVec.ofNat 64 offset)+BitVec.ofNat 64 n ≠ boundary.rip := by
    intro n _ hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact instruction_ne_boundary he hout _ (by omega)
  obtain ⟨n1, s1, run1, ready1, _, e1⟩ := initialize_correct (entry+14#64) boundary
    (next 14 44 (by decide)) s ready
    (code_slice he loaded 14 _ (by decide) initialize_bytes) pre
  have f1 := initialize_frame e1
  have mem1 := pre.memory.of_scratch f1
  have loaded1 := scratch_loaded pre.memory f1 loaded
  have ip1 : s1.RIP = entry+58#64 := by
    have h := e1.rip
    change _ = (entry+14#64)+44#64 at h
    simpa only [BitVec.add_assoc, show 14#64+44#64 = 58#64 by decide +kernel] using h
  have m1 : (Operand.reg 1#5 : Operand 64).read s1 = (Operand.reg 1#5 : Operand 64).read s :=
    e1.agrees.read (by simp [initializeEffect, Effect.components, Write.component, Operand.component])
  have b1 : (Operand.reg 9#5 : Operand 64).read s1 = (Operand.reg 2#5 : Operand 64).read s :=
    e1.writes.2.1
  have ptr1 : (Operand.mem (stackPtr s1+24#64) : Operand 64).read s1 =
      (Operand.reg 6#5 : Operand 64).read s := by
    rw [Reduction.scratch_rsp f1]
    exact e1.writes.2.2.2.2.2.2.2.1
  obtain ⟨n2, s2, run2, ready2, _, e2⟩ := firstProducts_correct (entry+58#64) boundary
    (next 58 40 (by decide)) s1 ready1
    (code_slice he loaded1 58 _ (by decide) firstProducts_bytes) ip1
  have f2 := firstProducts_frame e2
  have f12 := Reduction.scratch_trans f1 f2
  have mem2 := mem1.of_scratch f2
  have loaded2 := scratch_loaded mem1 f2 loaded1
  have ip2 : s2.RIP = entry+98#64 := by
    have h := e2.rip
    change _ = (entry+58#64)+40#64 at h
    simpa only [BitVec.add_assoc, show 58#64+40#64 = 98#64 by decide +kernel] using h
  have m2 : (Operand.reg 1#5 : Operand 64).read s2 = (Operand.reg 1#5 : Operand 64).read s :=
    (e2.agrees.read (by simp [firstProductsEffect, Effect.components, Write.component, Operand.component])).trans m1
  have b2 : (Operand.reg 9#5 : Operand 64).read s2 = (Operand.reg 2#5 : Operand 64).read s :=
    (e2.agrees.read (by simp [firstProductsEffect, Effect.components, Write.component, Operand.component])).trans b1
  have pre2 : FirstCarryPre (entry+98#64) s2 := by
    refine ⟨ip2, mem2, scratch_apart he mem2 98 46 (by decide), ?_⟩
    rw [m2]
    exact P256.Proofs.Program.readable_of_grow (readable_limb pre.modulus 8 (by decide)) f12.grow
  obtain ⟨n3, s3, run3, ready3, _, e3⟩ := firstCarry_correct (entry+98#64) boundary
    (next 98 46 (by decide)) s2 ready2
    (code_slice he loaded2 98 _ (by decide) firstCarry_bytes) pre2
  have f3 := firstCarry_frame e3
  have f123 := Reduction.scratch_trans f12 f3
  have mem3 := mem2.of_scratch f3
  have loaded3 := scratch_loaded mem2 f3 loaded2
  have ip3 : s3.RIP = entry+144#64 := by
    have h := e3.rip
    change _ = (entry+98#64)+46#64 at h
    simpa only [BitVec.add_assoc, show 98#64+46#64 = 144#64 by decide +kernel] using h
  have m3 : (Operand.reg 1#5 : Operand 64).read s3 = (Operand.reg 1#5 : Operand 64).read s :=
    (e3.agrees.read (by simp [firstCarryEffect, Effect.components, Write.component, Operand.component])).trans m2
  have b3 : (Operand.reg 9#5 : Operand 64).read s3 = (Operand.reg 2#5 : Operand 64).read s :=
    (e3.agrees.read (by simp [firstCarryEffect, Effect.components, Write.component, Operand.component])).trans b2
  have pre3 : FirstMiddlePre (entry+144#64) s3 := by
    refine ⟨ip3, mem3, scratch_apart he mem3 144 80 (by decide), ?_, ?_, ?_, ?_⟩
    · rw [b3]
      exact P256.Proofs.Program.readable_of_grow pre.right f123.grow
    · change RangeApart (stackPtr s3) 112 _ 32
      rw [Reduction.scratch_rsp f123, b3]
      exact pre.rightApart
    · rw [m3]
      exact P256.Proofs.Program.readable_of_grow pre.modulus f123.grow
    · change RangeApart (stackPtr s3) 112 _ 32
      rw [Reduction.scratch_rsp f123, m3]
      exact pre.modulusApart
  obtain ⟨n4, s4, run4, ready4, _, e4⟩ := firstMiddle_correct (entry+144#64) boundary
    (next 144 80 (by decide)) s3 ready3
    (code_slice he loaded3 144 _ (by decide) firstMiddle_bytes) pre3
  have f4 := firstMiddle_frame e4
  have f1234 := Reduction.scratch_trans f123 f4
  have mem4 := mem3.of_scratch f4
  have loaded4 := scratch_loaded mem3 f4 loaded3
  have ip4 : s4.RIP = entry+224#64 := by
    have h := e4.rip
    change _ = (entry+144#64)+80#64 at h
    simpa only [BitVec.add_assoc, show 144#64+80#64 = 224#64 by decide +kernel] using h
  obtain ⟨n5, s5, run5, ready5, _, e5⟩ := firstHigh_correct (entry+224#64) boundary
    (next 224 57 (by decide)) s4 ready4
    (code_slice he loaded4 224 _ (by decide) firstHigh_bytes)
    ⟨ip4, mem4, scratch_apart he mem4 224 57 (by decide)⟩
  have f5 := firstHigh_frame e5
  have f12345 := Reduction.scratch_trans f1234 f5
  have mem5 := mem4.of_scratch f5
  have loaded5 := scratch_loaded mem4 f5 loaded4
  have ip5 : s5.RIP = entry+281#64 := by
    have h := e5.rip
    change _ = (entry+224#64)+57#64 at h
    simpa only [BitVec.add_assoc, show 224#64+57#64 = 281#64 by decide +kernel] using h
  have ptr5 : (Operand.mem (stackPtr s5+24#64) : Operand 64).read s5 =
      (Operand.reg 6#5 : Operand 64).read s :=
    (firstHigh_pointer e5).trans ((firstMiddle_pointer e4).trans
      ((firstCarry_pointer e3).trans ((firstProducts_pointer e2).trans ptr1)))
  have pre5 : FirstTopPre (entry+281#64) s5 := by
    refine ⟨ip5, mem5, scratch_apart he mem5 281 48 (by decide), ?_⟩
    change MemReadable s5 ((Operand.mem (stackPtr s5+24#64) : Operand 64).read s5+8#64) 8
    rw [ptr5]
    exact P256.Proofs.Program.readable_of_grow (readable_limb pre.left 8 (by decide)) f12345.grow
  obtain ⟨n6, t, run6, ready6, _, e6⟩ := firstTop_correct (entry+281#64) boundary
    (next 281 48 (by decide)) s5 ready5
    (code_slice he loaded5 281 _ (by decide) firstTop_bytes) pre5
  have f6 := firstTop_frame e6
  exact ⟨_, t, ((((run1.trans run2).trans run3).trans run4).trans run5).trans run6,
    ready6, scratch_loaded mem5 f6 loaded5, Reduction.scratch_trans f12345 f6,
    ⟨⟨s1, s2, s3, s4, s5, e1, e2, e3, e4, e5, e6⟩⟩⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery
