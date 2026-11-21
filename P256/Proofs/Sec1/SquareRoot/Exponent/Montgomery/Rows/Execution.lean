import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Trace (entry : BitVec 64) (s t : RamState) where
  s1 : RamState
  s2 : RamState
  s3 : RamState
  s4 : RamState
  s5 : RamState
  s6 : RamState
  s7 : RamState
  s8 : RamState
  s9 : RamState
  s10 : RamState
  s11 : RamState
  e1 : (secondStartEffect (entry+329#64) s).Holds s s1
  e2 : (secondMiddleEffect (entry+425#64) s1).Holds s1 s2
  e3 : (secondHighEffect (entry+483#64) s2).Holds s2 s3
  e4 : (secondTopEffect (entry+530#64) s3).Holds s3 s4
  e5 : (thirdStartEffect (entry+592#64) s4).Holds s4 s5
  e6 : (thirdMiddleEffect (entry+686#64) s5).Holds s5 s6
  e7 : (thirdHighEffect (entry+744#64) s6).Holds s6 s7
  e8 : (thirdTopEffect (entry+786#64) s7).Holds s7 s8
  e9 : (fourthStartEffect (entry+847#64) s8).Holds s8 s9
  e10 : (fourthMiddleEffect (entry+943#64) s9).Holds s9 s10
  e11 : (fourthHighEffect (entry+1001#64) s10).Holds s10 s11
  e12 : (fourthTopEffect (entry+1040#64) s11).Holds s11 t

theorem execution [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {a b : Vector (BitVec 64) 4} {s : RamState} (pre : Pre entry boundary a b s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      AgreesExcept (Reduction.scratchComponents s) s t ∧ Nonempty (Trace entry s t) := by
  have next (offset size : Nat) (hb : offset+size < 1469) :
      ∀ n : Nat, 0 < n → n ≤ size →
        (entry+BitVec.ofNat 64 offset)+BitVec.ofNat 64 n ≠ boundary.rip := by
    intro n _ hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact instruction_ne_boundary pre.entryValid pre.boundaryOutside _ (by omega)
  have apart {u : RamState} (memory : Reduction.MemoryPre u)
      (offset size : Nat) (hb : offset+size ≤ 1469) :
      RangeApart (stackPtr u) 112 (entry+BitVec.ofNat 64 offset) size := by
    have h := memory.scratch_apart pre.entryValid 0 112 offset size (by decide) hb
    simpa only [BitVec.add_zero] using h
  have loaded_of {u v : RamState} (memory : Reduction.MemoryPre u)
      (ag : AgreesExcept (Reduction.scratchComponents u) u v) (hl : ProgramLoaded u) :
      ProgramLoaded v :=
    memory.loaded (ag.mono (by intro c hc; exact List.mem_append_left _ hc)) hl
  obtain ⟨n1, s1, run1, ready1, _, e1⟩ := secondStart_correct (entry+329#64) boundary
    (next 329 96 (by decide)) s pre.ready
    (code_slice pre.entryValid pre.loaded 329 _ (by decide) secondStart_bytes) ⟨pre.rip, pre.memory, apart pre.memory 329 96 (by decide)⟩
  have f1 := secondStart_frame e1
  have ag1 := f1
  have mem1 := pre.memory.of_scratch f1
  have loaded1 := loaded_of pre.memory f1 pre.loaded
  have ip1 : s1.RIP = entry+425#64 := by
    have h := e1.rip
    change _ = (entry+329#64)+96#64 at h
    simpa only [BitVec.add_assoc, show 329#64+96#64 = 425#64 by decide +kernel] using h
  have ptr1 := secondStart_pointer e1
  obtain ⟨n2, s2, run2, ready2, _, e2⟩ := secondMiddle_correct (entry+425#64) boundary
    (next 425 58 (by decide)) s1 ready1
    (code_slice pre.entryValid loaded1 425 _ (by decide) secondMiddle_bytes) ⟨ip1, mem1, apart mem1 425 58 (by decide)⟩
  have f2 := secondMiddle_frame e2
  have ag2 := scratch_trans ag1 f2
  have mem2 := mem1.of_scratch f2
  have loaded2 := loaded_of mem1 f2 loaded1
  have ip2 : s2.RIP = entry+483#64 := by
    have h := e2.rip
    change _ = (entry+425#64)+58#64 at h
    simpa only [BitVec.add_assoc, show 425#64+58#64 = 483#64 by decide +kernel] using h
  have ptr2 := (secondMiddle_pointer e2).trans ptr1
  obtain ⟨n3, s3, run3, ready3, _, e3⟩ := secondHigh_correct (entry+483#64) boundary
    (next 483 47 (by decide)) s2 ready2
    (code_slice pre.entryValid loaded2 483 _ (by decide) secondHigh_bytes) ⟨ip2, mem2, apart mem2 483 47 (by decide)⟩
  have f3 := secondHigh_frame e3
  have ag3 := scratch_trans ag2 f3
  have mem3 := mem2.of_scratch f3
  have loaded3 := loaded_of mem2 f3 loaded2
  have ip3 : s3.RIP = entry+530#64 := by
    have h := e3.rip
    change _ = (entry+483#64)+47#64 at h
    simpa only [BitVec.add_assoc, show 483#64+47#64 = 530#64 by decide +kernel] using h
  have ptr3 := (secondHigh_pointer e3).trans ptr2
  have topPre4 : TopPre (entry+530#64) 62 s3 := by
    refine ⟨⟨ip3, mem3, apart mem3 530 62 (by decide)⟩, ?_⟩
    change MemReadable s3 (savedPtr s3) 32
    rw [ptr3]
    exact P256.Proofs.Program.readable_of_grow pre.input ag3.grow
  obtain ⟨n4, s4, run4, ready4, _, e4⟩ := secondTop_correct (entry+530#64) boundary
    (next 530 62 (by decide)) s3 ready3
    (code_slice pre.entryValid loaded3 530 _ (by decide) secondTop_bytes) topPre4
  have f4 := secondTop_frame e4
  have ag4 := scratch_trans ag3 f4
  have mem4 := mem3.of_scratch f4
  have loaded4 := loaded_of mem3 f4 loaded3
  have ip4 : s4.RIP = entry+592#64 := by
    have h := e4.rip
    change _ = (entry+530#64)+62#64 at h
    simpa only [BitVec.add_assoc, show 530#64+62#64 = 592#64 by decide +kernel] using h
  have ptr4 := (secondTop_pointer e4).trans ptr3
  obtain ⟨n5, s5, run5, ready5, _, e5⟩ := thirdStart_correct (entry+592#64) boundary
    (next 592 94 (by decide)) s4 ready4
    (code_slice pre.entryValid loaded4 592 _ (by decide) thirdStart_bytes) ⟨ip4, mem4, apart mem4 592 94 (by decide)⟩
  have f5 := thirdStart_frame e5
  have ag5 := scratch_trans ag4 f5
  have mem5 := mem4.of_scratch f5
  have loaded5 := loaded_of mem4 f5 loaded4
  have ip5 : s5.RIP = entry+686#64 := by
    have h := e5.rip
    change _ = (entry+592#64)+94#64 at h
    simpa only [BitVec.add_assoc, show 592#64+94#64 = 686#64 by decide +kernel] using h
  have ptr5 := (thirdStart_pointer e5).trans ptr4
  obtain ⟨n6, s6, run6, ready6, _, e6⟩ := thirdMiddle_correct (entry+686#64) boundary
    (next 686 58 (by decide)) s5 ready5
    (code_slice pre.entryValid loaded5 686 _ (by decide) thirdMiddle_bytes) ⟨ip5, mem5, apart mem5 686 58 (by decide)⟩
  have f6 := thirdMiddle_frame e6
  have ag6 := scratch_trans ag5 f6
  have mem6 := mem5.of_scratch f6
  have loaded6 := loaded_of mem5 f6 loaded5
  have ip6 : s6.RIP = entry+744#64 := by
    have h := e6.rip
    change _ = (entry+686#64)+58#64 at h
    simpa only [BitVec.add_assoc, show 686#64+58#64 = 744#64 by decide +kernel] using h
  have ptr6 := (thirdMiddle_pointer e6).trans ptr5
  obtain ⟨n7, s7, run7, ready7, _, e7⟩ := thirdHigh_correct (entry+744#64) boundary
    (next 744 42 (by decide)) s6 ready6
    (code_slice pre.entryValid loaded6 744 _ (by decide) thirdHigh_bytes) ⟨ip6, mem6, apart mem6 744 42 (by decide)⟩
  have f7 := thirdHigh_frame e7
  have ag7 := scratch_trans ag6 f7
  have mem7 := mem6.of_scratch f7
  have loaded7 := loaded_of mem6 f7 loaded6
  have ip7 : s7.RIP = entry+786#64 := by
    have h := e7.rip
    change _ = (entry+744#64)+42#64 at h
    simpa only [BitVec.add_assoc, show 744#64+42#64 = 786#64 by decide +kernel] using h
  have ptr7 := (thirdHigh_pointer e7).trans ptr6
  have topPre8 : TopPre (entry+786#64) 61 s7 := by
    refine ⟨⟨ip7, mem7, apart mem7 786 61 (by decide)⟩, ?_⟩
    change MemReadable s7 (savedPtr s7) 32
    rw [ptr7]
    exact P256.Proofs.Program.readable_of_grow pre.input ag7.grow
  obtain ⟨n8, s8, run8, ready8, _, e8⟩ := thirdTop_correct (entry+786#64) boundary
    (next 786 61 (by decide)) s7 ready7
    (code_slice pre.entryValid loaded7 786 _ (by decide) thirdTop_bytes) topPre8
  have f8 := thirdTop_frame e8
  have ag8 := scratch_trans ag7 f8
  have mem8 := mem7.of_scratch f8
  have loaded8 := loaded_of mem7 f8 loaded7
  have ip8 : s8.RIP = entry+847#64 := by
    have h := e8.rip
    change _ = (entry+786#64)+61#64 at h
    simpa only [BitVec.add_assoc, show 786#64+61#64 = 847#64 by decide +kernel] using h
  obtain ⟨n9, s9, run9, ready9, _, e9⟩ := fourthStart_correct (entry+847#64) boundary
    (next 847 96 (by decide)) s8 ready8
    (code_slice pre.entryValid loaded8 847 _ (by decide) fourthStart_bytes) ⟨ip8, mem8, apart mem8 847 96 (by decide)⟩
  have f9 := fourthStart_frame e9
  have ag9 := scratch_trans ag8 f9
  have mem9 := mem8.of_scratch f9
  have loaded9 := loaded_of mem8 f9 loaded8
  have ip9 : s9.RIP = entry+943#64 := by
    have h := e9.rip
    change _ = (entry+847#64)+96#64 at h
    simpa only [BitVec.add_assoc, show 847#64+96#64 = 943#64 by decide +kernel] using h
  obtain ⟨n10, s10, run10, ready10, _, e10⟩ := fourthMiddle_correct (entry+943#64) boundary
    (next 943 58 (by decide)) s9 ready9
    (code_slice pre.entryValid loaded9 943 _ (by decide) fourthMiddle_bytes) ⟨ip9, mem9, apart mem9 943 58 (by decide)⟩
  have f10 := fourthMiddle_frame e10
  have ag10 := scratch_trans ag9 f10
  have mem10 := mem9.of_scratch f10
  have loaded10 := loaded_of mem9 f10 loaded9
  have ip10 : s10.RIP = entry+1001#64 := by
    have h := e10.rip
    change _ = (entry+943#64)+58#64 at h
    simpa only [BitVec.add_assoc, show 943#64+58#64 = 1001#64 by decide +kernel] using h
  obtain ⟨n11, s11, run11, ready11, _, e11⟩ := fourthHigh_correct (entry+1001#64) boundary
    (next 1001 39 (by decide)) s10 ready10
    (code_slice pre.entryValid loaded10 1001 _ (by decide) fourthHigh_bytes) ⟨ip10, mem10, apart mem10 1001 39 (by decide)⟩
  have f11 := fourthHigh_frame e11
  have ag11 := scratch_trans ag10 f11
  have mem11 := mem10.of_scratch f11
  have loaded11 := loaded_of mem10 f11 loaded10
  have ip11 : s11.RIP = entry+1040#64 := by
    have h := e11.rip
    change _ = (entry+1001#64)+39#64 at h
    simpa only [BitVec.add_assoc, show 1001#64+39#64 = 1040#64 by decide +kernel] using h
  obtain ⟨n12, t, run12, ready12, _, e12⟩ := fourthTop_correct (entry+1040#64) boundary
    (next 1040 32 (by decide)) s11 ready11
    (code_slice pre.entryValid loaded11 1040 _ (by decide) fourthTop_bytes) ⟨ip11, mem11, apart mem11 1040 32 (by decide)⟩
  have f12 := fourthTop_frame e12
  have ag12 := scratch_trans ag11 f12
  have mem12 := mem11.of_scratch f12
  have loaded12 := loaded_of mem11 f12 loaded11
  have ip12 : t.RIP = entry+1072#64 := by
    have h := e12.rip
    change _ = (entry+1040#64)+32#64 at h
    simpa only [BitVec.add_assoc, show 1040#64+32#64 = 1072#64 by decide +kernel] using h
  exact ⟨_, t, (((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12),
    ready12, loaded12, ag12, ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩⟩⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
