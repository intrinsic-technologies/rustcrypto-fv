import P256.Proofs.EcdhWrapper.Finish.Copy.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem copy_words [Bindings] {initial s0 : RamState} {secret peer : ByteArray}
    {slices : Array Input} (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip) (ready0 : ReadyToStep s0)
    (loaded0 : ProgramLoaded s0)
    (grow0 : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s0.external[a]?).isSome)
    (sp0 : stackPtr s0=stackPtr initial-504) (rip : s0.RIP=0x106be4)
    (saved : memLoad s0.external (stackPtr initial-472) 64=initial.regValue .rcx) :
    ∃ t, Advances (returnBoundary initial) 9 s0 t ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ t.RIP=0x106c0c ∧ t.regValue .rcx=initial.regValue .rcx ∧
      t.regValue .r8=s0.regValue .r8 ∧
      AgreesExcept (components initial) s0 t ∧
      (∀ j<4, memLoad t.external (initial.regValue .rcx+8+BitVec.ofNat 64 (8*j)) 64=
        memLoad s0.external (stackPtr initial-504+BitVec.ofNat 64 (8*j)) 64) := by
  obtain ⟨s1,a1,ready1,e1⟩ := (mov_r64_m64_effect_step 0x106be4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances ready0
    (programText_slice (programLoaded_codeIn loaded0) 0x6be4 _ (by decide) (by decide +kernel))
    ⟨rip,by change MemReadable s0 (stackPtr s0+BitVec.ofNat 64 24) 8; exact Peer.Buffer.readable call grow0 sp0 (off := 24) (len := 8) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6be9 (by decide)))
  have g1 : AgreesExcept [.reg 0,.rip] s0 s1 := e1.agrees
  have wide1 : AgreesExcept (components initial) s0 s1 := g1.mono (by simp [components])
  have v1 : s1.regValue .rax=memLoad s0.external (stackPtr initial-BitVec.ofNat 64 480) 64 := by
    have h : s1.regValue .rax=memLoad s0.external (stackPtr s0+24) 64 := e1.writes
    rw [h]
    change memLoad s0.external (stackPtr s0+BitVec.ofNat 64 24) 64=_
    rw [Peer.Buffer.address sp0 (off := 24) (by decide)]
  have sp1 : stackPtr s1=stackPtr initial-504 := (g1.read (n := 64) (r := 4) (by simp)).trans sp0
  have loaded1 := loaded_after call loaded0 wide1
  have grow1 := fun a h ↦ g1.grow a (grow0 a h)
  have total1 : AgreesExcept (components initial) s0 s1 := wide1
  obtain ⟨s2,a2,ready2,e2⟩ := (mov_r64_m64_effect_step 0x106be9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances ready1
    (programText_slice (programLoaded_codeIn loaded1) 0x6be9 _ (by decide) (by decide +kernel))
    ⟨e1.rip,by change MemReadable s1 (stackPtr s1+BitVec.ofNat 64 32) 8; exact Peer.Buffer.readable call grow1 sp1 (off := 32) (len := 8) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bee (by decide)))
  have g2 : AgreesExcept [.reg 1,.rip] s1 s2 := e2.agrees
  have wide2 : AgreesExcept (components initial) s1 s2 := g2.mono (by simp [components])
  have v2 : s2.regValue .rcx=memLoad s0.external (stackPtr initial-BitVec.ofNat 64 472) 64 := by
    have h : s2.regValue .rcx=memLoad s1.external (stackPtr s1+32) 64 := e2.writes
    rw [h]
    change memLoad s1.external (stackPtr s1+BitVec.ofNat 64 32) 64=_
    rw [Peer.Buffer.address sp1 (off := 32) (by decide)]
    exact stack_read call total1 (by decide) (by decide)
  have sp2 : stackPtr s2=stackPtr initial-504 := (g2.read (n := 64) (r := 4) (by simp)).trans sp1
  have loaded2 := loaded_after call loaded1 wide2
  have grow2 := fun a h ↦ g2.grow a (grow1 a h)
  have cx2 : s2.regValue .rcx=initial.regValue .rcx := v2.trans saved
  have total2 : AgreesExcept (components initial) s0 s2 := (total1.trans wide2).mono (by simp)
  obtain ⟨s3,a3,ready3,e3⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106bee 0x48 (by simp [RexWPrefix]) 0 (.base 1 (.d8 32)) (by decide) rfl rfl).advances ready2
    (programText_slice (programLoaded_codeIn loaded2) 0x6bee _ (by decide) (by decide +kernel))
    ⟨e2.rip,by change CrossPageStore.Writable s2 (s2.regValue .rcx+32) 8; rw [cx2]; exact (output_writable call grow2).add 32 (by decide),
      by change RangeApart (s2.regValue .rcx+32) 8 0x106bee 4; rw [cx2]; exact output_code call (off := 32) (len := 8) (pc := 0x6bee) (n := 4) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bf2 (by decide)))
  have g3 : AgreesExcept [.mem (initial.regValue .rcx+32) 8,.rip] s2 s3 := by
    have h := e3.agrees
    x86_norm [movM64R64Effect,storeAddrAt,cx2] at h ⊢
    change AgreesExcept [.mem (s2.regValue .rcx+32) 8,.rip] s2 s3 at h
    rw [cx2] at h
    exact h
  have wide3 := store_agrees (off := 32) (by decide) g3
  have value3 : memLoad s3.external (initial.regValue .rcx+32) 64=memLoad s0.external (stackPtr initial-480) 64 := by
    have h : memLoad s3.external (s2.regValue .rcx+32) 64=s2.regValue .rax := e3.writes
    rw [cx2] at h
    rw [h]
    exact (g2.read (n := 64) (r := 0) (by simp)).trans v1
  have sp3 : stackPtr s3=stackPtr initial-504 := (g3.read (n := 64) (r := 4) (by simp)).trans sp2
  have loaded3 := loaded_after call loaded2 wide3
  have grow3 := fun a h ↦ g3.grow a (grow2 a h)
  have cx3 : s3.regValue .rcx=initial.regValue .rcx := (g3.read (n := 64) (r := 1) (by simp)).trans cx2
  have total3 : AgreesExcept (components initial) s0 s3 := (total2.trans wide3).mono (by simp)
  obtain ⟨s4,a4,ready4,e4⟩ := (mov_r64_m64_effect_step 0x106bf2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances ready3
    (programText_slice (programLoaded_codeIn loaded3) 0x6bf2 _ (by decide) (by decide +kernel))
    ⟨e3.rip,by change MemReadable s3 (stackPtr s3+BitVec.ofNat 64 16) 8; exact Peer.Buffer.readable call grow3 sp3 (off := 16) (len := 8) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bf7 (by decide)))
  have g4 : AgreesExcept [.reg 0,.rip] s3 s4 := e4.agrees
  have wide4 : AgreesExcept (components initial) s3 s4 := g4.mono (by simp [components])
  have v4 : s4.regValue .rax=memLoad s0.external (stackPtr initial-BitVec.ofNat 64 488) 64 := by
    have h : s4.regValue .rax=memLoad s3.external (stackPtr s3+16) 64 := e4.writes
    rw [h]
    change memLoad s3.external (stackPtr s3+BitVec.ofNat 64 16) 64=_
    rw [Peer.Buffer.address sp3 (off := 16) (by decide)]
    exact stack_read call total3 (by decide) (by decide)
  have sp4 : stackPtr s4=stackPtr initial-504 := (g4.read (n := 64) (r := 4) (by simp)).trans sp3
  have loaded4 := loaded_after call loaded3 wide4
  have grow4 := fun a h ↦ g4.grow a (grow3 a h)
  have cx4 : s4.regValue .rcx=initial.regValue .rcx := (g4.read (n := 64) (r := 1) (by simp)).trans cx3
  have total4 : AgreesExcept (components initial) s0 s4 := (total3.trans wide4).mono (by simp)
  obtain ⟨s5,a5,ready5,e5⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106bf7 0x48 (by simp [RexWPrefix]) 0 (.base 1 (.d8 24)) (by decide) rfl rfl).advances ready4
    (programText_slice (programLoaded_codeIn loaded4) 0x6bf7 _ (by decide) (by decide +kernel))
    ⟨e4.rip,by change CrossPageStore.Writable s4 (s4.regValue .rcx+24) 8; rw [cx4]; exact (output_writable call grow4).add 24 (by decide),
      by change RangeApart (s4.regValue .rcx+24) 8 0x106bf7 4; rw [cx4]; exact output_code call (off := 24) (len := 8) (pc := 0x6bf7) (n := 4) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bfb (by decide)))
  have g5 : AgreesExcept [.mem (initial.regValue .rcx+24) 8,.rip] s4 s5 := by
    have h := e5.agrees
    x86_norm [movM64R64Effect,storeAddrAt,cx4] at h ⊢
    change AgreesExcept [.mem (s4.regValue .rcx+24) 8,.rip] s4 s5 at h
    rw [cx4] at h
    exact h
  have wide5 := store_agrees (off := 24) (by decide) g5
  have value5 : memLoad s5.external (initial.regValue .rcx+24) 64=memLoad s0.external (stackPtr initial-488) 64 := by
    have h : memLoad s5.external (s4.regValue .rcx+24) 64=s4.regValue .rax := e5.writes
    rw [cx4] at h
    rw [h]
    exact v4
  have sp5 : stackPtr s5=stackPtr initial-504 := (g5.read (n := 64) (r := 4) (by simp)).trans sp4
  have loaded5 := loaded_after call loaded4 wide5
  have grow5 := fun a h ↦ g5.grow a (grow4 a h)
  have cx5 : s5.regValue .rcx=initial.regValue .rcx := (g5.read (n := 64) (r := 1) (by simp)).trans cx4
  have total5 : AgreesExcept (components initial) s0 s5 := (total4.trans wide5).mono (by simp)
  obtain ⟨s6,a6,ready6,e6⟩ := (mov_r64_m64_effect_step 0x106bfb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready5
    (programText_slice (programLoaded_codeIn loaded5) 0x6bfb _ (by decide) (by decide +kernel))
    ⟨e5.rip,by change MemReadable s5 (stackPtr s5+BitVec.ofNat 64 0) 8; exact Peer.Buffer.readable call grow5 sp5 (off := 0) (len := 8) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bff (by decide)))
  have g6 : AgreesExcept [.reg 0,.rip] s5 s6 := e6.agrees
  have wide6 : AgreesExcept (components initial) s5 s6 := g6.mono (by simp [components])
  have v6 : s6.regValue .rax=memLoad s0.external (stackPtr initial-BitVec.ofNat 64 504) 64 := by
    have h : s6.regValue .rax=memLoad s5.external (stackPtr s5+0) 64 := e6.writes
    rw [h]
    change memLoad s5.external (stackPtr s5+BitVec.ofNat 64 0) 64=_
    rw [Peer.Buffer.address sp5 (off := 0) (by decide)]
    exact stack_read call total5 (by decide) (by decide)
  have sp6 : stackPtr s6=stackPtr initial-504 := (g6.read (n := 64) (r := 4) (by simp)).trans sp5
  have loaded6 := loaded_after call loaded5 wide6
  have grow6 := fun a h ↦ g6.grow a (grow5 a h)
  have cx6 : s6.regValue .rcx=initial.regValue .rcx := (g6.read (n := 64) (r := 1) (by simp)).trans cx5
  have total6 : AgreesExcept (components initial) s0 s6 := (total5.trans wide6).mono (by simp)
  obtain ⟨s7,a7,ready7,e7⟩ := (mov_r64_m64_effect_step 0x106bff 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances ready6
    (programText_slice (programLoaded_codeIn loaded6) 0x6bff _ (by decide) (by decide +kernel))
    ⟨e6.rip,by change MemReadable s6 (stackPtr s6+BitVec.ofNat 64 8) 8; exact Peer.Buffer.readable call grow6 sp6 (off := 8) (len := 8) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6c04 (by decide)))
  have g7 : AgreesExcept [.reg 2,.rip] s6 s7 := e7.agrees
  have wide7 : AgreesExcept (components initial) s6 s7 := g7.mono (by simp [components])
  have v7 : s7.regValue .rdx=memLoad s0.external (stackPtr initial-BitVec.ofNat 64 496) 64 := by
    have h : s7.regValue .rdx=memLoad s6.external (stackPtr s6+8) 64 := e7.writes
    rw [h]
    change memLoad s6.external (stackPtr s6+BitVec.ofNat 64 8) 64=_
    rw [Peer.Buffer.address sp6 (off := 8) (by decide)]
    exact stack_read call total6 (by decide) (by decide)
  have sp7 : stackPtr s7=stackPtr initial-504 := (g7.read (n := 64) (r := 4) (by simp)).trans sp6
  have loaded7 := loaded_after call loaded6 wide7
  have grow7 := fun a h ↦ g7.grow a (grow6 a h)
  have cx7 : s7.regValue .rcx=initial.regValue .rcx := (g7.read (n := 64) (r := 1) (by simp)).trans cx6
  have total7 : AgreesExcept (components initial) s0 s7 := (total6.trans wide7).mono (by simp)
  obtain ⟨s8,a8,ready8,e8⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106c04 0x48 (by simp [RexWPrefix]) 2 (.base 1 (.d8 16)) (by decide) rfl rfl).advances ready7
    (programText_slice (programLoaded_codeIn loaded7) 0x6c04 _ (by decide) (by decide +kernel))
    ⟨e7.rip,by change CrossPageStore.Writable s7 (s7.regValue .rcx+16) 8; rw [cx7]; exact (output_writable call grow7).add 16 (by decide),
      by change RangeApart (s7.regValue .rcx+16) 8 0x106c04 4; rw [cx7]; exact output_code call (off := 16) (len := 8) (pc := 0x6c04) (n := 4) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6c08 (by decide)))
  have g8 : AgreesExcept [.mem (initial.regValue .rcx+16) 8,.rip] s7 s8 := by
    have h := e8.agrees
    x86_norm [movM64R64Effect,storeAddrAt,cx7] at h ⊢
    change AgreesExcept [.mem (s7.regValue .rcx+16) 8,.rip] s7 s8 at h
    rw [cx7] at h
    exact h
  have wide8 := store_agrees (off := 16) (by decide) g8
  have value8 : memLoad s8.external (initial.regValue .rcx+16) 64=memLoad s0.external (stackPtr initial-496) 64 := by
    have h : memLoad s8.external (s7.regValue .rcx+16) 64=s7.regValue .rdx := e8.writes
    rw [cx7] at h
    rw [h]
    exact v7
  have sp8 : stackPtr s8=stackPtr initial-504 := (g8.read (n := 64) (r := 4) (by simp)).trans sp7
  have loaded8 := loaded_after call loaded7 wide8
  have grow8 := fun a h ↦ g8.grow a (grow7 a h)
  have cx8 : s8.regValue .rcx=initial.regValue .rcx := (g8.read (n := 64) (r := 1) (by simp)).trans cx7
  have total8 : AgreesExcept (components initial) s0 s8 := (total7.trans wide8).mono (by simp)
  obtain ⟨s9,a9,ready9,e9⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106c08 0x48 (by simp [RexWPrefix]) 0 (.base 1 (.d8 8)) (by decide) rfl rfl).advances ready8
    (programText_slice (programLoaded_codeIn loaded8) 0x6c08 _ (by decide) (by decide +kernel))
    ⟨e8.rip,by change CrossPageStore.Writable s8 (s8.regValue .rcx+8) 8; rw [cx8]; exact (output_writable call grow8).add 8 (by decide),
      by change RangeApart (s8.regValue .rcx+8) 8 0x106c08 4; rw [cx8]; exact output_code call (off := 8) (len := 8) (pc := 0x6c08) (n := 4) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6c0c (by decide)))
  have g9 : AgreesExcept [.mem (initial.regValue .rcx+8) 8,.rip] s8 s9 := by
    have h := e9.agrees
    x86_norm [movM64R64Effect,storeAddrAt,cx8] at h ⊢
    change AgreesExcept [.mem (s8.regValue .rcx+8) 8,.rip] s8 s9 at h
    rw [cx8] at h
    exact h
  have wide9 := store_agrees (off := 8) (by decide) g9
  have value9 : memLoad s9.external (initial.regValue .rcx+8) 64=memLoad s0.external (stackPtr initial-504) 64 := by
    have h : memLoad s9.external (s8.regValue .rcx+8) 64=s8.regValue .rax := e9.writes
    rw [cx8] at h
    rw [h]
    exact ((g7.trans g8).read (n := 64) (r := 0) (by simp)).trans v6
  have sp9 : stackPtr s9=stackPtr initial-504 := (g9.read (n := 64) (r := 4) (by simp)).trans sp8
  have loaded9 := loaded_after call loaded8 wide9
  have grow9 := fun a h ↦ g9.grow a (grow8 a h)
  have cx9 : s9.regValue .rcx=initial.regValue .rcx := (g9.read (n := 64) (r := 1) (by simp)).trans cx8
  have total9 : AgreesExcept (components initial) s0 s9 := (total8.trans wide9).mono (by simp)
  have last3 : memLoad s9.external (initial.regValue .rcx+32) 64=memLoad s3.external (initial.regValue .rcx+32) 64 := by
    apply memLoad_agrees_apart (((((g4.trans g5).trans g6).trans g7).trans g8).trans g9)
    intro a len hm
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or,Component.mem.injEq,reduceCtorEq] at hm
    rcases hm with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨rfl,rfl⟩
    · exact offsets_apart (a := 24) (b := 32) (by decide) (by decide) (by decide)
    · exact offsets_apart (a := 16) (b := 32) (by decide) (by decide) (by decide)
    · exact offsets_apart (a := 8) (b := 32) (by decide) (by decide) (by decide)
  have last5 : memLoad s9.external (initial.regValue .rcx+24) 64=memLoad s5.external (initial.regValue .rcx+24) 64 := by
    apply memLoad_agrees_apart (((g6.trans g7).trans g8).trans g9)
    intro a len hm
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or,Component.mem.injEq,reduceCtorEq] at hm
    rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact offsets_apart (a := 16) (b := 24) (by decide) (by decide) (by decide)
    · exact offsets_apart (a := 8) (b := 24) (by decide) (by decide) (by decide)
  have last8 : memLoad s9.external (initial.regValue .rcx+16) 64=memLoad s8.external (initial.regValue .rcx+16) 64 := by
    apply memLoad_agrees_apart g9
    intro a len hm
    simp only [List.mem_cons,List.not_mem_nil,or_false,Component.mem.injEq,reduceCtorEq] at hm
    rcases hm with ⟨rfl,rfl⟩
    exact offsets_apart (a := 8) (b := 16) (by decide) (by decide) (by decide)
  refine ⟨s9,((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9),ready9,loaded9,e9.rip,cx9,(((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 8) (by simp)),total9,?_⟩
  intro j hj
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · have h := value9
    simpa only [Nat.reduceMul,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · have h := last8.trans value8
    simpa only [Nat.reduceMul,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · have h := last5.trans value5
    simpa only [Nat.reduceMul,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · have h := last3.trans value3
    simpa only [Nat.reduceMul,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h

end P256.Proofs.EcdhWrapper.Finish.Copy
