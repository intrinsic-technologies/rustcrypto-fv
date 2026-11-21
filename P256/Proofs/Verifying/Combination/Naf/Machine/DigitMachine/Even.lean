import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Memory
import P256.Proofs.Common.Instructions.CompareMemory.Register
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Instructions.StoreByte
import X86Proofs.Instructions.Inc.Generated.R.Triple
import P256.Proofs.Common.Instructions.Neg64

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Encoding.Parser.LengthCheck
open P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Neg64

set_option maxHeartbeats 600000 in
theorem even_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i c w : Nat}
    (pre : Pre s boundary) (state : BranchPre s t i c w) (rip : t.RIP = 0x10f43f) :
    ∃ fuel u, Advances boundary fuel t u ∧ BranchPost s t u (i+1) c i [0] := by
  have hi := state.indexBound
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset h)
  obtain ⟨a, ra, readyA, ea⟩ :=
    (cmp_m64_r64_effect_step 0x10f43f 0x4c (by simp [RexWPrefix]) 6
      (.sib 4 none 0 .none) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf43f _ (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable t ((Operand.reg 4 : Operand 64).read t+0#64) 8
        rw [BitVec.add_zero]
        change MemReadable t (stackPtr t) 8
        simpa only [BitVec.add_zero] using stack_readable pre.toCalleePre state.toFrameState (offset := 0) (len := 8) (by decide)⟩
      (next 0xf443 (by decide))
  have ga : AgreesExcept [.flags, .rip] t a := ea.agrees
  have fa := state.toFrameState.after_registers readyA ga (by simp [Component.Covers]) (by simp)
  have cfA : (StatusFlags.ofRFLAGS a.RFLAGS).CF = false := by
    have h := ea.flags.1
    change _ = decide ((memLoad t.external (stackPtr t+0#64) 64).toNat < (t.regValue .r14).toNat) at h
    rw [BitVec.add_zero] at h
    rw [state.rsp, state.outputLength, state.r14] at h
    rw [h]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64), BitVec.reduceToNat, decide_eq_false_iff_not]
    omega
  have zfA : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := ea.flags.2.2.2.1
    change _ = ((memLoad t.external (stackPtr t+0#64) 64 - t.regValue .r14) == 0) at h
    rw [BitVec.add_zero] at h
    rw [state.rsp, state.outputLength, state.r14] at h
    rw [h]
    have ne : (257 : BitVec 64) ≠ BitVec.ofNat 64 i := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
      omega
    simpa [BitVec.sub_eq_iff_eq_add] using ne
  obtain ⟨b, rb, readyB, _, ripB, gb⟩ := Iterator.Advance.branch32 (offset := 0xf443) 6 0xd1 false
    readyA fa.loaded ea.rip (by simp [condHolds, cfA, zfA]) (by decide) (by decide +kernel)
    (by decide +kernel) (next 0xf449 (by decide))
  have fb := fa.after_registers readyB gb (by simp [Component.Covers]) (by simp)
  have ab := ga.trans gb
  have rsiB : b.regValue .rsi = s.regValue .rdi :=
    (ab.read (n := 64) (r := 6) (by simp)).trans state.rsi
  have r14B : b.regValue .r14 = BitVec.ofNat 64 i :=
    (ab.read (n := 64) (r := 14) (by simp)).trans state.r14
  have addrB : (AddrMode.sib 6 (some 14) 0 .none).addr b 0x10f44e =
      s.regValue .rdi + BitVec.ofNat 64 i := by
    change b.regValue .rsi + (b.regValue .r14 <<< 0) + 0#64 = _
    rw [BitVec.shiftLeft_zero, BitVec.add_zero]
    rw [rsiB, r14B]
  obtain ⟨d, rd, readyD, ed⟩ :=
    (P256.Proofs.Common.Instructions.mov_m8_imm8_rex_effect_step 0x10f449 0x42 (by simp [RexNoWPrefix])
      (.sib 6 (some 14) 0 .none) (by decide) rfl rfl 0).advances readyB
      (programText_slice (programLoaded_codeIn fb.loaded) 0xf449 _ (by decide) (by decide +kernel))
      ⟨ripB, by change MemWritable b ((AddrMode.sib 6 (some 14) 0 .none).addr b 0x10f44e) 1
                rw [addrB]
                exact output_writable pre fb (by omega),
        by change RangeApart ((AddrMode.sib 6 (some 14) 0 .none).addr b 0x10f44e) 1 _ 5
           rw [addrB]
           exact output_code pre (by omega) (by decide : 0xf449+5 ≤ 118431)⟩
      (next 0xf44e (by decide))
  have gd : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 i) 1, .rip] b d := by
    have he := ed.agrees
    simp only [P256.Proofs.Common.Instructions.movM8Imm8RexEffect, storeEffect_components] at he
    change AgreesExcept [.mem ((AddrMode.sib 6 (some 14) 0 .none).addr b 0x10f44e) 1, .rip] b d at he
    rwa [addrB] at he
  obtain ⟨fd, md⟩ := output_after pre fb (i := i) (len := 1) (by omega) readyD gd
    (by intro comp hc a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ha
        · exact ha.elim) (by simp)
  obtain ⟨e, re, readyE, ee⟩ :=
    (inc_r64_effect_step 0x10f44e 0x49 0xc6 (by simp [RexWPrefix]) rfl rfl).advances readyD
      (programText_slice (programLoaded_codeIn fd.loaded) 0xf44e _ (by decide) (by decide +kernel))
      ed.rip (next 0xf451 (by decide))
  have ge : AgreesExcept [.reg 14, .flags, .rip] d e := ee.agrees
  have fe := fd.after_registers readyE ge (by simp [Component.Covers]) (by simp)
  obtain ⟨f, rf, readyF, ef⟩ :=
    (inc_r64_effect_step 0x10f451 0x49 0xc7 (by simp [RexWPrefix]) rfl rfl).advances readyE
      (programText_slice (programLoaded_codeIn fe.loaded) 0xf451 _ (by decide) (by decide +kernel))
      ee.rip (next 0xf454 (by decide))
  have gf : AgreesExcept [.reg 15, .flags, .rip] e f := ef.agrees
  have ff := fe.after_registers readyF gf (by simp [Component.Covers]) (by simp)
  have r14E : e.regValue .r14 = BitVec.ofNat 64 (i+1) := by
    have h := ee.writes
    change e.regValue .r14 = d.regValue .r14 + 1 at h
    have he : d.regValue .r14 = b.regValue .r14 := gd.read (n := 64) (r := 14) (by simp)
    rw [he, r14B] at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using h
  have r15F : f.regValue .r15 = BitVec.ofNat 64 (i+1) := by
    have h := ef.writes
    change f.regValue .r15 = e.regValue .r15 + 1 at h
    have he : e.regValue .r15 = BitVec.ofNat 64 i :=
      (((ab.trans gd).trans ge).read (n := 64) (r := 15) (by simp)).trans state.r15
    rw [he] at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨g, rg, readyG, eg⟩ :=
    (mov_r64_r64_effect_step 0x10f454 0x4c 0xfd (by simp [RexWPrefix]) rfl).advances readyF
      (programText_slice (programLoaded_codeIn ff.loaded) 0xf454 _ (by decide) (by decide +kernel))
      ef.rip (next 0xf457 (by decide))
  have gg : AgreesExcept [.reg 5, .rip] f g := eg.agrees
  have fg := ff.after_registers readyG gg (by simp [Component.Covers]) (by simp)
  obtain ⟨h, rh, readyH, eh⟩ :=
    (neg_r64_effect_step 0x10f457 0x48 0xdd (by simp [RexWPrefix]) rfl rfl).advances readyG
      (programText_slice (programLoaded_codeIn fg.loaded) 0xf457 _ (by decide) (by decide +kernel))
      eg.rip (next 0xf45a (by decide))
  have gh : AgreesExcept [.reg 5, .flags, .rip] g h := eh.agrees
  have fh := fg.after_registers readyH gh (by simp [Component.Covers]) (by simp)
  have bpH : h.regValue .rbp = -BitVec.ofNat 64 (i+1) := by
    have hp : g.regValue .rbp = f.regValue .r15 := eg.writes
    have hq : h.regValue .rbp = -g.regValue .rbp := eh.writes
    rw [hq, hp, r15F]
  have r15H : h.regValue .r15 = BitVec.ofNat 64 (i+1) :=
    ((gg.trans gh).read (n := 64) (r := 15) (by simp)).trans r15F
  have memoryH : h.external = d.external :=
    (((ge.trans gf).trans gg).trans gh).external (by simp [Component.Covers])
  have bitsH : memLoad h.external (stackPtr h+24) 64 = 256 := by
    have addr : stackPtr h+24 = stackPtr s-112 := by
      simpa only [BitVec.ofNat_eq_ofNat] using stack_address fh.rsp (offset := 24) (by decide)
    rw [addr, memoryH]
    apply Eq.trans _ state.bits
    apply memLoad_congr
    intro j hj
    change (d.external[stackPtr s-112+BitVec.ofNat 64 j]?).getD 0 =
      (t.external[stackPtr s-112+BitVec.ofNat 64 j]?).getD 0
    rw [md _]
    · rw [ab.external (by simp [Component.Covers])]
    · intro region hr hin
      have hr' : region = digitRegion s i 1 := by simpa using hr
      subst region
      apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
        (stackPtr s-112+BitVec.ofNat 64 j).toNat
      · have low : (s.regValue .rdi).toNat+257 < 2^32 := pre.outputBounded
        change (s.regValue .rdi+BitVec.ofNat 64 i).toNat ≤ _ ∧
          _ < (s.regValue .rdi+BitVec.ofNat 64 i).toNat+1 at hin
        rw [toNat_add_ofNat _ _ (by omega)] at hin
        change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat+257
        omega
      · exact ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide)
          (show (Component.mem (stackPtr s-112) 8).Covers _ from ⟨j, hj, rfl⟩)
  obtain ⟨v, rv, readyV, ev⟩ :=
    (cmp_r64_m64_effect_step 0x10f45a 0x4c (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances readyH
      (programText_slice (programLoaded_codeIn fh.loaded) 0xf45a _ (by decide) (by decide +kernel))
      ⟨eh.rip, stack_readable pre.toCalleePre fh (by decide : 24+8 ≤ 136)⟩
      (next 0xf45f (by decide))
  have gv : AgreesExcept [.flags, .rip] h v := ev.agrees
  have fv := fh.after_registers readyV gv (by simp [Component.Covers]) (by simp)
  have cfV : (StatusFlags.ofRFLAGS v.RFLAGS).CF = decide (i+1 < 256) := by
    have he := ev.flags.1
    change _ = decide ((h.regValue .r15).toNat < (memLoad h.external (stackPtr h+24) 64).toNat) at he
    simpa only [r15H, bitsH, BitVec.lt_def, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i+1 < 2^64), BitVec.reduceToNat] using he
  obtain ⟨z, rz, readyZ, _, ripZ, gz⟩ := Iterator.Advance.branch8 (offset := 0xf45f) 2 0x86
    (decide (i+1 < 256)) readyV fv.loaded ev.rip (by simp [condHolds, cfV]) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by split <;> first | exact next 0xf3e7 (by decide) | exact next 0xf461 (by decide))
  have fz := fv.after_registers readyZ gz (by simp [Component.Covers]) (by simp)
  have finish : ∃ fuel u, Advances boundary fuel z u ∧ FrameState s u ∧
      u.RIP = (if i+1 < 256 then 0x10f3e7 else 0x10f4da) ∧ AgreesExcept [.rip] z u := by
    by_cases lt : i+1 < 256
    · exact ⟨0, z, by rfl, fz, by simpa [lt, branchTarget, Extracted.textAddress] using ripZ,
        AgreesExcept.refl _ _⟩
    · obtain ⟨u, ru, readyU, eu⟩ := (jmp_rel8_effect_step 0x10f461 0x77 (by decide +kernel)).advances
        readyZ (programText_slice (programLoaded_codeIn fz.loaded) 0xf461 _ (by decide) (by decide +kernel))
        (by simpa [lt, branchTarget, Extracted.textAddress] using ripZ) (next 0xf4da (by decide))
      have gu : AgreesExcept [.rip] z u := eu.agrees
      exact ⟨1, u, ru, fz.after_registers readyU gu (by simp [Component.Covers]) (by simp),
        by simpa [lt, jmpEffect, branchTarget] using eu.rip, gu⟩
  obtain ⟨fuel, u, run, frame, ip, gu⟩ := finish
  have last := ((((ge.trans gf).trans gg).trans gh).trans gv).trans gz |>.trans gu
  have full := ((ab.trans gd).trans last)
  refine ⟨_, u, ((((((((ra.trans rb).trans rd).trans re).trans rf).trans rg).trans rh).trans rv).trans rz).trans run,
    ⟨frame, ip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (full.read (n := 64) (r := 12) (by simp)).trans state.r12
  · exact (full.read (n := 64) (r := 13) (by simp)).trans state.r13
  · exact ((((((gf.trans gg).trans gh).trans gv).trans gz).trans gu).read
      (n := 64) (r := 14) (by simp)).trans r14E
  · exact (((((gg.trans gh).trans gv).trans gz).trans gu).read
      (n := 64) (r := 15) (by simp)).trans r15F
  · exact (((gv.trans gz).trans gu).read (n := 64) (r := 5) (by simp)).trans bpH
  · have value : memLoad d.external (s.regValue .rdi+BitVec.ofNat 64 i) 8 = 0 := by
      have he := ed.writes
      change memLoad d.external ((AddrMode.sib 6 (some 14) 0 .none).addr b 0x10f44e) 8 = 0 at he
      rwa [addrB] at he
    have bytes := Bytes.of_memLoad (n := 8) (output_readable pre fd (i := i) (len := 1) (by omega)).mem
    change Bytes d.external (s.regValue .rdi+BitVec.ofNat 64 i) 1 (storedByte (memLoad d.external _ 8)) at bytes
    rw [value] at bytes
    intro j hj
    have eq : j = 0 := by simpa using hj
    subst j
    rw [last.external (by simp [Component.Covers])]
    change d.external[s.regValue .rdi+BitVec.ofNat 64 i+BitVec.ofNat 64 0]? = some 0
    exact bytes 0 (by decide)
  · intro a ha
    rw [last.external (by simp [Component.Covers]), md a ha,
      ab.external (by simp [Component.Covers])]

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
