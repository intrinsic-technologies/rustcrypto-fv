import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

set_option maxHeartbeats 1600000 in
theorem guard [Bindings] {s : RamState} {boundary : ReturnBoundary} {k q : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = 0x1181b4)
    (readable : MemReadable s (s.regValue .rdi + 16) 8)
    (index : memLoad s.external (s.regValue .rdi + 16) 64 = BitVec.ofNat 64 k)
    (requested : s.regValue .rsi = BitVec.ofNat 64 q)
    (step : q = k ∨ q = k+1) (bound : q < 4) (outer : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if q = k then 0x11822c else 0x1181cf) ∧
      t.regValue .rax = BitVec.ofNat 64 (k+1) ∧
      AgreesExcept [.reg 0, .reg 1, .flags, .rip] s t := by
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := load64 (offset := 0x181b4) 1 (.base 7 (.d8 16))
    (by decide +kernel) rfl rfl ready loaded rip readable
    (by decide) (by decide +kernel) outer
  have ax : a.regValue .rcx = BitVec.ofNat 64 k := effectA.writes.trans index
  have agA : AgreesExcept [.reg 1, .rip] s a := effectA.agrees
  obtain ⟨b, runB, readyB, loadedB, effectB⟩ := step_nomem (offset := 0x181b8)
    (lea_r64_effect_step 0x1181b8 0x48 (by simp [RexWPrefix]) 0
      (.base 1 (.d8 1)) (by decide +kernel) rfl rfl)
    readyA loadedA effectA.rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x181bc (by decide)))
    (by simp [Component.Covers])
  change (leaR64Effect 0x1181b8 0 (.base 1 (.d8 1)) a).Holds a b at effectB
  have bx : b.regValue .rax = BitVec.ofNat 64 (k+1) := by
    have h := effectB.writes
    change b.regValue .rax = a.regValue .rcx + 1 at h
    rw [h, ax, BitVec.ofNat_add]
    rfl
  have agB : AgreesExcept [.reg 0, .reg 1, .rip] s b :=
    (agA.trans effectB.agrees).mono (by simp)
  have bcx : b.regValue .rcx = BitVec.ofNat 64 k :=
    (effectB.agrees.read (n := 64) (r := 1) (by simp)).trans ax
  have bsi : b.regValue .rsi = BitVec.ofNat 64 q :=
    (agB.read (n := 64) (r := 6) (by simp)).trans requested
  obtain ⟨c, runC, readyC, loadedC, effectC⟩ := step_nomem (offset := 0x181bc)
    (cmp_r64_r64_effect_step 0x1181bc 0x48 0xf1 (by simp [RexWPrefix]) rfl)
    readyB loadedB effectB.rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x181bf (by decide)))
    (by simp [Component.Covers])
  have agC : AgreesExcept [.reg 0, .reg 1, .flags, .rip] s c :=
    (agB.trans effectC.agrees).mono (by simp)
  have zfC : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = decide (q = k) := by
    have h := effectC.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((b.regValue .rcx - b.regValue .rsi) == 0) at h
    rw [h, bcx, bsi]
    have hk : k < 4 := by omega
    have he : (BitVec.ofNat 64 k = BitVec.ofNat 64 q) ↔ q = k := by
      constructor
      · intro hh
        have := congrArg BitVec.toNat hh
        simp only [BitVec.toNat_ofNat] at this
        omega
      · rintro rfl; rfl
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.sub_eq_iff_eq_add, he]
  obtain ⟨d, runD, readyD, loadedD, ripD, agD⟩ := branch8 (offset := 0x181bf) 4 9 (decide (q=k))
    readyC loadedC effectC.rip zfC (by decide) (by decide +kernel) (by decide +kernel) (by
      by_cases he : q = k
      · simpa [he, branchTarget, Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0x181ca (by decide))
      · simpa [he, branchTarget, Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0x181c1 (by decide)))
  have frameD : AgreesExcept [.reg 0, .reg 1, .flags, .rip] s d :=
    (agC.trans agD).mono (by simp)
  have dx : d.regValue .rax = BitVec.ofNat 64 (k+1) :=
    ((effectC.agrees.trans agD).read (n := 64) (r := 0) (by simp)).trans bx
  have join : ∃ fuel e, Advances boundary fuel s e ∧ ReadyToStep e ∧ ProgramLoaded e ∧
      e.RIP = 0x1181ca ∧ e.regValue .rax = BitVec.ofNat 64 (k+1) ∧
      e.regValue .rcx = BitVec.ofNat 64 k ∧ e.regValue .rsi = BitVec.ofNat 64 q ∧
      AgreesExcept [.reg 0, .reg 1, .flags, .rip] s e := by
    have dcx : d.regValue .rcx = BitVec.ofNat 64 k :=
      ((effectC.agrees.trans agD).read (n := 64) (r := 1) (by simp)).trans bcx
    have dsi : d.regValue .rsi = BitVec.ofNat 64 q :=
      (frameD.read (n := 64) (r := 6) (by simp)).trans requested
    by_cases he : q = k
    · refine ⟨4, d, ((runA.trans runB).trans runC).trans runD, readyD, loadedD, ?_, dx, dcx, dsi, frameD⟩
      simpa [he, branchTarget, Extracted.textAddress] using ripD
    · have hq : q = k+1 := step.resolve_left he
      have ripD' : d.RIP = 0x1181c1 := by
        simpa [he, branchTarget, Extracted.textAddress] using ripD
      obtain ⟨e, runE, readyE, loadedE, effectE⟩ := step_nomem (offset := 0x181c1)
        (cmp_r64_r64_effect_step 0x1181c1 0x48 0xf0 (by simp [RexWPrefix]) rfl)
        readyD loadedD ripD' (by decide) (by decide +kernel)
        (boundary_ne_program outer (inProgram_of_textOffset 0x181c4 (by decide)))
        (by simp [Component.Covers])
      have zfE : (StatusFlags.ofRFLAGS e.RFLAGS).ZF = true := by
        have h := effectE.flags.2.2.2.1
        change _ = ((d.regValue .rax - d.regValue .rsi) == 0) at h
        simpa [dx, dsi, hq] using h
      obtain ⟨f, runF, readyF, loadedF, ripF, agF⟩ := branch32 (offset := 0x181c4) 5 0xa5 false
        readyE loadedE effectE.rip (by simp [condHolds, zfE]) (by decide) (by decide +kernel)
        (by decide +kernel) (boundary_ne_program outer (inProgram_of_textOffset 0x181ca (by decide)))
      have ef := effectE.agrees.trans agF
      exact ⟨6, f, ((((runA.trans runB).trans runC).trans runD).trans runE).trans runF,
        readyF, loadedF, ripF, (ef.read (n := 64) (r := 0) (by simp)).trans dx,
        (ef.read (n := 64) (r := 1) (by simp)).trans dcx,
        (ef.read (n := 64) (r := 6) (by simp)).trans dsi,
        (frameD.trans ef).mono (by simp)⟩
  obtain ⟨fuel, e, runE, readyE, loadedE, ripE, ex, ecx, esi, frameE⟩ := join
  obtain ⟨f, runF, readyF, loadedF, effectF⟩ := step_nomem (offset := 0x181ca)
    (cmp_r64_r64_effect_step 0x1181ca 0x48 0xce (by simp [RexWPrefix]) rfl)
    readyE loadedE ripE (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x181cd (by decide)))
    (by simp [Component.Covers])
  have condF : condHolds 6 (StatusFlags.ofRFLAGS f.RFLAGS) = decide (q=k) := by
    have cf := effectF.flags.1
    have zf := effectF.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS f.RFLAGS).CF = decide ((e.regValue .rsi).toNat < (e.regValue .rcx).toNat) at cf
    change (StatusFlags.ofRFLAGS f.RFLAGS).ZF = ((e.regValue .rsi - e.regValue .rcx) == 0) at zf
    rw [show condHolds 6 (StatusFlags.ofRFLAGS f.RFLAGS) =
      ((StatusFlags.ofRFLAGS f.RFLAGS).CF || (StatusFlags.ofRFLAGS f.RFLAGS).ZF) from rfl, cf, zf, esi, ecx]
    have hk : k < 4 := by omega
    have ltfalse : decide ((BitVec.ofNat 64 q).toNat < (BitVec.ofNat 64 k).toNat) = false := by
      simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]
      omega
    rw [ltfalse, Bool.false_or]
    have he : (BitVec.ofNat 64 q = BitVec.ofNat 64 k) ↔ q = k := by
      constructor
      · intro hh
        have := congrArg BitVec.toNat hh
        simp only [BitVec.toNat_ofNat] at this
        omega
      · rintro rfl; rfl
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.sub_eq_iff_eq_add, he]
  obtain ⟨t, runT, readyT, loadedT, ripT, agT⟩ := branch8 (offset := 0x181cd) 6 0x5d (decide (q=k))
    readyF loadedF effectF.rip condF (by decide) (by decide +kernel) (by decide +kernel) (by
      by_cases he : q = k
      · simpa [he, branchTarget, Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0x1822c (by decide))
      · simpa [he, branchTarget, Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0x181cf (by decide)))
  refine ⟨fuel+2, t, (runE.trans runF).trans runT, readyT, loadedT, ?_, ?_, ?_⟩
  · simpa [branchTarget, Extracted.textAddress] using ripT
  · exact ((effectF.agrees.trans agT).read (n := 64) (r := 0) (by simp)).trans ex
  · exact ((frameE.trans effectF.agrees).trans agT).mono (by simp)

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
