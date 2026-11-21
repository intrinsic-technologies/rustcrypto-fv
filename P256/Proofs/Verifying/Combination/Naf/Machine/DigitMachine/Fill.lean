import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Memory
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Instructions.StoreByte
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Iterator.Advance (step_nomem branch8)
open P256.Proofs.Common.Instructions (mov_m8_imm8_rex_effect_step)

theorem fill_step [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i k j : Nat}
    (pre : Pre s boundary) (frame : FrameState s t)
    (bound : i+k ≤ 256) (lt : j<k)
    (rip : t.RIP = 0x10f4c0) (rax : t.regValue .rax = BitVec.ofNat 64 (257-i))
    (rbp : t.regValue .rbp = BitVec.ofNat 64 k)
    (r14 : t.regValue .r14 = s.regValue .rdi+BitVec.ofNat 64 i)
    (rdx : t.regValue .rdx = BitVec.ofNat 64 j) :
    ∃ u, Advances boundary 6 t u ∧ FrameState s u ∧
      u.RIP = (if j+1<k then 0x10f4c0 else 0x10f4d2) ∧
      u.regValue .rdx = BitVec.ofNat 64 (j+1) ∧
      u.external[s.regValue .rdi+BitVec.ofNat 64 (i+j)]? = some 0 ∧
      AgreesExcept [.reg 2,.flags,.rip,.mem (s.regValue .rdi+BitVec.ofNat 64 (i+j)) 1] t u := by
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := step_nomem (offset := 0xf4c0)
    (cmp_r64_r64_effect_step 0x10f4c0 0x48 0xd0 (by simp [RexWPrefix]) rfl)
    (readyToStep frame.machine frame.bindingsSupported) frame.loaded rip (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4c3 (by decide)))
    (by simp [Component.Covers])
  have zfA : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .rax-t.regValue .rdx)==0) at h
    rw [h, rax, rdx]
    have ne : BitVec.ofNat 64 (257-i) ≠ BitVec.ofNat 64 j := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at hn
      omega
    simp [BitVec.sub_eq_iff_eq_add, ne]
  obtain ⟨b, runB, readyB, loadedB, ripB, agreesB⟩ := branch8 (offset := 0xf4c3) 4 0x42 false
    readyA loadedA effectA.rip zfA (by decide) (by decide +kernel) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4c5 (by decide)))
  have totalB : AgreesExcept [.flags,.rip] t b := (effectA.agrees.trans agreesB).mono (by simp)
  have frameB := frame.after_registers readyB totalB (by simp [Component.Covers]) (by simp)
  have b14 : b.regValue .r14 = s.regValue .rdi+BitVec.ofNat 64 i :=
    (totalB.read (n := 64) (r := 14) (by simp)).trans r14
  have bdx : b.regValue .rdx = BitVec.ofNat 64 j :=
    (totalB.read (n := 64) (r := 2) (by simp)).trans rdx
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (P256.Proofs.Common.Instructions.mov_m8_imm8_rex_effect_step 0x10f4c5 0x41 (by simp [RexNoWPrefix])
      (.sib 14 (some 2) 0 .none) (by decide +kernel) rfl rfl 0).advances readyB
      (programText_slice (programLoaded_codeIn loadedB) 0xf4c5
        [0x41,0xc6,0x04,0x16,0x00] (by decide) (by decide +kernel))
      ⟨ripB, by
        change MemWritable b (b.regValue .r14+(b.regValue .rdx <<< 0)+0#64) 1
        rw [BitVec.shiftLeft_zero, b14, bdx, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact output_writable pre frameB (by omega)
      , by
        change RangeApart (b.regValue .r14+(b.regValue .rdx <<< 0)+0#64) 1 0x10f4c5 5
        rw [BitVec.shiftLeft_zero, b14, bdx, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact output_code pre (pc := 0xf4c5) (by omega) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4ca (by decide)))
  change ({rip := 0x10f4ca, writes := [⟨(Operand.mem
    (b.regValue .r14+(b.regValue .rdx <<< 0)+0#64) : Operand 8),0⟩]} : Effect).Holds b c at effectC
  rw [BitVec.shiftLeft_zero, b14, bdx, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add] at effectC
  have agreesC : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 (i+j)) 1,.rip] b c := by
    simpa [Effect.components] using effectC.agrees
  have frameC := (output_after pre frameB (i := i+j) (len := 1) (by omega) readyC agreesC
    (by simp [Component.Covers]) (by simp)).1
  have zeroC : c.external[s.regValue .rdi+BitVec.ofNat 64 (i+j)]? = some 0 := by
    have bytes := Bytes.of_memLoad (n := 8) (output_readable pre frameC (i := i+j) (len := 1) (by omega)).mem
    have value : memLoad c.external (s.regValue .rdi+BitVec.ofNat 64 (i+j)) 8 = 0 := effectC.writes
    rw [value] at bytes
    simpa [storedByte] using bytes 0 (by decide)
  have cdx : c.regValue .rdx = BitVec.ofNat 64 j :=
    (agreesC.read (n := 64) (r := 2) (by simp)).trans bdx
  obtain ⟨d, runD, readyD, loadedD, effectD⟩ := step_nomem (offset := 0xf4ca)
    (inc_r64_effect_step 0x10f4ca 0x48 0xc2 (by simp [RexWPrefix]) rfl rfl)
    readyC frameC.loaded effectC.rip (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4cd (by decide)))
    (by simp [Component.Covers])
  have agreesD : AgreesExcept [.reg 2,.flags,.rip] c d := effectD.agrees
  have ddx : d.regValue .rdx = BitVec.ofNat 64 (j+1) := by
    have h := effectD.writes
    change d.regValue .rdx = c.regValue .rdx+1 at h
    rw [cdx] at h
    change d.regValue .rdx = BitVec.ofNat 64 j+1#64 at h
    simpa only [BitVec.ofNat_add] using h
  have dbp : d.regValue .rbp = BitVec.ofNat 64 k :=
    (((totalB.trans agreesC).trans agreesD).read (n := 64) (r := 5) (by simp)).trans rbp
  obtain ⟨e, runE, readyE, loadedE, effectE⟩ := step_nomem (offset := 0xf4cd)
    (cmp_r64_r64_effect_step 0x10f4cd 0x48 0xd5 (by simp [RexWPrefix]) rfl)
    readyD loadedD effectD.rip (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4d0 (by decide)))
    (by simp [Component.Covers])
  have zfE : (StatusFlags.ofRFLAGS e.RFLAGS).ZF = decide (k=j+1) := by
    have h := effectE.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS e.RFLAGS).ZF = ((d.regValue .rbp-d.regValue .rdx)==0) at h
    rw [h, dbp, ddx]
    have eq : (BitVec.ofNat 64 k = BitVec.ofNat 64 (j+1)) ↔ k=j+1 := by
      constructor
      · intro eq
        have hn := congrArg BitVec.toNat eq
        simp only [BitVec.toNat_ofNat] at hn
        omega
      · rintro rfl; rfl
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.sub_eq_iff_eq_add, eq]
  have condE : condHolds 5 (StatusFlags.ofRFLAGS e.RFLAGS) = decide (j+1<k) := by
    by_cases h : j+1<k
    · have ne : k ≠ j+1 := by omega
      simp [condHolds, zfE, h, ne]
    · have eq : k = j+1 := by omega
      simp [condHolds, zfE, eq]
  obtain ⟨u, runU, readyU, _, ripU, agreesU⟩ := branch8 (offset := 0xf4d0) 5 0xee (decide (j+1<k))
    readyE loadedE effectE.rip condE (by decide) (by decide +kernel) (by decide +kernel) (by
      by_cases h : j+1<k
      · simpa [h, branchTarget, Extracted.textAddress] using
          boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4c0 (by decide))
      · simpa [h, branchTarget, Extracted.textAddress] using
          boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4d2 (by decide)))
  have tail : AgreesExcept [.reg 2,.flags,.rip] c u :=
    ((agreesD.trans effectE.agrees).trans agreesU).mono (by simp)
  refine ⟨u, ((((runA.trans runB).trans runC).trans runD).trans runE).trans runU,
    frameC.after_registers readyU tail (by simp [Component.Covers]) (by simp), ?_, ?_, ?_, ?_⟩
  · simpa [branchTarget, Extracted.textAddress] using ripU
  · exact ((effectE.agrees.trans agreesU).read (n := 64) (r := 2) (by simp)).trans ddx
  · rw [tail.external (by simp [Component.Covers])]
    exact zeroC
  · exact ((totalB.trans agreesC).trans tail).mono (by simp)


theorem fill [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i k j : Nat}
    (pre : Pre s boundary) (frame : FrameState s t)
    (bound : i+k ≤ 256) (lt : j<k) (small : k≤5)
    (rip : t.RIP = 0x10f4c0) (rax : t.regValue .rax = BitVec.ofNat 64 (257-i))
    (rbp : t.regValue .rbp = BitVec.ofNat 64 k)
    (r14 : t.regValue .r14 = s.regValue .rdi+BitVec.ofNat 64 i)
    (rdx : t.regValue .rdx = BitVec.ofNat 64 j) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      u.RIP = 0x10f4d2 ∧ u.regValue .rdx = BitVec.ofNat 64 k ∧
      Bytes u.external (s.regValue .rdi+BitVec.ofNat 64 (i+j)) (k-j) (fun _ => 0) ∧
      AgreesExcept [.reg 2,.flags,.rip,.mem (s.regValue .rdi+BitVec.ofNat 64 (i+j)) (k-j)] t u := by
  generalize he : k-j = count
  induction count using Nat.strongRecOn generalizing j t with
  | ind count ih =>
    obtain ⟨v, runV, frameV, ripV, rdxV, zeroV, agreesV⟩ :=
      fill_step pre frame bound lt rip rax rbp r14 rdx
    by_cases next : j+1<k
    · have raxV : v.regValue .rax = BitVec.ofNat 64 (257-i) :=
        (agreesV.read (n := 64) (r := 0) (by simp)).trans rax
      have rbpV : v.regValue .rbp = BitVec.ofNat 64 k :=
        (agreesV.read (n := 64) (r := 5) (by simp)).trans rbp
      have r14V : v.regValue .r14 = s.regValue .rdi+BitVec.ofNat 64 i :=
        (agreesV.read (n := 64) (r := 14) (by simp)).trans r14
      have ripV' : v.RIP = 0x10f4c0 := by simpa only [ite_eq_left next] using ripV
      obtain ⟨fuel, u, runU, frameU, ripU, rdxU, zerosU, agreesU⟩ :=
        ih (k-(j+1)) (by omega) frameV next ripV' raxV rbpV r14V rdxV rfl
      refine ⟨6+fuel, u, runV.trans runU, frameU, ripU, rdxU, ?_, ?_⟩
      · intro q hq
        by_cases first : q=0
        · subst q
          simp only [BitVec.add_zero]
          refine (agreesU.memory _ ?_).trans zeroV
          intro c hc cover
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl <;> try exact cover.elim
          obtain ⟨a, ha, eq⟩ := cover
          rw [BitVec.add_assoc, ← BitVec.ofNat_add] at eq
          have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (s.regValue .rdi)).mp eq)
          simp only [BitVec.toNat_ofNat] at hn
          omega
        · have hz := zerosU (q-1) (by omega)
          rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hz ⊢
          rw [show i+(j+1)+(q-1) = i+j+q by omega] at hz
          exact hz
      · apply (agreesV.trans agreesU).widen
        · intro c hc hm
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
            simp_all [Component.isMem]
        · intro a c hc cover
          refine ⟨.mem (s.regValue .rdi+BitVec.ofNat 64 (i+j)) count, by simp, ?_⟩
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
            try exact cover.elim
          · obtain ⟨q, hq, rfl⟩ := cover
            exact ⟨q, by omega, rfl⟩
          · obtain ⟨q, hq, rfl⟩ := cover
            refine ⟨q+1, by omega, ?_⟩
            simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
            congr 2
            omega
    · have last : k = j+1 := by omega
      have countOne : count = 1 := by omega
      subst count
      refine ⟨6, v, runV, frameV, ?_, ?_, ?_, ?_⟩
      · simpa only [ite_eq_right next] using ripV
      · simpa only [last] using rdxV
      · intro q hq
        have q0 : q=0 := by omega
        simpa only [q0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using zeroV
      · simpa only [show k-j=1 by omega] using agreesV

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
