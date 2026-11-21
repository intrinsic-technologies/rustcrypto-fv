import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Sec1.Affine.Representation
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Identity

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : AffineDecodePre s boundary ⟨#[0]⟩) (state : Frame s t)
    (rip : t.RIP = 0x11062c) (output : t.regValue .rbx = s.regValue .rdi)
    (value : AffineAt t (s.regValue .rdi) .infinity) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (some .infinity) := by
  have writable := (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add
    72 (len := 1) (by decide)
  have byteWritable : MemWritable t (s.regValue .rdi + 72) 1 :=
    ⟨writable.low, writable.mem, writable.tables⟩
  have apart := P256.Proofs.Common.Instructions.RangeApart.add_left
    (ScalarFrame.output_code pre.toCalleePre (offset := 0x1062c) (len := 4) (by decide))
    72 (len := 1) (by decide)
  have address (v : RamState) : storeAddrAt 0x11062c (.base 3 (.d8 72)) 4 v =
      v.regValue .rbx + 72 := rfl
  obtain ⟨a, aa, ra, ea⟩ := (mov_m8_imm8_effect_step 0x11062c (.base 3 (.d8 72))
    (by decide) rfl rfl 1).advances (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1062c _
      (by decide) (by decide +kernel))
    ⟨rip, by
        change MemWritable t (storeAddrAt 0x11062c (.base 3 (.d8 72)) 4 t) 1
        simpa only [address, output] using byteWritable,
      by
        change RangeApart (storeAddrAt 0x11062c (.base 3 (.d8 72)) 4 t) 1 0x11062c 4
        rw [address, output]
        exact apart⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10630 (by decide)))
  have ga : AgreesExcept [.mem (s.regValue .rdi + 72) 1, .rip] t a := by
    have h := ea.agrees
    simp only [movM8Imm8Effect_components] at h
    change AgreesExcept [.mem (t.regValue .rbx + 72) 1, .rip] t a at h
    rwa [output] at h
  have writes : WritesWithin [.mem (s.regValue .rdi + 72) 1, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, ScalarFrame.output_contains pre.toCalleePre (by decide) ha⟩
    · exact ha.elim
  have sa := state.after_effect pre.toCalleePre (by decide) ra ga writes (by simp)
  have valid : a.external[s.regValue .rdi + 72]? = some 1 := by
    have hw : memLoad a.external (s.regValue .rdi + 72) 8 = 1 := by
      have h : memLoad a.external (storeAddrAt 0x11062c (.base 3 (.d8 72)) 4 t) 8 = 1 := ea.writes
      simpa only [address, output] using h
    have hb : Bytes a.external (s.regValue .rdi + 72) 1 (storedByte (memLoad a.external (s.regValue .rdi + 72) 8)) :=
      Bytes.of_memLoad (n := 8) (fun i hi => ga.grow _ (writable.mem i hi))
    rw [hw] at hb
    have hz := hb 0 (by decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hz
    exact hz.trans (congrArg some (by decide +kernel))
  have affine : AffineAt a (s.regValue .rdi) .infinity := by
    apply value.of_bytes_eq
    intro i hi
    apply ga.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j,hj,eq⟩ := hcov
      have zero : j = 0 := by omega
      subst j
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at eq
      change s.regValue .rdi + BitVec.ofNat 64 i = s.regValue .rdi + 72 at eq
      simp only [BitVec.add_right_inj] at eq
      have h := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, BitVec.reduceToNat] at h
      omega
    · exact hcov.elim
  obtain ⟨u, au, ru, eu⟩ := (jmp_rel32_effect_step 0x110630 0x6ed (by decide)).advances ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0x10630 _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10d22 (by decide)))
  have gu : AgreesExcept [.rip] a u := eu.agrees
  have memory := gu.external (by simp [Component.Covers])
  refine ⟨u, aa.trans au, sa.after_registers ru gu (by simp [Component.Covers]) (by simp),
    eu.rip, ?_⟩
  exact (show AffineResultAt a (s.regValue .rdi) (some .infinity) from ⟨affine, valid⟩).of_bytes_eq
    (fun _ _ => by rw [memory])

end P256.Proofs.Sec1.Affine.Identity
