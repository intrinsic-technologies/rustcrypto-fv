import Sha2.Proofs.Common.Memory.Fill.Memory
import Sha2.Proofs.Common.Memory.Fill.Prologue
import Sha2.Proofs.Common.Memory.Fill.Stos
import Sha2.Proofs.Common.Memory.Fill.StosOperation
import Sha2.Proofs.Common.Memory.Fill.Loops
import Sha2.Proofs.Common.Memory.Fill.Return
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open Sha2.Proofs.Program

open Sha2.Proofs.Common.Machine (CalleePre CalleeResult boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice supportedMachine_readyToStep)
open Sha2.Proofs.Common.Memory.Fill (FillState fillComponents finish prologue registerComponents)

namespace Sha2.Proofs.Common.Memory.Fill

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memset_inProgram (offset : Nat) (h : offset < 69) :
    InProgram ((0x10dd10 : BitVec 64) + BitVec.ofNat 64 offset) := by
  have hi := inProgram_of_textOffset (0xdd10+offset) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hi
  exact hi

end Sha2.Proofs.Common.Memory.Fill

namespace Sha2.Proofs.Common.Memory

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memset_zero_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {n reserve : Nat} (hp : CalleePre s boundary 0x10dd10 0 n reserve)
    (hzero : (s.regValue .rsi).setWidth 32 = 0) (hlen : s.regValue .rdx = BitVec.ofNat 64 n) (bound : n < 2^32)
    (hReturn : InProgram (returnBoundary s).rip) :
    ∃ final, CalleeResult s final boundary n reserve ∧
      (∀ i < n, final.external[s.regValue .rdi + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept (fillComponents s n ++ [.reg 4, .rip]) s final := by
  let head := min n ((8 - (s.regValue .rdi).toNat % 8) % 8)
  have headSmall : head < 8 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.mod_lt _ (by decide))
  have headBound : head ≤ n := Nat.min_le_left _ _
  obtain ⟨s1, a1, hr1, hc1, hi1, hz1, _, hx1, hs1, h81, he1⟩ := Fill.prologue
    (supportedMachine_readyToStep hp.machine) (programLoaded_codeIn hp.loaded)
    hp.outerBoundary hp.rip hzero hlen bound
  have h1 : FillState s s1 0 := (FillState.start (supportedMachine_readyToStep hp.machine)).registers
    hr1 he1
  have code1 := programText_slice hc1 0xdd44 [0xf3,0xaa] (by decide) (by decide +kernel)
  obtain ⟨s2, a2, h2, hi2, _, he2⟩ := h1.repStosb hp (more := head) (by omega) hi1 hx1 hz1 code1
    (by intro i hi; have ht := Sha2.Proofs.Common.Memory.Fill.memset_inProgram (52+i) (by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht; exact ht)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0xdd46 (by decide)))
  have h2' : FillState s s2 head := by simpa only [Nat.zero_add] using h2
  have hs2 : s2.regValue .rsi = BitVec.ofNat 64 ((n-head)/8) :=
    (he2.read (n := 64) (r := 6) (by simp)).trans hs1
  have h82 : s2.regValue .r8 = BitVec.ofNat 64 ((n-head)%8) :=
    (he2.read (n := 64) (r := 8) (by simp)).trans h81
  have hz2 : s2.regValue .rax = 0 := (he2.read (n := 64) (r := 0) (by simp)).trans hz1
  have i3 := mov_r64_r64_effect_step 0x10dd46 0x48 0xf1 (by simp [RexWPrefix]) (by decide)
  have code2 := programText_slice (programLoaded_codeIn (h2'.loaded hp headBound))
    0xdd46 [0x48,0x89,0xf1] (by decide) (by decide +kernel)
  obtain ⟨s3, a3, h3, e3⟩ := h2'.step i3 code2 hi2
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0xdd49 (by decide)))
    (by change ∀ c ∈ [Component.reg 1, .rip], c ∈ registerComponents; simp [registerComponents])
  have hx3 : rcx.read s3 = BitVec.ofNat 64 ((n-head)/8) := e3.writes.trans hs2
  have hz3 : s3.regValue .rax = 0 :=
    (e3.agrees.read (n := 64) (r := 0) (by simp only [movR64R64Effect_components]; decide +kernel)).trans hz2
  have h83 : s3.regValue .r8 = BitVec.ofNat 64 ((n-head)%8) :=
    (e3.agrees.read (n := 64) (r := 8) (by simp only [movR64R64Effect_components]; decide +kernel)).trans h82
  have hbulk : head + 8*((n-head)/8) ≤ n := by omega
  have align3 : 0 < (n-head)/8 → (s3.regValue .rdi).toNat % 8 = 0 := by
    intro _
    have hd : (s.regValue .rdi).toNat + n < 2^32 := hp.outputBounded
    rw [h3.rdi, toNat_add_ofNat _ _ (by omega)]
    dsimp only [head]
    omega
  have code3 := programText_slice (programLoaded_codeIn (h3.loaded hp headBound))
    0xdd49 [0xf3,0x48,0xab] (by decide) (by decide +kernel)
  obtain ⟨s4, a4, h4, hi4, _, he4⟩ := h3.repStosq hp hbulk e3.rip hx3 hz3 align3 code3
    (by intro i hi; have ht := Sha2.Proofs.Common.Memory.Fill.memset_inProgram (57+i) (by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht; exact ht)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0xdd4c (by decide)))
  have h84 : s4.regValue .r8 = BitVec.ofNat 64 ((n-head)%8) :=
    (he4.read (n := 64) (r := 8) (by simp)).trans h83
  have hz4 : s4.regValue .rax = 0 := (he4.read (n := 64) (r := 0) (by simp)).trans hz3
  have i5 := mov_r64_r64_effect_step 0x10dd4c 0x4c 0xc1 (by simp [RexWPrefix]) (by decide)
  have code4 := programText_slice (programLoaded_codeIn (h4.loaded hp hbulk))
    0xdd4c [0x4c,0x89,0xc1] (by decide) (by decide +kernel)
  obtain ⟨s5, a5, h5, e5⟩ := h4.step i5 code4 hi4
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0xdd4f (by decide)))
    (by change ∀ c ∈ [Component.reg 1, .rip], c ∈ registerComponents; simp [registerComponents])
  have hx5 : rcx.read s5 = BitVec.ofNat 64 ((n-head)%8) := e5.writes.trans h84
  have hz5 : s5.regValue .rax = 0 :=
    (e5.agrees.read (n := 64) (r := 0) (by simp only [movR64R64Effect_components]; decide +kernel)).trans hz4
  have htotal : head + 8*((n-head)/8) + (n-head)%8 = n := by omega
  have code5 := programText_slice (programLoaded_codeIn (h5.loaded hp hbulk))
    0xdd4f [0xf3,0xaa] (by decide) (by decide +kernel)
  obtain ⟨s6, a6, h6, hi6, _, _⟩ := h5.repStosb hp (by omega) e5.rip hx5 hz5 code5
    (by intro i hi; have ht := Sha2.Proofs.Common.Memory.Fill.memset_inProgram (63+i) (by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht; exact ht)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0xdd51 (by decide)))
  rw [htotal] at h6
  have i7 := mov_r64_r64_effect_step 0x10dd51 0x48 0xd0 (by simp [RexWPrefix]) (by decide)
  have code6 := programText_slice (programLoaded_codeIn (h6.loaded hp (Nat.le_refl _)))
    0xdd51 [0x48,0x89,0xd0] (by decide) (by decide +kernel)
  obtain ⟨s7, a7, h7, e7⟩ := h6.step i7 code6 hi6
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0xdd54 (by decide)))
    (by change ∀ c ∈ [Component.reg 0, .rip], c ∈ registerComponents; simp [registerComponents])
  exact finish hp h7 e7.rip (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))) hReturn


theorem memset_zero32_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {reserve : Nat} (hp : CalleePre s boundary 0x10dd10 0 32 reserve)
    (hzero : (s.regValue .rsi).setWidth 32 = 0) (hlen : s.regValue .rdx = 32)
    (hReturn : InProgram (returnBoundary s).rip) :
    ∃ final, CalleeResult s final boundary 32 reserve ∧
      (∀ i < 32, final.external[s.regValue .rdi + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept (fillComponents s 32 ++ [.reg 4, .rip]) s final :=
  memset_zero_correct hp hzero hlen (by decide) hReturn

end Sha2.Proofs.Common.Memory
