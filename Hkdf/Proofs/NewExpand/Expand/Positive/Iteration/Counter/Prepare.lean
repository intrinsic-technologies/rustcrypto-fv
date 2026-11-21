import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Store
import Hkdf.Proofs.Common.Instructions.Lea32
import Hkdf.Proofs.Common.Memory.Bytes
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.AccImm32.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine

private theorem load_counter [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {length n : Nat}
    (ctx : StackContext entry boundary length) (running : RunningFrame entry boundary length s)
    (sp : stackPtr s = base entry) (pc : s.RIP = 0x10f8a0)
    (counter : slot s 256 = BitVec.ofNat 64 n) (bound : n < 255) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x10f8b9 ∧
      t.regValue .rax = BitVec.ofNat 64 n ∧ t.regValue .r15 = base entry + 80 ∧
      AgreesExcept [.reg 0, .reg 15, .flags, .rip] s t := by
  have code := programLoaded_codeIn running.loaded
  obtain ⟨u, a₁, r₁, load⟩ := (mov_r64_m64_effect_step 0x10f8a0 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl).advances
    (supportedMachine_readyToStep running.machine)
    (programText_slice code 0xf8a0 [0x48,0x8b,0x84,0x24,0,1,0,0] (by decide) (by decide +kernel))
    ⟨pc, by
      change MemReadable s (stackPtr s + 256) 8
      rw [sp]
      exact read_stack ctx running (off := 256) (by decide) (by decide)⟩
    (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8a8 (by decide)))
  have f₁ : AgreesExcept [.reg 0, .rip] s u := load.agrees
  have reg₁ : u.regValue .rax = BitVec.ofNat 64 n := load.writes.trans counter
  have codeU := f₁.codeIn (by simp [Component.Covers]) code
  obtain ⟨v, a₂, r₂, cmp⟩ := (cmp_rax_imm32_effect_step 0x10f8a8 0x48 256
    (by simp [RexWPrefix])).advances r₁
    (programText_slice codeU 0xf8a8 [0x48,0x3d,0,1,0,0] (by decide) (by decide +kernel))
    load.rip (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8ae (by decide)))
  have f₂ : AgreesExcept [.flags, .rip] u v := cmp.agrees
  have zero : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = false := by
    have z := cmp.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF = (u.regValue .rax - 256 == 0) at z
    rw [z, reg₁]
    apply Bool.eq_false_iff.mpr
    intro same
    have eq : (BitVec.ofNat 64 n) = 256 := by
      have sub : BitVec.ofNat 64 n - 256 = 0 := beq_iff_eq.mp same
      bv_omega
    have val := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2^64 by omega),
      BitVec.reduceToNat] at val
    omega
  have f₁₂ := f₁.trans f₂
  have spV : stackPtr v = base entry :=
    (f₁₂.read (n := 64) (r := 4) (by simp)).trans sp
  have codeV := f₂.codeIn (by simp [Component.Covers]) codeU
  obtain ⟨w, a₃, r₃, lea⟩ := (lea_r64_effect_step 0x10f8ae 0x4c
    (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances r₂
    (programText_slice codeV 0xf8ae [0x4c,0x8d,0x7c,0x24,0x50] (by decide) (by decide +kernel))
    cmp.rip (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8b3 (by decide)))
  have f₃ : AgreesExcept [.reg 15, .rip] v w := lea.agrees
  have zeroW : (StatusFlags.ofRFLAGS w.RFLAGS).ZF = false := by
    rw [f₃.statusFlags (by simp), zero]
  obtain ⟨t, step, ready, branch⟩ := jcc_rel32_effect_step 0x10f8b3 4 0x190 w r₃
    (programText_slice (f₃.codeIn (by simp [Component.Covers]) codeV)
      0xf8b3 [0x0f,0x84,0x90,1,0,0] (by decide) (by decide +kernel))
    ⟨lea.rip, fun _ => by decide⟩
  have pcT : t.RIP = 0x10f8b9 := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS w.RFLAGS).ZF then 0x10fa49 else 0x10f8b9) = _
    rw [zeroW]
    rfl
  have f₄ : AgreesExcept [.rip] w t := branch.agrees
  have a₄ : Advances boundary 1 w t := Advances.of_step step (.inl
    (by rw [pcT]; exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8b9 (by decide))))
  have keep := (f₂.trans f₃).trans f₄
  refine ⟨_, t, ((a₁.trans a₂).trans a₃).trans a₄, ready, pcT,
    (keep.read (n := 64) (r := 0) (by simp)).trans reg₁, ?_,
    ((f₁₂.trans f₃).trans f₄).mono (by simp)⟩
  have r15T : t.regValue .r15 = w.regValue .r15 := f₄.read (n := 64) (r := 15) (by simp)
  rw [r15T]
  exact (show w.regValue .r15 = stackPtr v + 80 from lea.writes).trans (by rw [spV])

private theorem counter_byte {n : Nat} (bound : n < 255) :
    ((BitVec.ofNat 64 n + 1).setWidth 32 |>.setWidth 64 |>.setWidth 8) =
      (UInt8.ofNat (n + 1)).toBitVec := by
  change _ = BitVec.ofNat 8 (n + 1)
  have nVal : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, nVal, BitVec.toNat_ofNat, BitVec.reduceToNat]
  omega

theorem prepare [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length n tail : Nat} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f8a0) (counter : slot s 256 = BitVec.ofNat 64 n) (bound : n < 255)
    (tailByte : s.external[base entry + 335]? = some (UInt8.ofNat tail)) (tailBound : tail < 64) :
    ∃ t, RunningFrame entry boundary length t ∧ stackPtr t = base entry ∧
      t.RIP = (if tail = 63 then 0x10f8ce else 0x10f920) ∧
      t.regValue .rax = BitVec.ofNat 64 tail ∧
      (t.regValue .rcx).setWidth 8 = (UInt8.ofNat (n + 1)).toBitVec ∧
      t.regValue .r15 = base entry + 80 ∧
      t.external[base entry + 80]? = some (UInt8.ofNat (n + 1)) ∧
      AgreesExcept [.reg 0, .reg 1, .reg 15, .flags, .mem (base entry + 80) 1, .rip] s t := by
  obtain ⟨fuel, u, runU, readyU, pcU, axU, r15U, frameU⟩ :=
    load_counter ctx running sp pc counter bound
  have ru := no_memory ctx running runU readyU frameU (by simp [Component.Covers]) (by simp)
  have spU : stackPtr u = base entry := (frameU.read (n := 64) (r := 4) (by simp)).trans sp
  obtain ⟨v, runV, readyV, lea⟩ := (Instructions.Lea32.lea_r32_legacy_effect_step 0x10f8b9
    1 (.base 0 (.d8 1)) (by decide) rfl rfl).advances readyU
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf8b9 [0x8d,0x48,1] (by decide) (by decide +kernel))
    pcU (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8bc (by decide)))
  have frameV : AgreesExcept [.reg 1, .rip] u v := lea.agrees
  have rv := no_memory ctx ru runV readyV frameV (by simp [Component.Covers]) (by simp)
  have spV : stackPtr v = base entry := (frameV.read (n := 64) (r := 4) (by simp)).trans spU
  have cxV : (v.regValue .rcx).setWidth 8 = (UInt8.ofNat (n + 1)).toBitVec := by
    have write : v.regValue .rcx = ((u.regValue .rax + 1).setWidth 32).setWidth 64 := lea.writes
    rw [write, axU]
    exact counter_byte bound
  obtain ⟨w, rw', readyW, pcW, written, frameW⟩ := store_stack ctx rv
    (codeOff := 0xf8bc) (codeSize := 4) (off := 80) (width := 8) lea.rip
    (show stackPtr v + 80 = _ by rw [spV]; rfl) (by decide) (by decide)
    (write_byte ctx rv (by decide))
    (mov_m8_r8_effect_step 0x10f8bc 1 (by decide) (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
    (programText_slice (programLoaded_codeIn rv.loaded) 0xf8bc [0x88,0x4c,0x24,0x50]
      (by decide) (by decide +kernel))
  have spW : stackPtr w = base entry := (frameW.read (n := 64) (r := 4) (by simp)).trans spV
  have newByte := byte_of_load (read_stack ctx rw' (off := 80) (by decide) (by decide))
    (written.trans cxV)
  have frameUW := frameV.trans frameW
  have tailW : w.external[base entry + 335]? = some (UInt8.ofNat tail) := by
    rw [frameW.byte (by
      intro c hc cover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, eq⟩ := cover
        have j0 : j = 0 := by omega
        subst j
        simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at eq
        bv_omega
      · exact cover.elim),
      frameV.external (by simp [Component.Covers]),
      frameU.external (by simp [Component.Covers]), tailByte]
  obtain ⟨x, runX, readyX, load⟩ := (movzx_r32_m8_effect_step 0x10f8c0 0
    (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl).advances readyW
    (programText_slice (programLoaded_codeIn rw'.loaded) 0xf8c0 [0x0f,0xb6,0x84,0x24,0x4f,1,0,0]
      (by decide) (by decide +kernel))
    ⟨pcW, by
      change MemReadable w (stackPtr w + 335) 1
      rw [spW]
      exact read_stack ctx rw' (off := 335) (by decide) (by decide)⟩
    (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8c8 (by decide)))
  have frameX : AgreesExcept [.reg 0, .rip] w x := load.agrees
  have rx := no_memory ctx rw' runX readyX frameX (by simp [Component.Covers]) (by simp)
  have axX : x.regValue .rax = BitVec.ofNat 64 tail := by
    have tailLoad : memLoad w.external (base entry + 335) 8 = (UInt8.ofNat tail).toBitVec := by
      have hb : Bytes w.external (base entry + 335) 1 (storedByte (UInt8.ofNat tail).toBitVec) := by
        intro i hi
        have h : i = 0 := by omega
        subst i
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, storedByte, Nat.mul_zero,
          Nat.shiftRight_zero, UInt8.ofNat_toNat, UInt8.toNat_toBitVec] using tailW
      exact hb.memLoad (by decide) (by decide)
    change x.regValue .rax = BitVec.ofNat 64 tail
    rw [show x.regValue .rax = (((Operand.mem (stackPtr w + 335) : Operand 8).read w).setWidth 32).setWidth 64
      from load.writes, spW]
    change ((memLoad w.external (base entry + 335) 8).setWidth 32).setWidth 64 = _
    rw [tailLoad]
    apply BitVec.eq_of_toNat_eq
    change (((BitVec.ofNat 8 tail).setWidth 32).setWidth 64).toNat = _
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  obtain ⟨y, runY, readyY, cmp⟩ := (cmp_r64_imm8_effect_step 0x10f8c8 0x48 0xf8 63
    (by simp [RexWPrefix]) rfl rfl).advances readyX
    (programText_slice (programLoaded_codeIn rx.loaded) 0xf8c8 [0x48,0x83,0xf8,0x3f] (by decide) (by decide +kernel))
    load.rip (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8cc (by decide)))
  have frameY : AgreesExcept [.flags, .rip] x y := cmp.agrees
  have ry := no_memory ctx rx runY readyY frameY (by simp [Component.Covers]) (by simp)
  have zero : (StatusFlags.ofRFLAGS y.RFLAGS).ZF = decide (tail = 63) := by
    have z := cmp.flags.2.2.2.1
    change _ = (x.regValue .rax - 63 == 0) at z
    rw [z, axX]
    by_cases eq : tail = 63
    · subst tail; rfl
    · rw [decide_eq_false_iff_not.mpr eq]
      apply Bool.eq_false_iff.mpr
      intro same
      have val : (BitVec.ofNat 64 tail) = 63 := by
        have sub : BitVec.ofNat 64 tail - 63 = 0 := beq_iff_eq.mp same
        bv_omega
      have hn := congrArg BitVec.toNat val
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show tail < 2^64 by omega),
        BitVec.reduceToNat] at hn
      exact eq hn
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel8_effect_step 0x10f8cc 5 0x52 y readyY
    (programText_slice (programLoaded_codeIn ry.loaded) 0xf8cc [0x75,0x52] (by decide) (by decide +kernel))
    ⟨cmp.rip, fun _ => by decide⟩
  have pcT : t.RIP = if tail = 63 then 0x10f8ce else 0x10f920 := by
    rw [branch.rip]
    change (if !(StatusFlags.ofRFLAGS y.RFLAGS).ZF then 0x10f920 else 0x10f8ce) = _
    rw [zero]
    split <;> simp_all
  have runT : Advances boundary 1 y t := Advances.of_step step (.inl (by
    rw [pcT]
    split
    · exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8ce (by decide))
    · exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf920 (by decide))))
  have frameT : AgreesExcept [.rip] y t := branch.agrees
  have afterW := (frameX.trans frameY).trans frameT
  have afterV := frameW.trans afterW
  have afterU := frameUW.trans afterW
  exact ⟨t, no_memory ctx ry runT readyT frameT (by simp [Component.Covers]) (by simp),
    (afterW.read (n := 64) (r := 4) (by simp)).trans spW, pcT,
    ((frameY.trans frameT).read (n := 64) (r := 0) (by simp)).trans axX,
    (congrArg (BitVec.setWidth 8) (afterV.read (n := 64) (r := 1) (by simp))).trans cxV,
    (afterU.read (n := 64) (r := 15) (by simp)).trans r15U,
    (afterW.byte (by simp [Component.Covers])).trans newByte,
    (frameU.trans afterU).mono (by simp)⟩

end Hkdf.Proofs.NewExpand.Expand.Counter
