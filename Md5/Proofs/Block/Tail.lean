import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Bytes
import Md5.Proofs.Block.Preconditions
import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Load.Cmp
import Md5.Proofs.Block.Rounds.Store
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem compression_tail [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {stop : BitVec 64} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hEntry : s.RIP = 0x102427)
    (hRead : MemReadable s (s.regValue .rsp + 104) 8)
    (hEnd : memLoad s.external (s.regValue .rsp + 104) 64 = stop)
    (hBoundary : OutsideCompression boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if s.regValue .rsi + 64 = stop then 0x102436 else 0x101be0) ∧
      t.regValue .rsi = s.regValue .rsi + 64 ∧
      AgreesExcept [.reg 6, .flags, .rip] s t := by
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x102427)
      (codeRange 0x102427 [0x48, 0x83, 0xc6, 0x40]) (addR64Imm8Effect 0x102427 6 64) :=
    add_r64_imm8_effect_step 0x102427 0x48 0xc6 64
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  obtain ⟨u, hau, hru, heu⟩ := hAdd.advances hReady
    (program_text_slice hCode 0x2427 4 (by decide +kernel)) hEntry
    (outsideCompression_ne (pc := 0x10242b) hBoundary (by decide) (by decide))
  have hcu := heu.codeIn (addR64Imm8Effect_avoids _ _ _ _ _) hCode
  have hsu : u.regValue .rsp = s.regValue .rsp := heu.agrees.read (n := 64) (r := 4) (by simp)
  have hmu : u.external = s.external := heu.agrees.external (by simp [Component.Covers])
  have hsi : u.regValue .rsi = s.regValue .rsi + 64 := heu.writes
  have hCmp : StepEffect
      (LoadPre 0x10242b (fun t ↦ t.regValue .rsp + 104) 8)
      (codeRange 0x10242b [0x48, 0x3b, 0x74, 0x24, 0x68])
      (Rounds.cmpR64M64Effect 0x10242b 6 (.sib 4 none 0 (.d8 104))) := by
    exact Rounds.cmp_r64_m64_effect_step 0x10242b 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 104))
      (by decide) (by decide) (by decide)
  have hPre : LoadPre 0x10242b (fun t ↦ t.regValue .rsp + 104) 8 u :=
    ⟨heu.rip, by rw [hsu]; exact hRead.of_external_eq hmu⟩
  obtain ⟨v, huv, hrv, hev⟩ := hCmp.advances hru
    (program_text_slice hcu 0x242b 5 (by decide +kernel)) hPre
    (outsideCompression_ne (pc := 0x102430) hBoundary (by decide) (by decide))
  have hcv := hev.agrees.codeIn (by simp [Rounds.cmpR64M64Effect,
    Effect.components, Component.Covers]) hcu
  have hz : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = (s.regValue .rsi + 64 == stop) := by
    have hz := hev.flag .ZF
    rw [Rounds.cmpR64M64Effect_zf] at hz
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (u.regValue .rsi == memLoad u.external (u.regValue .rsp + 104) 64) at hz
    simpa only [hsi, hsu, hmu, hEnd] using hz
  have hcond : condHolds 5 (StatusFlags.ofRFLAGS v.RFLAGS) =
      !(s.regValue .rsi + 64 == stop) := congrArg Bool.not hz
  have hBranch := jcc_rel32_effect_step 0x102430 5 0xfffff7aa
  have hNext : (jccEffect 0x102430 6 5 ((0xfffff7aa#32).signExtend 64) v).rip =
      (if s.regValue .rsi + 64 = stop then 0x102436 else 0x101be0) := by
    simp only [jccEffect, hcond, branchEffect]
    split <;> simp_all [branchTarget]
  have hBoundary' : (jccEffect 0x102430 6 5 ((0xfffff7aa#32).signExtend 64) v).rip ≠
      boundary.rip := by
    rw [hNext]
    split <;> exact outsideCompression_ne hBoundary (by decide) (by decide)
  obtain ⟨t, hvt, hrt, het⟩ := hBranch.advances hrv
    (program_text_slice hcv 0x2430 6 (by decide +kernel))
    ⟨hev.rip, fun _ ↦ by decide +kernel⟩ hBoundary'
  have hgt : AgreesExcept [.rip] v t := het.agrees
  refine ⟨t, (hau.trans huv).trans hvt, hrt,
    hgt.codeIn (by simp [Component.Covers]) hcv, het.rip.trans hNext, ?_, ?_⟩
  · exact (hgt.read (n := 64) (r := 6) (by simp)).trans
      ((hev.agrees.read (n := 64) (r := 6) (by
        simp [Rounds.cmpR64M64Effect, Effect.components])).trans hsi)
  · apply ((heu.agrees.trans hev.agrees).trans hgt).mono
    simp [addR64Imm8Effect, Rounds.cmpR64M64Effect, Effect.components]

structure OutputPre (output : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = 0x102436
  read : MemReadable s (s.regValue .rsp + 96) 8
  pointer : memLoad s.external (s.regValue .rsp + 96) 64 = output
  write : Memory.MemWritable s output 16
  avoid : ∀ i < 16, ¬ InProgram (output + BitVec.ofNat 64 i)

def outputBytes : List UInt8 :=
  [0x48, 0x8b, 0x74, 0x24, 0x60, 0x44, 0x89, 0x46, 0x04,
    0x89, 0x56, 0x08, 0x89, 0x46, 0x0c, 0x89, 0x0e]

def outputEffect (output : BitVec 64) (s : RamState) : Effect :=
  { rip := 0x102447
    writes := [⟨(.reg 6 : Operand 64), output⟩,
      ⟨(.mem (output + 4) : Operand 32), (Operand.reg 8 : Operand 32).read s⟩,
      ⟨(.mem (output + 8) : Operand 32), (Operand.reg 2 : Operand 32).read s⟩,
      ⟨(.mem (output + 12) : Operand 32), (Operand.reg 0 : Operand 32).read s⟩,
      ⟨(.mem output : Operand 32), (Operand.reg 1 : Operand 32).read s⟩] }

theorem output_address_in_program (i : Nat) (hi : i < 17) :
    InProgram (0x102436 + BitVec.ofNat 64 i) := by
  have hsize : 0x2447 ≤ Extracted.textBytes.size := by decide +kernel
  have h := text_address_in_program (0x2436 + i) (by omega)
  simpa only [BitVec.ofNat_add, Extracted.textAddress, ← BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h

theorem OutputPre.apart {output : BitVec 64} {s : RamState} (h : OutputPre output s)
    (offset codeOffset codeLength : Nat) (ho : offset + 4 ≤ 16)
    (hc : codeOffset + codeLength ≤ 17) :
    RangeApart (output + BitVec.ofNat 64 offset) 4
      (0x102436 + BitVec.ofNat 64 codeOffset) codeLength := by
  intro i hi j hj he
  apply h.avoid (offset + i) (by omega)
  have hp := output_address_in_program (codeOffset + j) (by omega)
  simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, ← he] using hp

macro "output_store_mid " out:term "," offset:term "," codeOffset:term ","
    codeLength:term : tactic =>
  `(tactic| (
    intro s t h hE hO
    have hsi : (Operand.reg (6#5) : Operand 64).read t = $out := by
      have hr := (hO true).read (Operand.reg (6#5) : Operand 64) trivial
      x86_norm at hr
      exact hr.symm.trans h.pointer
    refine ⟨⟨hE.rip_of (by x86_norm), ?_, ?_⟩, ?_⟩
    · x86_norm
      rw [hsi]
      simpa using (memoryWritable_slice h.write $offset 4 (by decide)).of_holds hE
    · x86_norm
      rw [hsi]
      simpa using h.apart $offset $codeOffset $codeLength (by decide) (by decide)
    · apply Effect.avoids_of_components_mem_rip (by rfl)
      x86_norm
      rw [hsi]
      simpa using h.apart $offset 0 17 (by decide) (by decide)))

theorem compression_output_block [Bindings] (output : BitVec 64) (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    AdvancesBlock boundary (OutputPre output) (codeRange 0x102436 outputBytes)
      (outputEffect output) := by
  unfold outputBytes
  md5_run_begin (mov_r64_m64_effect_step 0x102436 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide))
  case pre => intro s h; exact ⟨h.rip, h.read⟩
  case boundary =>
    intro _ _
    exact outsideCompression_ne (pc := 0x10243b)
      hOutside (by decide) (by decide)
  md5_run_then (Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x10243b 0x44
    (by unfold RexNoWPrefix; decide) 0 (.base 6 (.d8 4))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x102436) 5 (by decide +kernel)
  case mid => output_store_mid output, 4, 5, 4
  case boundary =>
    intro _ _
    exact outsideCompression_ne (pc := 0x10243f)
      hOutside (by decide) (by decide)
  md5_run_then (Rounds.Store.mov_m32_r32_noRex_effect_step 0x10243f 2 (.base 6 (.d8 8))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x102436) 9 (by decide +kernel)
  case mid => output_store_mid output, 8, 9, 3
  case boundary =>
    intro _ _
    exact outsideCompression_ne (pc := 0x102442)
      hOutside (by decide) (by decide)
  md5_run_then (Rounds.Store.mov_m32_r32_noRex_effect_step 0x102442 0 (.base 6 (.d8 12))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x102436) 12 (by decide +kernel)
  case mid => output_store_mid output, 12, 12, 3
  case boundary =>
    intro _ _
    exact outsideCompression_ne (pc := 0x102445)
      hOutside (by decide) (by decide)
  md5_run_then (Rounds.Store.mov_m32_r32_noRex_effect_step 0x102445 1 (.base 6 .none)
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x102436) 15 (by decide +kernel)
  case mid => output_store_mid output, 0, 15, 2
  case boundary =>
    intro _ _
    exact outsideCompression_ne (pc := 0x102447)
      hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t h hE
  have hp : (Operand.mem ((Operand.reg (4#5) : Operand 64).read s + 96#64) :
      Operand 64).read s = output := h.pointer
  apply hE.weaken
  · x86_norm [outputEffect]
  · x86_norm [outputEffect, hp]
    simp [gprNumber, rexR]
  · intro i; cases i <;> x86_norm [outputEffect]
  · x86_norm [outputEffect, hp]
    exact BitVec.add_zero output

theorem compression_output [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {output : BitVec 64} {buffer : Standards.RFC.MD5.Buffer} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hEntry : s.RIP = 0x102436)
    (hRead : MemReadable s (s.regValue .rsp + 96) 8)
    (hOutput : memLoad s.external (s.regValue .rsp + 96) 64 = output)
    (hWrite : Memory.MemWritable s output 16)
    (hAvoid : ∀ i < 16, ¬ InProgram (output + BitVec.ofNat 64 i))
    (hRegisters : LoopRegisters buffer s)
    (hBoundary : OutsideCompression boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x102447 ∧ t.regValue .rsi = output ∧
      Bytes t.external output 4 (storedByte buffer.A) ∧
      Bytes t.external (output + 4) 4 (storedByte buffer.B) ∧
      Bytes t.external (output + 8) 4 (storedByte buffer.C) ∧
      Bytes t.external (output + 12) 4 (storedByte buffer.D) ∧
      AgreesExcept [.reg 6, .mem output 16, .rip] s t := by
  have hc : CodeIn (codeRange 0x102436 outputBytes) s :=
    program_text_slice hCode 0x2436 17 (by decide +kernel)
  obtain ⟨fuel, t, hat, hrt, _, he⟩ :=
    compression_output_block output boundary hBoundary s hReady hc
      ⟨hEntry, hRead, hOutput, hWrite, hAvoid⟩
  have hg : AgreesExcept [.reg 6, .mem (output + 4) 4, .mem (output + 8) 4,
      .mem (output + 12) 4, .mem output 4, .rip] s t := by
    simpa [outputEffect, Effect.components] using he.agrees
  have hFrame : AgreesExcept [.reg 6, .mem output 16, .rip] s t := by
    apply hg.widen
    · intro c hcm hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [Component.isMem]
    · intro address c hcm hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
      all_goals
        refine ⟨.mem output 16, by simp, ?_⟩
        obtain ⟨i, hi, he⟩ := hcov
      · refine ⟨4 + i, by omega, ?_⟩
        simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
      · refine ⟨8 + i, by omega, ?_⟩
        simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
      · refine ⟨12 + i, by omega, ?_⟩
        simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
      · exact ⟨i, by omega, he⟩
  have hct : CodeIn Extracted.programImage t := by
    apply CodeIn.of_agreesExcept hFrame _ hCode
    intro x hx c hcm hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i, hi, hiEq⟩ := hcov
    exact hAvoid i hi (hiEq ▸ ⟨x.2, hx⟩)
  have hb (offset : Nat) (ho : offset + 4 ≤ 16) (value : BitVec 32)
      (hv : memLoad t.external (output + BitVec.ofNat 64 offset) 32 = value) :
      Bytes t.external (output + BitVec.ofNat 64 offset) 4 (storedByte value) := by
    have ha : ∀ i < 32 / 8,
        (t.external[output + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      apply hFrame.grow
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hWrite.bytes (offset + i) (by omega)
    have hbytes := Bytes.of_memLoad ha
    rw [hv] at hbytes
    exact hbytes
  refine ⟨fuel, t, hat, hrt, hct, he.rip, he.writes.1, ?_, ?_, ?_, ?_, hFrame⟩
  · have hv : memLoad t.external output 32 = buffer.A :=
      he.writes.2.2.2.2.trans hRegisters.1
    simpa using hb 0 (by decide) buffer.A (by simpa using hv)
  · exact hb 4 (by decide) buffer.B (he.writes.2.1.trans hRegisters.2.1)
  · exact hb 8 (by decide) buffer.C (he.writes.2.2.1.trans hRegisters.2.2.1)
  · exact hb 12 (by decide) buffer.D (he.writes.2.2.2.1.trans hRegisters.2.2.2)

end Md5.Proofs.Block
