import Sha2.Proofs.Common.Instructions.ForgetFlags
import Sha2.Proofs.Reset.Header
import Sha2.Proofs.Wrapper.Variant
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Reset.Dispatch

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

def branchBytes (displacement : BitVec 32 := 0x257) (count : BitVec 4 := 12) : List UInt8 :=
  encodeTestR64R64 count count ++ [0x0f, 0x84] ++ immBytes 32 displacement

def tailBytes (savedSlot : BitVec 32 := 184) (index : BitVec 3 := 7)
    (displacement : BitVec 8 := 48) : List UInt8 :=
  [0x4c, 0x89, 0xac, 0x24] ++ immBytes 32 savedSlot ++
    [0x45, 0x31, UInt8.ofBitVec (3#2 ++ index ++ index), 0xeb, UInt8.ofBitVec displacement]

def entryOffset : Variant → Nat
  | .sha224 => 0xdae
  | .sha256 => 0x29de

def entry (v : Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (entryOffset v)

def branchEffect (p : BitVec 64) (s : RamState) (displacement : BitVec 32 := 0x257) (count : BitVec 4 := 12) : Effect :=
  { rip := if (.reg (count.setWidth 5) : Operand 64).read s = 0#64 then p + 9 + displacement.signExtend 64 else p + 9
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem branch [Bindings] (p : BitVec 64) {displacement : BitVec 32} {count : BitVec 4} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 9)
    (target : InProgram (p + 9 + displacement.signExtend 64)) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (branchBytes displacement count))
      (Effect.post (fun s => branchEffect p s displacement count)) := by
  intro s ready loaded rip
  have test : StepEffect (fun s => s.RIP = p)
      (codeRange p (encodeTestR64R64 count count))
      (testR64R64Effect p (count.setWidth 5) (count.setWidth 5)) := by
    obtain ⟨rex, modrm, bytes, rexValid, modValid, dst, src⟩ := encodeTestR64R64_spec count count
    rw [bytes]
    simpa only [dst, src] using test_r64_r64_effect_step p rex modrm rexValid modValid
  obtain ⟨u, run, readyU, tested⟩ := test.advances ready
    (loaded.mono (codeRange_mem_of_take (by simp [branchBytes, encodeTestR64R64]))) rip
    (boundary_ne_program outside (inside 3 (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := tested.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) loaded
  have testedRip : u.RIP = p + (3 : BitVec 64) := tested.rip
  have low : (branchTarget (p + 3) 6 (BitVec.signExtend 64 displacement)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step (p + 3) 4 displacement u readyU
    (codeU.mono (codeRange_mem_of_drop 3 (by
      simp only [branchBytes, encodeTestR64R64, List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append, List.length_cons, immBytes_length]
      change List.take (6) (0x0f :: 0x84 :: immBytes 32 displacement) = _
      simp only [List.take_succ_cons]
      exact congrArg (List.cons 0x0f) (congrArg (List.cons 0x84)
        (by simpa only [immBytes_length] using (List.take_length (l := immBytes 32 displacement))))))) ⟨testedRip, fun _ => low⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((.reg (count.setWidth 5) : Operand 64).read s == 0) := by
    have zero := tested.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((.reg (count.setWidth 5) : Operand 64).read s &&& (.reg (count.setWidth 5) : Operand 64).read s == 0) at zero
    simpa only [BitVec.and_self] using zero
  have ripT : t.RIP = (branchEffect p s displacement count).rip := by
    rw [jumped.rip]
    simp only [jccEffect, X86Proofs.branchEffect, branchTarget, condHolds]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then p + 3 + 6 +
      BitVec.signExtend 64 displacement else p + 3 + 6) = _
    rw [zero]
    simp [branchEffect, BitVec.add_assoc]
  have frameT : AgreesExcept [.flags, .rip] s t :=
    (frame.trans jumped.agrees).mono (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [ripT]
    simp only [branchEffect]
    split
    · exact boundary_ne_program outside target
    · exact boundary_ne_program outside (inside 9 (by decide))
  refine ⟨2, t, run.trans advance, readyT, ?_, ?_⟩
  · exact frameT.codeIn (by simp [Component.Covers]) loaded
  · refine ⟨ripT, ?_, ?_, ?_⟩
    · exact trivial
    · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    · exact frameT

structure TailPre (p : BitVec 64) (s : RamState) (savedSlot : BitVec 32 := 184) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (rspOf s + savedSlot.signExtend 64) 8
  apart : RangeApart (rspOf s + savedSlot.signExtend 64) 8 p 13

def tailEffect (p : BitVec 64) (s : RamState) (savedSlot : BitVec 32 := 184)
    (index : BitVec 3 := 7) (displacement : BitVec 8 := 48) : Effect :=
  { rip := p + (13 + displacement.signExtend 64)
    writes := [⟨(.mem (rspOf s + savedSlot.signExtend 64) : Operand 64), (.reg 13 : Operand 64).read s⟩,
      ⟨(.reg (0#1 ++ 1#1 ++ index) : Operand 64), 0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tailAt [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 13)
    (displacement : BitVec 8 := 48)
    (target : InProgram (p + (13 + displacement.signExtend 64)))
    (savedSlot : BitVec 32 := 184) (index : BitVec 3 := 7) :
    AdvanceTriple boundary (fun s => TailPre p s savedSlot)
      (codeRange p (tailBytes savedSlot index displacement))
      (Effect.post (fun s => tailEffect p s savedSlot index displacement)) := by
  have low : (branchTarget (p + 11) 2 (displacement.signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  have rm : gprNumber 0#1 (rexB (0x45 : UInt8).toBitVec)
      (modrmRm (UInt8.ofBitVec (3#2 ++ index ++ index))) = 0#1 ++ 1#1 ++ index :=
    (by decide +kernel : ∀ i : BitVec 3, gprNumber 0#1 (rexB (0x45 : UInt8).toBitVec)
      (modrmRm (UInt8.ofBitVec (3#2 ++ i ++ i))) = 0#1 ++ 1#1 ++ i) index
  have reg : gprNumber 0#1 (rexR (0x45 : UInt8).toBitVec)
      (modrmReg (UInt8.ofBitVec (3#2 ++ index ++ index))) = 0#1 ++ 1#1 ++ index :=
    (by decide +kernel : ∀ i : BitVec 3, gprNumber 0#1 (rexR (0x45 : UInt8).toBitVec)
      (modrmReg (UInt8.ofBitVec (3#2 ++ i ++ i))) = 0#1 ++ 1#1 ++ i) index
  dsimp only [tailBytes]
  advance_reloc_begin (mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 savedSlot)) (by simp [AddrMode.Valid]) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step
    (p + 8) 0x45 (UInt8.ofBitVec (3#2 ++ index ++ index))
      (by simp [RexNoWPrefix]) (by exact (show ∀ i : BitVec 3,
        modrmMod (UInt8.ofBitVec (3#2 ++ i ++ i)) = 3 by decide +kernel) index)))
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (p + 11) displacement low)
    next (boundary_ne_program outside target)
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [tailEffect, rm, reg]
  · x86_norm [tailEffect, rm, reg]
    constructor
    · congr 2 <;> decide +kernel
    · simp
  · intro i; cases i <;> x86_norm [tailEffect, rm, reg]
  · x86_norm [tailEffect, rm, reg]
  all_goals first
    | (apply codeRange_mem_of_drop 11; simp [immBytes, immByte, List.range_succ])
    | (apply codeRange_mem_of_drop 8; simp [immBytes, List.range_succ])
    | (simpa [immBytes_length] using hP.apart)
    | (apply codeRange_mem_of_take; simp [AddrMode.modrm, AddrMode.mod, AddrMode.rm,
        AddrMode.tail, AddrMode.sibByte, idxLow, regLow, Disp.mod, Disp.bytes, immBytes, List.range_succ])

theorem tail [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 13)
    (target : InProgram (p + 61)) :
    AdvanceTriple boundary (TailPre p) (codeRange p tailBytes)
      (Effect.post (tailEffect p)) :=
  tailAt p boundary outside inside 48 target

theorem branch_code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (entry v) branchBytes) s :=
  programText_slice (programLoaded_codeIn loaded) (entryOffset v) branchBytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem tail_code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (entry v + 9) tailBytes) s := by
  have h := programText_slice (programLoaded_codeIn loaded) (entryOffset v + 9) tailBytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
  simpa [entry, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem inside (v : Variant) : BlockInProgram (entry v) 608 :=
  blockInProgram_of_textOffset (entryOffset v) 608 (by cases v <;> decide +kernel)

end Sha2.Proofs.Reset.Dispatch
