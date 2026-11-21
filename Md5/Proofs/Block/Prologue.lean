import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Control
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Preconditions
import Md5.Proofs.Block.Push
import Md5.Proofs.Block.Shl
import Md5.Proofs.Block.Nop
import Md5.Proofs.Block.Rounds.Load
import Md5.Proofs.Block.Rounds.Store
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

namespace Md5.Proofs.Block

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

structure ProloguePre (s : RamState) : Prop where
  rip : s.RIP = 0x101ba9
  write : Memory.MemWritable s (stackPtr s - 184) 184
  code : ∀ i < 184, ¬ InProgram (stackPtr s - 184 + BitVec.ofNat 64 i)
  read : MemReadable s ((Operand.reg 7 : Operand 64).read s) 16
  apart : RangeApart (stackPtr s - 184) 184 ((Operand.reg 7 : Operand 64).read s) 16

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

theorem ProloguePre.writable {s : RamState} (h : ProloguePre s) (back count : Nat)
    (hback : back ≤ 184) (hcount : count ≤ back) :
    Memory.MemWritable s (stackPtr s - BitVec.ofNat 64 back) count := by
  have hs := memoryWritable_slice h.write (184 - back) count (by omega)
  have he : stackPtr s - 184 + BitVec.ofNat 64 (184 - back) =
      stackPtr s - BitVec.ofNat 64 back := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 184 back (by omega) hback]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [BitVec.sub_eq_add_neg (184#64), ← BitVec.add_assoc, BitVec.sub_add_cancel,
      ← BitVec.sub_eq_add_neg]
  rwa [he] at hs

theorem ProloguePre.avoids_mem {s : RamState} (h : ProloguePre s) (back count : Nat)
    (hback : back ≤ 184) (hcount : count ≤ back) :
    ∀ x, InProgram x →
      ¬ (Component.mem (stackPtr s - BitVec.ofNat 64 back) count).Covers x := by
  intro x ⟨byte, hx⟩ ⟨i, hi, he⟩
  apply h.code (184 - back + i) (by omega)
  refine ⟨byte, ?_⟩
  have hadd : stackPtr s - 184 + BitVec.ofNat 64 (184 - back + i) =
      stackPtr s - BitVec.ofNat 64 back + BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.ofNat_sub_ofNat_of_le 184 back (by omega)
      hback]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [BitVec.sub_eq_add_neg (184#64), ← BitVec.add_assoc, BitVec.sub_add_cancel,
      ← BitVec.sub_eq_add_neg]
  rwa [hadd, ← he]

def prologueBytes : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
   0x48, 0x81, 0xec, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xd0,
   0x48, 0xc1, 0xe0, 0x06, 0x48, 0x01, 0xf0, 0x48, 0x89, 0x44, 0x24, 0x68,
   0x8b, 0x0f, 0x44, 0x8b, 0x47, 0x04, 0x8b, 0x57, 0x08,
   0x48, 0x89, 0x7c, 0x24, 0x60, 0x8b, 0x47, 0x0c,
   0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem prologue_address_in_program (i : Nat) (hi : i < 55) :
    InProgram (0x101ba9 + BitVec.ofNat 64 i) := by
  have hsize : 0x1be0 ≤ Extracted.textBytes.size := by decide +kernel
  have h := text_address_in_program (0x1ba9 + i) (by omega)
  simpa only [BitVec.ofNat_add, Extracted.textAddress, ← BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.ofNat_eq_ofNat] using h

theorem prologue_code_address {x : BitVec 64 × UInt8}
    (h : x ∈ codeRange 0x101ba9 prologueBytes) : InProgram x.1 := by
  obtain ⟨j, hj, he⟩ := exists_of_mem_codeRange h
  have hl : prologueBytes.length = 55 := rfl
  rw [hl] at hj
  exact he ▸ prologue_address_in_program j hj

theorem ProloguePre.apart_instruction {s : RamState} (h : ProloguePre s)
    (back count offset len : Nat) (hback : back ≤ 184) (hcount : count ≤ back)
    (hlen : offset + len ≤ 55) :
    RangeApart (stackPtr s - BitVec.ofNat 64 back) count
      (0x101ba9 + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply h.avoids_mem back count hback hcount _
    (by simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using
      prologue_address_in_program (offset + j) (by omega))
  exact ⟨i, hi, he.symm⟩

def prologueEffect (s : RamState) : Effect :=
  { rip := 0x101be0
    writes := [
      ⟨.mem (stackPtr s - 8), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 16), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 24), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 32), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 40), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 48), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨.reg 4, stackPtr s - 184⟩,
      ⟨.mem (stackPtr s - 80),
        ((Operand.reg 2 : Operand 64).read s <<< 6) + (Operand.reg 6 : Operand 64).read s⟩,
      ⟨.reg 1, ((Operand.mem ((Operand.reg 7 : Operand 64).read s) : Operand 32).read s).setWidth
        64⟩,
      ⟨.reg 8, ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read
        s).setWidth 64⟩,
      ⟨.reg 2, ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read
        s).setWidth 64⟩,
      ⟨.mem (stackPtr s - 88), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨.reg 0, ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read
        s).setWidth 64⟩]
    flags := some (.ofStatusFlags (addSpec
      ((Operand.reg 2 : Operand 64).read s <<< 6) ((Operand.reg 6 : Operand 64).read s)).2) }


private theorem writable_of_agrees {s t : RamState} {cs : List Component}
    {addr : BitVec 64} {len : Nat} (h : Memory.MemWritable s addr len)
    (ha : AgreesExcept cs s t) : Memory.MemWritable t addr len :=
  ⟨h.low, fun i hi ↦ ha.grow _ (h.bytes i hi), h.tables⟩

private theorem read_memory_of_agrees {s t : RamState} {cs : List Component}
    (h : AgreesExcept cs s t) {address : BitVec 64} {n : Nat}
    (ha : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (address + BitVec.ofNat 64 i)) :
    (Operand.mem address : Operand n).read t = (Operand.mem address : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[address + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[address + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte (ha i hi)]

theorem ProloguePre.apart_input {s : RamState} (h : ProloguePre s)
    (back offset : BitVec 64) (hb : back.toNat ≤ 184) (hback : 8 ≤ back.toNat)
    (hoff : offset.toNat + 4 ≤ 16) :
    RangeApart (stackPtr s - back) 8
      ((Operand.reg 7 : Operand 64).read s + offset) 4 := by
  have hp := MemoryRoutines.rangeApart_slice_left h.apart (184 - back.toNat) 8 (by omega)
  have he : stackPtr s - 184 + BitVec.ofNat 64 (184 - back.toNat) =
      stackPtr s - back := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 184 back.toNat (by omega) hb,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [BitVec.sub_eq_add_neg (184#64), ← BitVec.add_assoc, BitVec.sub_add_cancel,
      ← BitVec.sub_eq_add_neg]
  rw [he] at hp
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    MemoryRoutines.rangeApart_slice_right hp offset.toNat 4 hoff

private theorem input_not_covers {s : RamState} (h : ProloguePre s)
    (back offset : BitVec 64) (hb : back.toNat ≤ 184) (hback : 8 ≤ back.toNat)
    (hoff : offset.toNat + 4 ≤ 16) (j : Nat) (hj : j < 4) :
    ¬ (Component.mem (stackPtr s - back) 8).Covers
      ((Operand.reg 7 : Operand 64).read s + offset + BitVec.ofNat 64 j) := by
  rintro ⟨i, hi, he⟩
  exact h.apart_input back offset hb hback hoff i hi j hj he.symm

private theorem slot_not_covers (base a b : BitVec 64)
    (h : OffsetsApart (-a) 8 (-b) 8)
    (j : Nat) (hj : j < 8) :
    ¬ (Component.mem (base - a) 8).Covers
      (base - b + BitVec.ofNat 64 j) := by
  rintro ⟨i, hi, he⟩
  exact h.ne base hi hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using he.symm)

private theorem prologue_instruction_code {s : RamState}
    (h : CodeIn Extracted.programImage s) (offset count : Nat) (bytes : List UInt8)
    (he : Extracted.textBytes.toListFrom (0x1ba9 + offset) count = bytes)
    (hsize : 0x1ba9 + offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (0x101ba9 + BitVec.ofNat 64 offset) bytes) s := by
  have hc := program_text_slice h (0x1ba9 + offset) count hsize
  simpa only [he, BitVec.ofNat_add, Extracted.textAddress, ← BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hc

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
theorem compression_prologue [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    AdvancesBlock boundary ProloguePre Extracted.programImage prologueEffect := by
  have hPush0 : StepEffect (PushPre 0x101ba9) (codeRange 0x101ba9 [0x55])
      (pushR64Effect 0x101ba9 1 5) := by
    have hr : gprNumber 0 0
        (opcodeReg 0x55) = 5 := by decide +kernel
    simpa only [hr] using push_r64_effect_step 0x101ba9 0x55
      (by decide)
  have hPush1 : StepEffect (PushPre (0x101ba9 + 1)) (codeRange (0x101ba9 + 1) [0x41, 0x57])
      (pushR64Effect (0x101ba9 + 1) 2 15) := by
    have hr : gprNumber 0 (rexB (0x41 : UInt8).toBitVec)
        (opcodeReg 0x57) = 15 := by decide +kernel
    simpa only [hr] using push_r64_rex_effect_step (0x101ba9 + 1) 0x41 0x57
      (by unfold RexPrefix; decide) (by decide)
  have hPush2 : StepEffect (PushPre (0x101ba9 + 3)) (codeRange (0x101ba9 + 3) [0x41, 0x56])
      (pushR64Effect (0x101ba9 + 3) 2 14) := by
    have hr : gprNumber 0 (rexB (0x41 : UInt8).toBitVec)
        (opcodeReg 0x56) = 14 := by decide +kernel
    simpa only [hr] using push_r64_rex_effect_step (0x101ba9 + 3) 0x41 0x56
      (by unfold RexPrefix; decide) (by decide)
  have hPush3 : StepEffect (PushPre (0x101ba9 + 5)) (codeRange (0x101ba9 + 5) [0x41, 0x55])
      (pushR64Effect (0x101ba9 + 5) 2 13) := by
    have hr : gprNumber 0 (rexB (0x41 : UInt8).toBitVec)
        (opcodeReg 0x55) = 13 := by decide +kernel
    simpa only [hr] using push_r64_rex_effect_step (0x101ba9 + 5) 0x41 0x55
      (by unfold RexPrefix; decide) (by decide)
  have hPush4 : StepEffect (PushPre (0x101ba9 + 7)) (codeRange (0x101ba9 + 7) [0x41, 0x54])
      (pushR64Effect (0x101ba9 + 7) 2 12) := by
    have hr : gprNumber 0 (rexB (0x41 : UInt8).toBitVec)
        (opcodeReg 0x54) = 12 := by decide +kernel
    simpa only [hr] using push_r64_rex_effect_step (0x101ba9 + 7) 0x41 0x54
      (by unfold RexPrefix; decide) (by decide)
  have hPush5 : StepEffect (PushPre (0x101ba9 + 9)) (codeRange (0x101ba9 + 9) [0x53])
      (pushR64Effect (0x101ba9 + 9) 1 3) := by
    have hr : gprNumber 0 0
        (opcodeReg 0x53) = 3 := by decide +kernel
    simpa only [hr] using push_r64_effect_step (0x101ba9 + 9) 0x53
      (by decide)
  have hSub : StepEffect (fun s ↦ s.RIP = 0x101ba9 + 10)
      (codeRange (0x101ba9 + 10) [0x48, 0x81, 0xec, 0x88, 0x00, 0x00, 0x00])
      (subR64Imm32Effect (0x101ba9 + 10) 4 136) :=
    sub_r64_imm32_effect_step _ 0x48 0xec 136 (by unfold RexWPrefix; decide)
      (by decide) (by decide)
  have hMov : StepEffect (fun s ↦ s.RIP = 0x101ba9 + 17)
      (codeRange (0x101ba9 + 17) [0x48, 0x89, 0xd0])
      (movR64R64Effect (0x101ba9 + 17) 0 2) :=
    mov_r64_r64_effect_step _ 0x48 0xd0 (by unfold RexWPrefix; decide) (by decide)
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x101ba9 + 24)
      (codeRange (0x101ba9 + 24) [0x48, 0x01, 0xf0])
      (addR64R64Effect (0x101ba9 + 24) 0 6) :=
    add_r64_r64_effect_step _ 0x48 0xf0 (by unfold RexWPrefix; decide) (by decide)
  have hStoreEnd : StepEffect
      (Memory.StorePre (0x101ba9 + 27) 5
        (storeAddrAt (0x101ba9 + 27) (.sib 4 none 0 (.d8 104)) 5) 8)
      (codeRange (0x101ba9 + 27) [0x48, 0x89, 0x44, 0x24, 0x68])
      (movM64R64Effect (0x101ba9 + 27) 0 (.sib 4 none 0 (.d8 104))) := by
    have ht : (AddrMode.sib 4 none 0 (.d8 104)).tail = [0x24, 104] := by decide +kernel
    have hm : (AddrMode.sib 4 none 0 (.d8 104)).modrm 0 = 68 := by decide +kernel
    have hr : gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 0 = 0 := by decide +kernel
    simpa only [ht, hm, hr, List.length_cons, List.length_nil, Nat.reduceAdd] using
      Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step (0x101ba9 + 27) 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 104))
        ⟨by decide, fun h ↦ by cases h⟩ rfl rfl
  have hLoadA : StepEffect
      (LoadPre (0x101ba9 + 32)
        (fun s ↦ (.base 7 .none : AddrMode).addr s (0x101ba9 + 34)) 4)
      (codeRange (0x101ba9 + 32) [0x8b, 0x0f])
      (Rounds.movR32M32NoRexEffect (0x101ba9 + 32) 1 (.base 7 .none)) :=
    Rounds.mov_r32_m32_noRex_effect_step _ 1 (.base 7 .none) (by decide) rfl rfl
  have hLoadB : StepEffect
      (LoadPre (0x101ba9 + 34)
        (fun s ↦ (.base 7 (.d8 4) : AddrMode).addr s (0x101ba9 + 38)) 4)
      (codeRange (0x101ba9 + 34) [0x44, 0x8b, 0x47, 0x04])
      (movR32M32Effect (0x101ba9 + 34) 8 (.base 7 (.d8 4))) :=
    mov_r32_m32_effect_step _ 0x44 (by unfold RexNoWPrefix; decide)
      0 (.base 7 (.d8 4)) (by decide) rfl rfl
  have hLoadC : StepEffect
      (LoadPre (0x101ba9 + 38)
        (fun s ↦ (.base 7 (.d8 8) : AddrMode).addr s (0x101ba9 + 41)) 4)
      (codeRange (0x101ba9 + 38) [0x8b, 0x57, 0x08])
      (Rounds.movR32M32NoRexEffect (0x101ba9 + 38) 2 (.base 7 (.d8 8))) :=
    Rounds.mov_r32_m32_noRex_effect_step _ 2 (.base 7 (.d8 8)) (by decide) rfl rfl
  have hStoreOutput : StepEffect
      (Memory.StorePre (0x101ba9 + 41) 5
        (storeAddrAt (0x101ba9 + 41) (.sib 4 none 0 (.d8 96)) 5) 8)
      (codeRange (0x101ba9 + 41) [0x48, 0x89, 0x7c, 0x24, 0x60])
      (movM64R64Effect (0x101ba9 + 41) 7 (.sib 4 none 0 (.d8 96))) := by
    have ht : (AddrMode.sib 4 none 0 (.d8 96)).tail = [0x24, 96] := by decide +kernel
    have hm : (AddrMode.sib 4 none 0 (.d8 96)).modrm 7 = 124 := by decide +kernel
    have hr : gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 7 = 7 := by decide +kernel
    simpa only [ht, hm, hr, List.length_cons, List.length_nil, Nat.reduceAdd] using
      Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step (0x101ba9 + 41) 0x48
        (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 96))
        ⟨by decide, fun h ↦ by cases h⟩ rfl rfl
  have hLoadD : StepEffect
      (LoadPre (0x101ba9 + 46)
        (fun s ↦ (.base 7 (.d8 12) : AddrMode).addr s (0x101ba9 + 49)) 4)
      (codeRange (0x101ba9 + 46) [0x8b, 0x47, 0x0c])
      (Rounds.movR32M32NoRexEffect (0x101ba9 + 46) 0 (.base 7 (.d8 12))) :=
    Rounds.mov_r32_m32_noRex_effect_step _ 0 (.base 7 (.d8 12)) (by decide) rfl rfl
  have hShl := shl_rax_six_effect_step (0x101ba9 + 20)
  have hNop := nop_66_sib_disp8_effect_step (0x101ba9 + 49)
  intro s hReady hCode hPre
  have G0 : AgreesExcept [] s s := AgreesExcept.refl [] s
  have sp0 : stackPtr s = stackPtr s - (0 : BitVec 64) := by simp
  have addr0 : pushAddr s = stackPtr s - 8 := rfl
  have pre0 : PushPre (0x101ba9 + 0) s := by
    refine ⟨hPre.rip, ?_⟩
    rw [addr0]
    exact writable_of_agrees (hPre.writable 8 8 (by decide) (by decide)) G0
  have code0 : CodeIn (codeRange (0x101ba9 + 0) [0x55]) s :=
    prologue_instruction_code hCode 0 1 [0x55] (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, a0, r1, e0⟩ := hPush0.advances hReady code0 pre0
    (by
      change (0x101ba9 + 1 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g0 : AgreesExcept [.reg 4, .mem (stackPtr s - 8) 8, .rip] s t1 := by
    simpa only [pushR64Effect_components, addr0] using e0.agrees
  have c1 : CodeIn Extracted.programImage t1 := by
    apply CodeIn.of_agreesExcept g0 ?_ hCode
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hPre.avoids_mem 8 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G1 := G0.trans g0
  have sp1 : stackPtr t1 = stackPtr s - 8 := by
    have hh := e0.writes.1
    change stackPtr t1 = pushAddr s at hh
    exact hh.trans addr0
  have save0 : (Operand.mem (stackPtr s - 8) : Operand 64).read t1 =
      (Operand.reg 5 : Operand 64).read s := by
    have hh := e0.writes.2
    change (Operand.mem (pushAddr s) : Operand 64).read t1 =
      (Operand.reg 5 : Operand 64).read s at hh
    rw [addr0] at hh
    exact hh.trans (G0.read (by simp))
  have addr1 : pushAddr t1 = stackPtr s - 16 := by
    simp only [pushAddr, sp1, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd]
  have pre1 : PushPre (0x101ba9 + 1) t1 := by
    refine ⟨e0.rip, ?_⟩
    rw [addr1]
    exact writable_of_agrees (hPre.writable 16 8 (by decide) (by decide)) G1
  have code1 : CodeIn (codeRange (0x101ba9 + 1) [0x41, 0x57]) t1 :=
    prologue_instruction_code c1 1 2 [0x41, 0x57] (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, a1, r2, e1⟩ := hPush1.advances r1 code1 pre1
    (by
      change (0x101ba9 + 3 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g1 : AgreesExcept [.reg 4, .mem (stackPtr s - 16) 8, .rip] t1 t2 := by
    simpa only [pushR64Effect_components, addr1] using e1.agrees
  have c2 : CodeIn Extracted.programImage t2 := by
    apply CodeIn.of_agreesExcept g1 ?_ c1
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hPre.avoids_mem 16 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G2 := G1.trans g1
  have sp2 : stackPtr t2 = stackPtr s - 16 := by
    have hh := e1.writes.1
    change stackPtr t2 = pushAddr t1 at hh
    exact hh.trans addr1
  have save1 : (Operand.mem (stackPtr s - 16) : Operand 64).read t2 =
      (Operand.reg 15 : Operand 64).read s := by
    have hh := e1.writes.2
    change (Operand.mem (pushAddr t1) : Operand 64).read t2 = (Operand.reg 15 : Operand 64).read t1
      at hh
    rw [addr1] at hh
    exact hh.trans (G1.read (by simp))
  have addr2 : pushAddr t2 = stackPtr s - 24 := by
    simp only [pushAddr, sp2, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd]
  have pre2 : PushPre (0x101ba9 + 3) t2 := by
    refine ⟨e1.rip, ?_⟩
    rw [addr2]
    exact writable_of_agrees (hPre.writable 24 8 (by decide) (by decide)) G2
  have code2 : CodeIn (codeRange (0x101ba9 + 3) [0x41, 0x56]) t2 :=
    prologue_instruction_code c2 3 2 [0x41, 0x56] (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, a2, r3, e2⟩ := hPush2.advances r2 code2 pre2
    (by
      change (0x101ba9 + 5 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g2 : AgreesExcept [.reg 4, .mem (stackPtr s - 24) 8, .rip] t2 t3 := by
    simpa only [pushR64Effect_components, addr2] using e2.agrees
  have c3 : CodeIn Extracted.programImage t3 := by
    apply CodeIn.of_agreesExcept g2 ?_ c2
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hPre.avoids_mem 24 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G3 := G2.trans g2
  have sp3 : stackPtr t3 = stackPtr s - 24 := by
    have hh := e2.writes.1
    change stackPtr t3 = pushAddr t2 at hh
    exact hh.trans addr2
  have save2 : (Operand.mem (stackPtr s - 24) : Operand 64).read t3 =
      (Operand.reg 14 : Operand 64).read s := by
    have hh := e2.writes.2
    change (Operand.mem (pushAddr t2) : Operand 64).read t3 = (Operand.reg 14 : Operand 64).read t2
      at hh
    rw [addr2] at hh
    exact hh.trans (G2.read (by simp))
  have addr3 : pushAddr t3 = stackPtr s - 32 := by
    simp only [pushAddr, sp3, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd]
  have pre3 : PushPre (0x101ba9 + 5) t3 := by
    refine ⟨e2.rip, ?_⟩
    rw [addr3]
    exact writable_of_agrees (hPre.writable 32 8 (by decide) (by decide)) G3
  have code3 : CodeIn (codeRange (0x101ba9 + 5) [0x41, 0x55]) t3 :=
    prologue_instruction_code c3 5 2 [0x41, 0x55] (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, a3, r4, e3⟩ := hPush3.advances r3 code3 pre3
    (by
      change (0x101ba9 + 7 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g3 : AgreesExcept [.reg 4, .mem (stackPtr s - 32) 8, .rip] t3 t4 := by
    simpa only [pushR64Effect_components, addr3] using e3.agrees
  have c4 : CodeIn Extracted.programImage t4 := by
    apply CodeIn.of_agreesExcept g3 ?_ c3
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hPre.avoids_mem 32 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G4 := G3.trans g3
  have sp4 : stackPtr t4 = stackPtr s - 32 := by
    have hh := e3.writes.1
    change stackPtr t4 = pushAddr t3 at hh
    exact hh.trans addr3
  have save3 : (Operand.mem (stackPtr s - 32) : Operand 64).read t4 =
      (Operand.reg 13 : Operand 64).read s := by
    have hh := e3.writes.2
    change (Operand.mem (pushAddr t3) : Operand 64).read t4 = (Operand.reg 13 : Operand 64).read t3
      at hh
    rw [addr3] at hh
    exact hh.trans (G3.read (by simp))
  have addr4 : pushAddr t4 = stackPtr s - 40 := by
    simp only [pushAddr, sp4, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd]
  have pre4 : PushPre (0x101ba9 + 7) t4 := by
    refine ⟨e3.rip, ?_⟩
    rw [addr4]
    exact writable_of_agrees (hPre.writable 40 8 (by decide) (by decide)) G4
  have code4 : CodeIn (codeRange (0x101ba9 + 7) [0x41, 0x54]) t4 :=
    prologue_instruction_code c4 7 2 [0x41, 0x54] (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, a4, r5, e4⟩ := hPush4.advances r4 code4 pre4
    (by
      change (0x101ba9 + 9 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g4 : AgreesExcept [.reg 4, .mem (stackPtr s - 40) 8, .rip] t4 t5 := by
    simpa only [pushR64Effect_components, addr4] using e4.agrees
  have c5 : CodeIn Extracted.programImage t5 := by
    apply CodeIn.of_agreesExcept g4 ?_ c4
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hPre.avoids_mem 40 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G5 := G4.trans g4
  have sp5 : stackPtr t5 = stackPtr s - 40 := by
    have hh := e4.writes.1
    change stackPtr t5 = pushAddr t4 at hh
    exact hh.trans addr4
  have save4 : (Operand.mem (stackPtr s - 40) : Operand 64).read t5 =
      (Operand.reg 12 : Operand 64).read s := by
    have hh := e4.writes.2
    change (Operand.mem (pushAddr t4) : Operand 64).read t5 = (Operand.reg 12 : Operand 64).read t4
      at hh
    rw [addr4] at hh
    exact hh.trans (G4.read (by simp))
  have addr5 : pushAddr t5 = stackPtr s - 48 := by
    simp only [pushAddr, sp5, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd]
  have pre5 : PushPre (0x101ba9 + 9) t5 := by
    refine ⟨e4.rip, ?_⟩
    rw [addr5]
    exact writable_of_agrees (hPre.writable 48 8 (by decide) (by decide)) G5
  have code5 : CodeIn (codeRange (0x101ba9 + 9) [0x53]) t5 :=
    prologue_instruction_code c5 9 1 [0x53] (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, a5, r6, e5⟩ := hPush5.advances r5 code5 pre5
    (by
      change (0x101ba9 + 10 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g5 : AgreesExcept [.reg 4, .mem (stackPtr s - 48) 8, .rip] t5 t6 := by
    simpa only [pushR64Effect_components, addr5] using e5.agrees
  have c6 : CodeIn Extracted.programImage t6 := by
    apply CodeIn.of_agreesExcept g5 ?_ c5
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hPre.avoids_mem 48 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G6 := G5.trans g5
  have sp6 : stackPtr t6 = stackPtr s - 48 := by
    have hh := e5.writes.1
    change stackPtr t6 = pushAddr t5 at hh
    exact hh.trans addr5
  have save5 : (Operand.mem (stackPtr s - 48) : Operand 64).read t6 =
      (Operand.reg 3 : Operand 64).read s := by
    have hh := e5.writes.2
    change (Operand.mem (pushAddr t5) : Operand 64).read t6 = (Operand.reg 3 : Operand 64).read t5
      at hh
    rw [addr5] at hh
    exact hh.trans (G5.read (by simp))
  have pre6 : t6.RIP = (0x101ba9 + 10) := e5.rip
  have code6 : CodeIn (codeRange (0x101ba9 + 10) [0x48, 0x81, 0xec, 0x88, 0x0, 0x0, 0x0]) t6 :=
    prologue_instruction_code c6 10 7 [0x48, 0x81, 0xec, 0x88, 0x0, 0x0, 0x0] (by decide +kernel)
      (by decide +kernel)
  obtain ⟨t7, a6, r7, e6⟩ := hSub.advances r6 code6 pre6
    (by
      change (0x101ba9 + 17 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g6 : AgreesExcept [.reg 4, .flags, .rip] t6 t7 := by
    exact e6.agrees
  have c7 : CodeIn Extracted.programImage t7 := by
    apply CodeIn.of_agreesExcept g6 ?_ c6
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hcov
    · exact hcov
  have G7 := G6.trans g6
  have sp7 : stackPtr t7 = stackPtr s - 184 := by
    have hh := e6.writes
    change stackPtr t7 = stackPtr t6 - 136 at hh
    rw [sp6] at hh
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hh
  have pre7 : t7.RIP = (0x101ba9 + 17) := e6.rip
  have code7 : CodeIn (codeRange (0x101ba9 + 17) [0x48, 0x89, 0xd0]) t7 :=
    prologue_instruction_code c7 17 3 [0x48, 0x89, 0xd0] (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, a7, r8, e7⟩ := hMov.advances r7 code7 pre7
    (by
      change (0x101ba9 + 20 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g7 : AgreesExcept [.reg 0, .rip] t7 t8 := by
    exact e7.agrees
  have c8 : CodeIn Extracted.programImage t8 := by
    apply CodeIn.of_agreesExcept g7 ?_ c7
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcov
    · exact hcov
  have G8 := G7.trans g7
  have sp8 : stackPtr t8 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t8 = (Operand.reg 4 : Operand 64).read t7 := g7.read
      (by simp)
    exact hh.trans sp7
  have move : (Operand.reg 0 : Operand 64).read t8 = (Operand.reg 2 : Operand 64).read s := by
    have hh := e7.writes
    change (Operand.reg 0 : Operand 64).read t8 = (Operand.reg 2 : Operand 64).read t7 at hh
    exact hh.trans (G7.read (by simp))
  have pre8 : t8.RIP = (0x101ba9 + 20) := e7.rip
  have code8 : CodeIn (codeRange (0x101ba9 + 20) [0x48, 0xc1, 0xe0, 0x6]) t8 :=
    prologue_instruction_code c8 20 4 [0x48, 0xc1, 0xe0, 0x6] (by decide +kernel) (by
      decide +kernel)
  obtain ⟨t9, a8, r9, e8⟩ := hShl.advances r8 code8 pre8
    (by
      change (0x101ba9 + 24 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g8 : AgreesExcept [.reg 0, .flags, .rip] t8 t9 := by
    exact e8.agrees
  have c9 : CodeIn Extracted.programImage t9 := by
    apply CodeIn.of_agreesExcept g8 ?_ c8
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hcov
    · exact hcov
  have G9 := G8.trans g8
  have sp9 : stackPtr t9 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t9 = (Operand.reg 4 : Operand 64).read t8 := g8.read
      (by simp)
    exact hh.trans sp8
  have shifted : (Operand.reg 0 : Operand 64).read t9 = (Operand.reg 2 : Operand 64).read s <<< 6 :=
    by
    have hh := e8.writes
    change (Operand.reg 0 : Operand 64).read t9 = (Operand.reg 0 : Operand 64).read t8 <<< 6 at hh
    rwa [move] at hh
  have pre9 : t9.RIP = (0x101ba9 + 24) := e8.rip
  have code9 : CodeIn (codeRange (0x101ba9 + 24) [0x48, 0x1, 0xf0]) t9 :=
    prologue_instruction_code c9 24 3 [0x48, 0x1, 0xf0] (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, a9, r10, e9⟩ := hAdd.advances r9 code9 pre9
    (by
      change (0x101ba9 + 27 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g9 : AgreesExcept [.reg 0, .flags, .rip] t9 t10 := by
    exact e9.agrees
  have c10 : CodeIn Extracted.programImage t10 := by
    apply CodeIn.of_agreesExcept g9 ?_ c9
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hcov
    · exact hcov
  have G10 := G9.trans g9
  have sp10 : stackPtr t10 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t10 = (Operand.reg 4 : Operand 64).read t9 :=
      g9.read (by simp)
    exact hh.trans sp9
  have si9 : (Operand.reg 6 : Operand 64).read t9 = (Operand.reg 6 : Operand 64).read s := G9.read
    (by simp)
  have added : (Operand.reg 0 : Operand 64).read t10 = ((Operand.reg 2 : Operand 64).read s <<< 6) +
    (Operand.reg 6 : Operand 64).read s := by
    have hh := e9.writes
    change (Operand.reg 0 : Operand 64).read t10 = (Operand.reg 0 : Operand 64).read t9 +
      (Operand.reg 6 : Operand 64).read t9 at hh
    rwa [shifted, si9] at hh
  have addFlags : (StatusFlagsOutcome.ofStatusFlags
      (addSpec ((Operand.reg 2 : Operand 64).read s <<< 6) ((Operand.reg 6 : Operand 64).read
        s)).2).Allows
      (StatusFlags.ofRFLAGS t10.RFLAGS) := by
    have hh := e9.flags
    change (StatusFlagsOutcome.ofStatusFlags
      (addSpec ((Operand.reg 0 : Operand 64).read t9) ((Operand.reg 6 : Operand 64).read
        t9)).2).Allows _ at hh
    rwa [shifted, si9] at hh
  have addr10 : storeAddrAt (0x101ba9 + 27) (.sib 4 none 0 (.d8 104)) 5 t10 =
      stackPtr s - 80 := by
    change (Operand.reg 4 : Operand 64).read t10 + 104 = _
    rw [← stackPtr_read, sp10]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have pre10 : Memory.StorePre (0x101ba9 + 27) 5
      (storeAddrAt (0x101ba9 + 27) (.sib 4 none 0 (.d8 104)) 5) 8 t10 := by
    refine ⟨e9.rip, ?_, ?_⟩
    · rw [addr10]
      exact writable_of_agrees (hPre.writable 80 8 (by decide) (by decide)) G10
    · rw [addr10]
      exact hPre.apart_instruction 80 8 27 5 (by decide) (by decide) (by decide)
  have code10 : CodeIn (codeRange (0x101ba9 + 27) [0x48, 0x89, 0x44, 0x24, 0x68]) t10 :=
    prologue_instruction_code c10 27 5 [0x48, 0x89, 0x44, 0x24, 0x68] (by decide +kernel) (by
      decide +kernel)
  obtain ⟨t11, a10, r11, e10⟩ := hStoreEnd.advances r10 code10 pre10
    (by
      change (0x101ba9 + 32 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g10 : AgreesExcept [.mem (stackPtr s - 80) 8, .rip] t10 t11 := by
    simpa only [movM64R64Effect_components,
      show (3 + (AddrMode.sib 4 none 0 (.d8 104)).tail.length) = 5 from rfl,
      addr10] using e10.agrees
  have c11 : CodeIn Extracted.programImage t11 := by
    apply CodeIn.of_agreesExcept g10 ?_ c10
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hPre.avoids_mem 80 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G11 := G10.trans g10
  have sp11 : stackPtr t11 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t11 = (Operand.reg 4 : Operand 64).read t10 :=
      g10.read (by simp)
    exact hh.trans sp10
  have stored10 : (Operand.mem (stackPtr s - 80) : Operand 64).read t11 =
      (Operand.reg 0 : Operand 64).read t10 := by
    have hh := e10.writes
    change (Operand.mem (storeAddrAt (0x101ba9 + 27) (.sib 4 none 0 (.d8 104)) 5 t10)
      : Operand 64).read t11 = (Operand.reg 0 : Operand 64).read t10 at hh
    rwa [addr10] at hh
  have di11 : (Operand.reg 7 : Operand 64).read t11 = (Operand.reg 7 : Operand 64).read s :=
    G11.read (by simp)
  have pre11 : LoadPre (0x101ba9 + 32)
      (fun t ↦ (.base 7 .none : AddrMode).addr t ((0x101ba9 + 32) + 2)) 4 t11 := by
    refine ⟨e10.rip, ?_⟩
    change MemReadable t11 ((Operand.reg 7 : Operand 64).read t11 + 0) 4
    rw [di11]
    have hr := MemoryRoutines.memReadable_slice hPre.read 0 4 (by decide)
    exact ⟨hr.low, fun j hj ↦ G11.grow _ (hr.mem j hj)⟩
  have code11 : CodeIn (codeRange (0x101ba9 + 32) [0x8b, 0xf]) t11 :=
    prologue_instruction_code c11 32 2 [0x8b, 0xf] (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, a11, r12, e11⟩ := hLoadA.advances r11 code11 pre11
    (by
      change (0x101ba9 + 34 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g11 : AgreesExcept [.reg 1, .rip] t11 t12 := by
    exact e11.agrees
  have c12 : CodeIn Extracted.programImage t12 := by
    apply CodeIn.of_agreesExcept g11 ?_ c11
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcov
    · exact hcov
  have G12 := G11.trans g11
  have sp12 : stackPtr t12 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t12 = (Operand.reg 4 : Operand 64).read t11 :=
      g11.read (by simp)
    exact hh.trans sp11
  have buf11 : (Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 32).read t11 =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 32).read s := by
    apply read_memory_of_agrees G11
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact input_not_covers hPre _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel) j hj
  have word11 : (Operand.reg 1 : Operand 64).read t12 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 32).read s).setWidth 64 :=
        by
    have hh := e11.writes
    change (Operand.reg 1 : Operand 64).read t12 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read t11 + 0) : Operand 32).read t11).setWidth 64
        at hh
    rwa [di11, buf11] at hh
  have di12 : (Operand.reg 7 : Operand 64).read t12 = (Operand.reg 7 : Operand 64).read s :=
    G12.read (by simp)
  have pre12 : LoadPre (0x101ba9 + 34)
      (fun t ↦ (.base 7 (.d8 4) : AddrMode).addr t ((0x101ba9 + 34) + 4)) 4 t12 := by
    refine ⟨e11.rip, ?_⟩
    change MemReadable t12 ((Operand.reg 7 : Operand 64).read t12 + 4) 4
    rw [di12]
    have hr := MemoryRoutines.memReadable_slice hPre.read 4 4 (by decide)
    exact ⟨hr.low, fun j hj ↦ G12.grow _ (hr.mem j hj)⟩
  have code12 : CodeIn (codeRange (0x101ba9 + 34) [0x44, 0x8b, 0x47, 0x4]) t12 :=
    prologue_instruction_code c12 34 4 [0x44, 0x8b, 0x47, 0x4] (by decide +kernel) (by
      decide +kernel)
  obtain ⟨t13, a12, r13, e12⟩ := hLoadB.advances r12 code12 pre12
    (by
      change (0x101ba9 + 38 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g12 : AgreesExcept [.reg 8, .rip] t12 t13 := by
    exact e12.agrees
  have c13 : CodeIn Extracted.programImage t13 := by
    apply CodeIn.of_agreesExcept g12 ?_ c12
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcov
    · exact hcov
  have G13 := G12.trans g12
  have sp13 : stackPtr t13 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t13 = (Operand.reg 4 : Operand 64).read t12 :=
      g12.read (by simp)
    exact hh.trans sp12
  have buf12 : (Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read t12 =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read s := by
    apply read_memory_of_agrees G12
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact input_not_covers hPre _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel) j hj
  have word12 : (Operand.reg 8 : Operand 64).read t13 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read s).setWidth 64 :=
        by
    have hh := e12.writes
    change (Operand.reg 8 : Operand 64).read t13 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read t12 + 4) : Operand 32).read t12).setWidth 64
        at hh
    rwa [di12, buf12] at hh
  have di13 : (Operand.reg 7 : Operand 64).read t13 = (Operand.reg 7 : Operand 64).read s :=
    G13.read (by simp)
  have pre13 : LoadPre (0x101ba9 + 38)
      (fun t ↦ (.base 7 (.d8 8) : AddrMode).addr t ((0x101ba9 + 38) + 3)) 4 t13 := by
    refine ⟨e12.rip, ?_⟩
    change MemReadable t13 ((Operand.reg 7 : Operand 64).read t13 + 8) 4
    rw [di13]
    have hr := MemoryRoutines.memReadable_slice hPre.read 8 4 (by decide)
    exact ⟨hr.low, fun j hj ↦ G13.grow _ (hr.mem j hj)⟩
  have code13 : CodeIn (codeRange (0x101ba9 + 38) [0x8b, 0x57, 0x8]) t13 :=
    prologue_instruction_code c13 38 3 [0x8b, 0x57, 0x8] (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, a13, r14, e13⟩ := hLoadC.advances r13 code13 pre13
    (by
      change (0x101ba9 + 41 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g13 : AgreesExcept [.reg 2, .rip] t13 t14 := by
    exact e13.agrees
  have c14 : CodeIn Extracted.programImage t14 := by
    apply CodeIn.of_agreesExcept g13 ?_ c13
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcov
    · exact hcov
  have G14 := G13.trans g13
  have sp14 : stackPtr t14 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t14 = (Operand.reg 4 : Operand 64).read t13 :=
      g13.read (by simp)
    exact hh.trans sp13
  have buf13 : (Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read t13 =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read s := by
    apply read_memory_of_agrees G13
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact input_not_covers hPre _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel) j hj
  have word13 : (Operand.reg 2 : Operand 64).read t14 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read s).setWidth 64 :=
        by
    have hh := e13.writes
    change (Operand.reg 2 : Operand 64).read t14 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read t13 + 8) : Operand 32).read t13).setWidth 64
        at hh
    rwa [di13, buf13] at hh
  have addr14 : storeAddrAt (0x101ba9 + 41) (.sib 4 none 0 (.d8 96)) 5 t14 =
      stackPtr s - 88 := by
    change (Operand.reg 4 : Operand 64).read t14 + 96 = _
    rw [← stackPtr_read, sp14]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have pre14 : Memory.StorePre (0x101ba9 + 41) 5
      (storeAddrAt (0x101ba9 + 41) (.sib 4 none 0 (.d8 96)) 5) 8 t14 := by
    refine ⟨e13.rip, ?_, ?_⟩
    · rw [addr14]
      exact writable_of_agrees (hPre.writable 88 8 (by decide) (by decide)) G14
    · rw [addr14]
      exact hPre.apart_instruction 88 8 41 5 (by decide) (by decide) (by decide)
  have code14 : CodeIn (codeRange (0x101ba9 + 41) [0x48, 0x89, 0x7c, 0x24, 0x60]) t14 :=
    prologue_instruction_code c14 41 5 [0x48, 0x89, 0x7c, 0x24, 0x60] (by decide +kernel) (by
      decide +kernel)
  obtain ⟨t15, a14, r15, e14⟩ := hStoreOutput.advances r14 code14 pre14
    (by
      change (0x101ba9 + 46 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g14 : AgreesExcept [.mem (stackPtr s - 88) 8, .rip] t14 t15 := by
    simpa only [movM64R64Effect_components,
      show (3 + (AddrMode.sib 4 none 0 (.d8 96)).tail.length) = 5 from rfl,
      addr14] using e14.agrees
  have c15 : CodeIn Extracted.programImage t15 := by
    apply CodeIn.of_agreesExcept g14 ?_ c14
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hPre.avoids_mem 88 8 (by decide) (by decide) x.1 ⟨x.2, hx⟩ hcov
    · exact hcov
  have G15 := G14.trans g14
  have sp15 : stackPtr t15 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t15 = (Operand.reg 4 : Operand 64).read t14 :=
      g14.read (by simp)
    exact hh.trans sp14
  have stored14 : (Operand.mem (stackPtr s - 88) : Operand 64).read t15 =
      (Operand.reg 7 : Operand 64).read t14 := by
    have hh := e14.writes
    change (Operand.mem (storeAddrAt (0x101ba9 + 41) (.sib 4 none 0 (.d8 96)) 5 t14)
      : Operand 64).read t15 = (Operand.reg 7 : Operand 64).read t14 at hh
    rwa [addr14] at hh
  have di15 : (Operand.reg 7 : Operand 64).read t15 = (Operand.reg 7 : Operand 64).read s :=
    G15.read (by simp)
  have pre15 : LoadPre (0x101ba9 + 46)
      (fun t ↦ (.base 7 (.d8 12) : AddrMode).addr t ((0x101ba9 + 46) + 3)) 4 t15 := by
    refine ⟨e14.rip, ?_⟩
    change MemReadable t15 ((Operand.reg 7 : Operand 64).read t15 + 12) 4
    rw [di15]
    have hr := MemoryRoutines.memReadable_slice hPre.read 12 4 (by decide)
    exact ⟨hr.low, fun j hj ↦ G15.grow _ (hr.mem j hj)⟩
  have code15 : CodeIn (codeRange (0x101ba9 + 46) [0x8b, 0x47, 0xc]) t15 :=
    prologue_instruction_code c15 46 3 [0x8b, 0x47, 0xc] (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, a15, r16, e15⟩ := hLoadD.advances r15 code15 pre15
    (by
      change (0x101ba9 + 49 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g15 : AgreesExcept [.reg 0, .rip] t15 t16 := by
    exact e15.agrees
  have c16 : CodeIn Extracted.programImage t16 := by
    apply CodeIn.of_agreesExcept g15 ?_ c15
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcov
    · exact hcov
  have G16 := G15.trans g15
  have sp16 : stackPtr t16 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t16 = (Operand.reg 4 : Operand 64).read t15 :=
      g15.read (by simp)
    exact hh.trans sp15
  have buf15 : (Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read t15 =
      (Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read s := by
    apply read_memory_of_agrees G15
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact input_not_covers hPre _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel) j hj
  have word15 : (Operand.reg 0 : Operand 64).read t16 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read s).setWidth 64 :=
        by
    have hh := e15.writes
    change (Operand.reg 0 : Operand 64).read t16 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read t15 + 12) : Operand 32).read t15).setWidth 64
        at hh
    rwa [di15, buf15] at hh
  have pre16 : t16.RIP = (0x101ba9 + 49) := e15.rip
  have code16 : CodeIn (codeRange (0x101ba9 + 49) [0x66, 0xf, 0x1f, 0x44, 0x0, 0x0]) t16 :=
    prologue_instruction_code c16 49 6 [0x66, 0xf, 0x1f, 0x44, 0x0, 0x0] (by decide +kernel) (by
      decide +kernel)
  obtain ⟨t17, a16, r17, e16⟩ := hNop.advances r16 code16 pre16
    (by
      change (0x101ba9 + 55 : BitVec 64) ≠ boundary.rip
      exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have g16 : AgreesExcept [.rip] t16 t17 := by
    exact e16.agrees
  have c17 : CodeIn Extracted.programImage t17 := by
    apply CodeIn.of_agreesExcept g16 ?_ c16
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    · exact hcov
  have G17 := G16.trans g16
  have sp17 : stackPtr t17 = stackPtr s - 184 := by
    have hh : (Operand.reg 4 : Operand 64).read t17 = (Operand.reg 4 : Operand 64).read t16 :=
      g16.read (by simp)
    exact hh.trans sp16
  have memKeep0 : (Operand.mem (stackPtr s - 8) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 8) : Operand 64).read t1 := by
    apply read_memory_of_agrees ((((((((((((((((g1).trans g2).trans g3).trans g4).trans g5).trans
      g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans
      g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have saved0 : (Operand.mem (stackPtr s - 8) : Operand 64).read t17 =
      (Operand.reg 5 : Operand 64).read s := memKeep0.trans save0
  have memKeep1 : (Operand.mem (stackPtr s - 16) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 16) : Operand 64).read t2 := by
    apply read_memory_of_agrees (((((((((((((((g2).trans g3).trans g4).trans g5).trans g6).trans
      g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans
      g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have saved1 : (Operand.mem (stackPtr s - 16) : Operand 64).read t17 =
      (Operand.reg 15 : Operand 64).read s := memKeep1.trans save1
  have memKeep2 : (Operand.mem (stackPtr s - 24) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 24) : Operand 64).read t3 := by
    apply read_memory_of_agrees ((((((((((((((g3).trans g4).trans g5).trans g6).trans g7).trans
      g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have saved2 : (Operand.mem (stackPtr s - 24) : Operand 64).read t17 =
      (Operand.reg 14 : Operand 64).read s := memKeep2.trans save2
  have memKeep3 : (Operand.mem (stackPtr s - 32) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 32) : Operand 64).read t4 := by
    apply read_memory_of_agrees (((((((((((((g4).trans g5).trans g6).trans g7).trans g8).trans
      g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have saved3 : (Operand.mem (stackPtr s - 32) : Operand 64).read t17 =
      (Operand.reg 13 : Operand 64).read s := memKeep3.trans save3
  have memKeep4 : (Operand.mem (stackPtr s - 40) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 40) : Operand 64).read t5 := by
    apply read_memory_of_agrees ((((((((((((g5).trans g6).trans g7).trans g8).trans g9).trans
      g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have saved4 : (Operand.mem (stackPtr s - 40) : Operand 64).read t17 =
      (Operand.reg 12 : Operand 64).read s := memKeep4.trans save4
  have memKeep5 : (Operand.mem (stackPtr s - 48) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 48) : Operand 64).read t6 := by
    apply read_memory_of_agrees (((((((((((g6).trans g7).trans g8).trans g9).trans g10).trans
      g11).trans g12).trans g13).trans g14).trans g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have saved5 : (Operand.mem (stackPtr s - 48) : Operand 64).read t17 =
      (Operand.reg 3 : Operand 64).read s := memKeep5.trans save5
  have memKeep10 : (Operand.mem (stackPtr s - 80) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 80) : Operand 64).read t11 := by
    apply read_memory_of_agrees ((((((g11).trans g12).trans g13).trans g14).trans g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have endPointer : (Operand.mem (stackPtr s - 80) : Operand 64).read t17 =
      ((Operand.reg 2 : Operand 64).read s <<< 6) + (Operand.reg 6 : Operand 64).read s :=
    memKeep10.trans (stored10.trans added)
  have memKeep14 : (Operand.mem (stackPtr s - 88) : Operand 64).read t17 =
      (Operand.mem (stackPtr s - 88) : Operand 64).read t15 := by
    apply read_memory_of_agrees ((g15).trans g16)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl
    all_goals first
      | exact fun hh ↦ hh
      | exact slot_not_covers (stackPtr s) _ _ (by unfold OffsetsApart; decide +kernel) j hj
  have outputPointer : (Operand.mem (stackPtr s - 88) : Operand 64).read t17 =
      (Operand.reg 7 : Operand 64).read s := memKeep14.trans (stored14.trans (G14.read (by simp)))
  have finalWord11 : (Operand.reg 1 : Operand 64).read t17 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 32).read s).setWidth 64 :=
    ((((((g12).trans g13).trans g14).trans g15).trans g16).read (by simp)).trans word11
  have finalWord12 : (Operand.reg 8 : Operand 64).read t17 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read s).setWidth 64 :=
    (((((g13).trans g14).trans g15).trans g16).read (by simp)).trans word12
  have finalWord13 : (Operand.reg 2 : Operand 64).read t17 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read s).setWidth 64 :=
    ((((g14).trans g15).trans g16).read (by simp)).trans word13
  have finalWord15 : (Operand.reg 0 : Operand 64).read t17 =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read s).setWidth 64 :=
    ((g16).read (by simp)).trans word15
  have flagsKeep : t17.RFLAGS = t10.RFLAGS := (((((((g10).trans g11).trans g12).trans g13).trans
    g14).trans g15).trans g16).rflags (by simp) (by simp)
  refine ⟨17, t17, ?_, r17, c17, ?_⟩
  · simpa only [Nat.reduceAdd] using ((((((((((((((((a0).trans a1).trans a2).trans a3).trans
    a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans
    a13).trans a14).trans a15).trans a16
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact e16.rip
    · change
        (Operand.mem (stackPtr s - 8) : Operand 64).read t17 =
          (Operand.reg 5 : Operand 64).read s ∧
        (Operand.mem (stackPtr s - 16) : Operand 64).read t17 =
          (Operand.reg 15 : Operand 64).read s ∧
        (Operand.mem (stackPtr s - 24) : Operand 64).read t17 =
          (Operand.reg 14 : Operand 64).read s ∧
        (Operand.mem (stackPtr s - 32) : Operand 64).read t17 =
          (Operand.reg 13 : Operand 64).read s ∧
        (Operand.mem (stackPtr s - 40) : Operand 64).read t17 =
          (Operand.reg 12 : Operand 64).read s ∧
        (Operand.mem (stackPtr s - 48) : Operand 64).read t17 =
          (Operand.reg 3 : Operand 64).read s ∧
        stackPtr t17 = stackPtr s - 184 ∧
        (Operand.mem (stackPtr s - 80) : Operand 64).read t17 =
          ((Operand.reg 2 : Operand 64).read s <<< 6) + (Operand.reg 6 : Operand 64).read s ∧
        (Operand.reg 1 : Operand 64).read t17 =
          ((Operand.mem ((Operand.reg 7 : Operand 64).read s) : Operand 32).read s).setWidth 64 ∧
        (Operand.reg 8 : Operand 64).read t17 =
          ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read s).setWidth 64
            ∧
        (Operand.reg 2 : Operand 64).read t17 =
          ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read s).setWidth 64
            ∧
        (Operand.mem (stackPtr s - 88) : Operand 64).read t17 =
          (Operand.reg 7 : Operand 64).read s ∧
        (Operand.reg 0 : Operand 64).read t17 =
          ((Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read s).setWidth 64
      refine ⟨saved0, saved1, saved2, saved3, saved4, saved5, sp17, endPointer, ?_,
        finalWord12, finalWord13, outputPointer, finalWord15⟩
      simpa only [show (Operand.reg 7 : Operand 64).read s + (0 : BitVec 64) =
        (Operand.reg 7 : Operand 64).read s from BitVec.add_zero _] using finalWord11
    · change (StatusFlagsOutcome.ofStatusFlags
        (addSpec ((Operand.reg 2 : Operand 64).read s <<< 6)
          ((Operand.reg 6 : Operand 64).read s)).2).Allows (StatusFlags.ofRFLAGS t17.RFLAGS)
      rwa [flagsKeep]
    · apply G17.mono
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or,
        or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [prologueEffect, Effect.components]


theorem prologueEffect_rsp {s t : RamState} (h : (prologueEffect s).Holds s t) :
    stackPtr t = stackPtr s - 184 := by
  change (Operand.reg 4 : Operand 64).read t = _
  exact Write.allHold_iff.mp h.writes
    ⟨(.reg 4 : Operand 64), stackPtr s - 184⟩ (by simp [prologueEffect])

theorem prologueEffect_rsi {s t : RamState} (h : (prologueEffect s).Holds s t) :
    (Operand.reg 6 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s :=
  h.agrees.read (by simp [prologueEffect, Effect.components])

theorem prologueEffect_saved {s t : RamState} (h : (prologueEffect s).Holds s t)
    (i : Fin 6) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 (136 + 8 * i.val)) : Operand 64).read t =
      (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read s := by
  rw [prologueEffect_rsp h]
  refine Write.allHold_iff.mp h.writes
    ⟨(.mem (stackPtr s - 184 + BitVec.ofNat 64 (136 + 8 * i.val)) : Operand 64),
      (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read s⟩ ?_
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    have := i.isLt
    omega
  rcases hi with hi | hi | hi | hi | hi | hi <;>
    simp [prologueEffect, hi, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem prologueEffect_words {s t : RamState} (h : (prologueEffect s).Holds s t)
    (i : Fin 4) :
    (Operand.reg (#[1, 8, 2, 0] : Array (BitVec 5))[i.val]! : Operand 64).read t =
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 (4 * i.val))
        : Operand 32).read s).setWidth 64 := by
  refine Write.allHold_iff.mp h.writes
    ⟨(.reg (#[1, 8, 2, 0] : Array (BitVec 5))[i.val]! : Operand 64),
      ((Operand.mem ((Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 (4 * i.val))
        : Operand 32).read s).setWidth 64⟩ ?_
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
    have := i.isLt
    omega
  rcases hi with hi | hi | hi | hi
  · simp only [hi, Nat.mul_zero, BitVec.add_zero]
    simp [prologueEffect]
  all_goals simp [prologueEffect, hi]

theorem prologueEffect_output_pointer {s t : RamState} (h : (prologueEffect s).Holds s t) :
    (Operand.mem (stackPtr t + 96) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s := by
  rw [prologueEffect_rsp h]
  have hw : (Operand.mem (stackPtr s - 88) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s :=
    Write.allHold_iff.mp h.writes
      ⟨(.mem (stackPtr s - 88) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩
      (by simp [prologueEffect])
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hw

theorem prologueEffect_end_pointer {s t : RamState} (h : (prologueEffect s).Holds s t) :
    (Operand.mem (stackPtr t + 104) : Operand 64).read t =
      (Operand.reg 6 : Operand 64).read s + ((Operand.reg 2 : Operand 64).read s <<< 6) := by
  rw [prologueEffect_rsp h]
  have hw : (Operand.mem (stackPtr s - 80) : Operand 64).read t =
      ((Operand.reg 2 : Operand 64).read s <<< 6) + (Operand.reg 6 : Operand 64).read s :=
    Write.allHold_iff.mp h.writes
      ⟨(.mem (stackPtr s - 80) : Operand 64),
        ((Operand.reg 2 : Operand 64).read s <<< 6) + (Operand.reg 6 : Operand 64).read s⟩
      (by simp [prologueEffect])
  have hc := hw.trans (BitVec.add_comm _ _)
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hc

end Md5.Proofs.Block
