import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.Callee100a80.Defs
import ChaCha20Poly1305.Proofs.Callee100a80.Run
import X86Proofs.Program.Execution
import X86Proofs.Program.Agrees
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Step.ReadyToStep
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Region
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple

namespace ChaCha20Poly1305.Proofs.Callee100a80

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305

theorem mem_read_congr {t u : RamState} (he : u.external = t.external) (a : BitVec 64) :
    (Operand.mem a : Operand 64).read u = (Operand.mem a : Operand 64).read t := by
  change memLoad u.external a 64 = memLoad t.external a 64
  rw [he]

theorem frame_readable [Bindings] {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {cs : List Component}
    (ha : AgreesExcept cs s t) (off : Nat) (h8 : 8 ≤ off) (hoff : off ≤ frameBytes) :
    MemReadable t (stackPtr s - BitVec.ofNat 64 off) 8 := by
  have hsl := h.stack.low
  have hlow := h.stackLow
  simp only [stackRegion, frameBytes] at hsl hlow hoff
  have hx : (stackPtr s - BitVec.ofNat 64 off).toNat = (stackPtr s).toNat - off := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, fun i hi ↦ ha.grow _ ?_⟩
  have hp := h.stack.present (frameBytes - off + i) (by simp only [stackRegion, frameBytes]; omega)
  have he : BitVec.ofNat 64 ((stackRegion s).start + (frameBytes - off + i)) =
      stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [stackRegion, frameBytes]
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rwa [he] at hp

theorem epilogue_add [Bindings] {t : RamState} (hr : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t) (hip : t.RIP = 0x1014aa)
    (boundary : ReturnBoundary) (hne : (0x1014b1 : BitVec 64) ≠ boundary.rip) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (addR64Imm32Effect 0x1014aa 4 0x170 t).Holds t u := by
  have hcode : CodeIn (codeRange 0x1014aa (0x48 :: 0x81 :: 0xc4 :: immBytes 32 0x170)) t :=
    MemoryRoutines.Machine.program_text_slice hc 0x14aa 7 (by decide +kernel)
  exact (add_r64_imm32_effect_step 0x1014aa 0x48 0xc4 0x170 (by unfold RexWPrefix; decide) (by decide)
    (by decide)).advances hr hcode hip hne

theorem reg_agrees {s t : RamState} {r : BitVec 5}
    (h : (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s) :
    (Component.reg r).Agrees s t := by
  simpa [Operand.read, Component.Agrees] using h

theorem pop_frame_step [Bindings] {t : RamState} {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} {dst : BitVec 5}
    (hstep : StepEffect (PopPre p) (codeRange p bytes) (popR64Effect p len dst))
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (hcode : CodeIn (codeRange p bytes) t) (hip : t.RIP = p)
    (hread : MemReadable t (stackPtr t) 8) (boundary : ReturnBoundary)
    (hne : p + BitVec.ofNat 64 len ≠ boundary.rip) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = p + BitVec.ofNat 64 len ∧
      (Operand.reg dst : Operand 64).read u = (Operand.mem (stackPtr t) : Operand 64).read t ∧
      stackPtr u = stackPtr t + 8 ∧ u.external = t.external ∧
      AgreesExcept [.reg dst, .reg 4, .rip] t u := by
  obtain ⟨u, ha, hr', he⟩ := hstep.advances hr hcode ⟨hip, hread⟩ hne
  exact ⟨u, ha, hr', he.codeIn (popR64Effect_avoids _ _ _ _ _) hc, he.rip, he.writes.1,
    he.writes.2, he.agrees.external (by simp [Component.Covers]), he.agrees⟩

theorem epilogue [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hf : Frame s t output message.size) (hip : t.RIP = 0x1014aa) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = retAddress ∧ stackPtr u = stackPtr s ∧
      AgreesExcept (callChanges s output message.size) s u ∧ rax.read u = rax.read t ∧
      u.external = t.external := by
  have hne : ∀ x : BitVec 64, 0x100a80 ≤ x.toNat → x.toNat < 0x1014bc → x ≠ boundary.rip := by
    intro x h1 h2 he
    subst he
    simp only [entry, codeEnd, BitVec.reduceToNat] at hb
    omega
  have hsp := hf.rsp
  simp only [frameBytes] at hsp
  have hsl := h.stack.low
  have hlow := h.stackLow
  simp only [stackRegion, frameBytes] at hsl hlow
  have sub_add (a b : Nat) (hab : b ≤ a) (ha : a ≤ 0x1a0) :
      stackPtr s - BitVec.ofNat 64 a + BitVec.ofNat 64 b =
        stackPtr s - BitVec.ofNat 64 (a - b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
      Nat.mod_eq_of_lt (a := a - b) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨t1, a1, r1, e1⟩ := epilogue_add hf.ready hf.code hip boundary
    (hne _ (by decide) (by decide))
  have c1 := e1.codeIn (addR64Imm32Effect_avoids _ _ _ _ _) hf.code
  have x1 : t1.external = t.external := e1.agrees.external (by simp [Component.Covers])
  have sp1 : stackPtr t1 = stackPtr s - BitVec.ofNat 64 0x30 := by
    have hw := e1.writes
    change stackPtr t1 = stackPtr t + (0x170#32).signExtend 64 at hw
    rw [hw, hsp, show (0x170#32).signExtend 64 = BitVec.ofNat 64 0x170 by decide]
    exact sub_add 0x1a0 0x170 (by decide) (by decide)
  have g1 := hf.agrees.trans e1.agrees
  obtain ⟨t2, a2, r2, c2, ip2, v2, sp2, x2, g2⟩ := pop_frame_step
    (pop_r64_effect_step 0x1014b1 0x5b (by decide) (by decide)) r1 c1
    (MemoryRoutines.Machine.program_text_slice c1 0x14b1 1 (by decide +kernel)) e1.rip
    (by rw [sp1]; exact frame_readable h g1 0x30 (by decide) (by decide)) boundary
    (hne _ (by decide) (by decide))
  have sp2' : stackPtr t2 = stackPtr s - BitVec.ofNat 64 0x28 := by
    rw [sp2, sp1]
    exact sub_add 0x30 8 (by decide) (by decide)
  have g2' := g1.trans g2
  obtain ⟨t3, a3, r3, c3, ip3, v3, sp3, x3, g3⟩ := pop_frame_step
    (pop_r64_rex_effect_step 0x1014b2 0x41 0x5c (by unfold RexPrefix; decide) (by decide) (by decide)) r2 c2
    (MemoryRoutines.Machine.program_text_slice c2 0x14b2 2 (by decide +kernel))
    (ip2.trans (by decide))
    (by rw [sp2']; exact frame_readable h g2' 0x28 (by decide) (by decide)) boundary
    (hne _ (by decide) (by decide))
  have sp3' : stackPtr t3 = stackPtr s - BitVec.ofNat 64 0x20 := by
    rw [sp3, sp2']
    exact sub_add 0x28 8 (by decide) (by decide)
  have g3' := g2'.trans g3
  obtain ⟨t4, a4, r4, c4, ip4, v4, sp4, x4, g4⟩ := pop_frame_step
    (pop_r64_rex_effect_step 0x1014b4 0x41 0x5d (by unfold RexPrefix; decide) (by decide) (by decide)) r3 c3
    (MemoryRoutines.Machine.program_text_slice c3 0x14b4 2 (by decide +kernel))
    (ip3.trans (by decide))
    (by rw [sp3']; exact frame_readable h g3' 0x20 (by decide) (by decide)) boundary
    (hne _ (by decide) (by decide))
  have sp4' : stackPtr t4 = stackPtr s - BitVec.ofNat 64 0x18 := by
    rw [sp4, sp3']
    exact sub_add 0x20 8 (by decide) (by decide)
  have g4' := g3'.trans g4
  obtain ⟨t5, a5, r5, c5, ip5, v5, sp5, x5, g5⟩ := pop_frame_step
    (pop_r64_rex_effect_step 0x1014b6 0x41 0x5e (by unfold RexPrefix; decide) (by decide) (by decide)) r4 c4
    (MemoryRoutines.Machine.program_text_slice c4 0x14b6 2 (by decide +kernel))
    (ip4.trans (by decide))
    (by rw [sp4']; exact frame_readable h g4' 0x18 (by decide) (by decide)) boundary
    (hne _ (by decide) (by decide))
  have sp5' : stackPtr t5 = stackPtr s - BitVec.ofNat 64 0x10 := by
    rw [sp5, sp4']
    exact sub_add 0x18 8 (by decide) (by decide)
  have g5' := g4'.trans g5
  obtain ⟨t6, a6, r6, c6, ip6, v6, sp6, x6, g6⟩ := pop_frame_step
    (pop_r64_rex_effect_step 0x1014b8 0x41 0x5f (by unfold RexPrefix; decide) (by decide) (by decide)) r5 c5
    (MemoryRoutines.Machine.program_text_slice c5 0x14b8 2 (by decide +kernel))
    (ip5.trans (by decide))
    (by rw [sp5']; exact frame_readable h g5' 0x10 (by decide) (by decide)) boundary
    (hne _ (by decide) (by decide))
  have sp6' : stackPtr t6 = stackPtr s - BitVec.ofNat 64 0x8 := by
    rw [sp6, sp5']
    exact sub_add 0x10 8 (by decide) (by decide)
  have g6' := g5'.trans g6
  obtain ⟨t7, a7, r7, c7, ip7, v7, sp7, x7, g7⟩ := pop_frame_step
    (pop_r64_effect_step 0x1014ba 0x5d (by decide) (by decide)) r6 c6
    (MemoryRoutines.Machine.program_text_slice c6 0x14ba 1 (by decide +kernel))
    (ip6.trans (by decide))
    (by rw [sp6']; exact frame_readable h g6' 0x8 (by decide) (by decide)) boundary
    (hne _ (by decide) (by decide))
  have hd2 : gprNumber 0 0 (opcodeReg 0x5b) = 3 := by decide
  have hd3 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x5c) = 12 := by decide
  have hd4 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x5d) = 13 := by decide
  have hd5 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x5e) = 14 := by decide
  have hd6 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x5f) = 15 := by decide
  have hd7 : gprNumber 0 0 (opcodeReg 0x5d) = 5 := by decide
  rw [hd2] at v2 g2
  rw [hd3] at v3 g3
  rw [hd4] at v4 g4
  rw [hd5] at v5 g5
  rw [hd6] at v6 g6
  rw [hd7] at v7 g7
  have saved (r : BitVec 5) (off : Nat) (hm : (r, off) ∈ savedSlots) {u : RamState}
      (hx : u.external = t.external) {a : BitVec 64}
      (ha : a = stackPtr s - BitVec.ofNat 64 off) :
      (Operand.mem a : Operand 64).read u = (Operand.reg r : Operand 64).read s := by
    rw [mem_read_congr hx, ha]
    exact hf.saved (r, off) hm
  have x2' : t2.external = t.external := x2.trans x1
  have x3' : t3.external = t.external := x3.trans x2'
  have x4' : t4.external = t.external := x4.trans x3'
  have x5' : t5.external = t.external := x5.trans x4'
  have x6' : t6.external = t.external := x6.trans x5'
  have x7' : t7.external = t.external := x7.trans x6'
  have q3 : (Operand.reg 3 : Operand 64).read t7 = (Operand.reg 3 : Operand 64).read s := by
    rw [((((g3.trans g4).trans g5).trans g6).trans g7).read (by simp), v2]
    exact saved 3 0x30 (by simp [savedSlots]) x1 sp1
  have q12 : (Operand.reg 12 : Operand 64).read t7 = (Operand.reg 12 : Operand 64).read s := by
    rw [(((g4.trans g5).trans g6).trans g7).read (by simp), v3]
    exact saved 12 0x28 (by simp [savedSlots]) x2' sp2'
  have q13 : (Operand.reg 13 : Operand 64).read t7 = (Operand.reg 13 : Operand 64).read s := by
    rw [((g5.trans g6).trans g7).read (by simp), v4]
    exact saved 13 0x20 (by simp [savedSlots]) x3' sp3'
  have q14 : (Operand.reg 14 : Operand 64).read t7 = (Operand.reg 14 : Operand 64).read s := by
    rw [(g6.trans g7).read (by simp), v5]
    exact saved 14 0x18 (by simp [savedSlots]) x4' sp4'
  have q15 : (Operand.reg 15 : Operand 64).read t7 = (Operand.reg 15 : Operand 64).read s := by
    rw [g7.read (by simp), v6]
    exact saved 15 0x10 (by simp [savedSlots]) x5' sp5'
  have q5 : (Operand.reg 5 : Operand 64).read t7 = (Operand.reg 5 : Operand 64).read s := by
    rw [v7]
    exact saved 5 0x8 (by simp [savedSlots]) x6' sp6'
  refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1, t7,
    (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7, r7, c7,
    ip7.trans (by decide), ?_, ?_, ?_, x7'⟩
  · rw [sp7, sp6']
    exact BitVec.sub_add_cancel _ _
  · apply (g6'.trans g7).narrow
    intro c hc hnc
    simp only [savedChanges] at hc
    simp only [hd2, hd3, hd4, hd5, hd6, addR64Imm32Effect_components] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first | exact absurd h hnc | ((try subst h); first
      | exact reg_agrees q3 | exact reg_agrees q5 | exact reg_agrees q12
      | exact reg_agrees q13 | exact reg_agrees q14 | exact reg_agrees q15
      | (exfalso; apply hnc; simp [callChanges]))
  · exact (((((e1.agrees.trans g2).trans g3).trans g4).trans g5).trans g6 |>.trans g7).read
      (by simp)

theorem stack_address {s : RamState} (off i : Nat) (hlow : frameBytes ≤ (stackPtr s).toNat)
    (hoff : off ≤ frameBytes) (hi : i < off + 8) (hhigh : (stackPtr s).toNat + 8 ≤ 2 ^ 32) :
    stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      BitVec.ofNat 64 ((stackRegion s).start + (frameBytes - off + i)) ∧
      (stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat - off + i := by
  simp only [frameBytes] at hlow hoff
  have hx : (stackPtr s - BitVec.ofNat 64 off).toNat = (stackPtr s).toNat - off := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hy : (stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - off + i := by
    rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, hy⟩
  apply BitVec.eq_of_toNat_eq
  rw [hy, BitVec.toNat_ofNat]
  simp only [stackRegion, frameBytes]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem stack_slot [Bindings] {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {cs : List Component}
    (ha : AgreesExcept cs s t) (off : Nat) (h8 : 8 ≤ off) (hoff : off ≤ frameBytes) :
    MemWritable t (stackPtr s - BitVec.ofNat 64 off) 8 ∧
      ∀ i < 8, ¬ InProgram (stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i) := by
  have hsl := h.stack.low
  have hlow := h.stackLow
  simp only [stackRegion] at hsl
  have hhigh : (stackPtr s).toNat + 8 ≤ 2 ^ 32 := by simp only [frameBytes] at hsl hlow; omega
  have hk (i : Nat) (hi : i < 8) := stack_address off i hlow hoff (by omega) hhigh
  have hin (i : Nat) (hi : i < 8) : frameBytes - off + i < (stackRegion s).size := by
    simp only [stackRegion, frameBytes] at hoff ⊢; omega
  have hcont (i : Nat) (hi : i < 8) : (stackRegion s).Contains
      (BitVec.ofNat 64 ((stackRegion s).start + (frameBytes - off + i))).toNat := by
    rw [← (hk i hi).1, (hk i hi).2]
    simp only [stackRegion, MemoryRegion.Contains, frameBytes] at hoff hlow ⊢
    omega
  have h0 := (hk 0 (by decide)).2
  simp only [BitVec.add_zero, Nat.add_zero] at h0
  refine ⟨⟨by simp only [frameBytes] at hoff hlow; omega, fun i hi ↦ ?_, ?_⟩, fun i hi ↦ ?_⟩
  · rw [(hk i hi).1]
    exact ha.grow _ (h.stack.present _ (hin i hi))
  · rw [h0]
    have hpt (i : Nat) (hi : i < 8) :
        ¬ pageTables.Contains ((stackPtr s).toNat - off + i) := by
      have hav := h.stack.avoids _ (hcont i hi)
      rw [← (hk i hi).1] at hav
      intro hc
      apply hav
      right
      rw [(hk i hi).2]
      exact hc
    have p0 := hpt 0 (by decide)
    have p7 := hpt 7 (by decide)
    simp only [pageTables, MemoryRegion.Contains] at p0 p7
    omega
  · have hav := h.stack.avoids _ (hcont i hi)
    rw [← (hk i hi).1] at hav
    exact fun hc ↦ hav (.inl hc)

theorem code_in_program (k j : Nat) (hk : k + j < Extracted.textBytes.size) :
    InProgram (BitVec.ofNat 64 (0x100000 + k) + BitVec.ofNat 64 j) := by
  have := MemoryRoutines.Machine.text_address_in_program (k + j) hk
  rwa [BitVec.ofNat_add (0x100000) k, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem stack_apart_code [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {t : RamState} {cs : List Component}
    (ha : AgreesExcept cs s t) (off : Nat) (h8 : 8 ≤ off) (hoff : off ≤ frameBytes)
    (k len : Nat) (hk : k + len ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s - BitVec.ofNat 64 off) 8 (BitVec.ofNat 64 (0x100000 + k)) len := by
  intro i hi j hj he
  apply (stack_slot h ha off h8 hoff).2 i hi
  rw [he]
  exact code_in_program k j (by omega)

theorem mem_read_agrees {cs : List Component} {t u : RamState} (ha : AgreesExcept cs t u)
    (a : BitVec 64) (hx : ∀ i < 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand 64).read u = (Operand.mem a : Operand 64).read t := by
  change memLoad u.external a 64 = memLoad t.external a 64
  apply memLoad_congr
  intro i hi
  exact congrArg (fun byte : Option UInt8 ↦ byte.getD 0) (ha.byte (hx i (by omega)))

theorem push_frame_step [Bindings] {t : RamState} {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} {src : BitVec 5}
    (hstep : StepEffect (PushPre p len) (codeRange p bytes) (pushR64Effect p len src))
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (hcode : CodeIn (codeRange p bytes) t) (hip : t.RIP = p)
    (hw : MemWritable t (pushAddr t) 8) (hap : RangeApart (pushAddr t) 8 p len)
    (hprog : ∀ i < 8, ¬ InProgram (pushAddr t + BitVec.ofNat 64 i))
    (boundary : ReturnBoundary) (hne : p + BitVec.ofNat 64 len ≠ boundary.rip) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = p + BitVec.ofNat 64 len ∧
      (Operand.mem (pushAddr t) : Operand 64).read u = (Operand.reg src : Operand 64).read t ∧
      stackPtr u = pushAddr t ∧
      AgreesExcept [.reg 4, .mem (pushAddr t) 8, .rip] t u := by
  obtain ⟨u, ha, hr', he⟩ := hstep.advances hr hcode ⟨hip, hw, hap⟩ hne
  have hav : (pushR64Effect p len src t).Avoids Extracted.programImage := by
    intro x hx c hcm hcov
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, he⟩ := hcov
      exact hprog i hi (he ▸ MemoryRoutines.Machine.inProgram_of_mem hx)
    · exact hcov
  refine ⟨u, ha, hr', he.codeIn hav hc, he.rip, he.writes.2, he.writes.1, ?_⟩
  have hg := he.agrees
  simpa using hg

theorem slot_ne {s : RamState} {off off' : Nat} (hlow : frameBytes ≤ (stackPtr s).toNat)
    (hhigh : (stackPtr s).toNat + 8 ≤ 2 ^ 32) (hoff : off ≤ frameBytes) (hoff' : off' ≤ frameBytes)
    (hd : off + 8 ≤ off' ∨ off' + 8 ≤ off) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i ≠
      stackPtr s - BitVec.ofNat 64 off' + BitVec.ofNat 64 j := by
  intro he
  have := congrArg BitVec.toNat he
  rw [(stack_address off i hlow hoff (by omega) hhigh).2,
    (stack_address off' j hlow hoff' (by omega) hhigh).2] at this
  simp only [frameBytes] at hlow hoff hoff'
  omega

theorem slot_in_frame {s : RamState} {off i : Nat} (hlow : frameBytes ≤ (stackPtr s).toNat)
    (hhigh : (stackPtr s).toNat + 8 ≤ 2 ^ 32) (hoff : off ≤ frameBytes) (h8 : 8 ≤ off)
    (hi : i < 8) :
    ∃ k < frameBytes, stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      stackPtr s - BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 k := by
  refine ⟨frameBytes - off + i, by omega, ?_⟩
  rw [(stack_address off i hlow hoff (by omega) hhigh).1,
    (stack_address frameBytes (frameBytes - off + i) hlow (Nat.le_refl _) (by omega) hhigh).1]
  congr 1
  omega

set_option maxHeartbeats 1000000 in
theorem prologue [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) :
    ∃ fuel t, Advances boundary fuel s t ∧ Entered s t output message.size := by
  have hne : ∀ x : BitVec 64, 0x100a80 ≤ x.toNat → x.toNat < 0x1014bc → x ≠ boundary.rip := by
    intro x h1 h2 he
    subst he
    simp only [entry, codeEnd, BitVec.reduceToNat] at hb
    omega
  have hsl := h.stack.low
  have hlow := h.stackLow
  simp only [stackRegion] at hsl
  have hhigh : (stackPtr s).toNat + 8 ≤ 2 ^ 32 := by simp only [frameBytes] at hsl hlow; omega
  have g0 := AgreesExcept.refl [] s
  have sp0 : stackPtr s = stackPtr s - BitVec.ofNat 64 0 := by simp
  have pa1 : pushAddr s = stackPtr s - BitVec.ofNat 64 0x8 := by
    simp only [pushAddr]
    rw [sp0]
    bv_omega
  obtain ⟨t1, a1, r1, c1, ip1, v1, sp1x, g1⟩ := push_frame_step
    (push_r64_effect_step 0x100a80 0x55 (by decide)) h.ready h.code
    (MemoryRoutines.Machine.program_text_slice h.code 0xa80 1 (by decide +kernel))
    h.rip
    (by rw [pa1]; exact (stack_slot h g0 0x8 (by decide) (by decide)).1)
    (by rw [pa1]; exact stack_apart_code h g0 0x8 (by decide) (by decide) 0xa80 1 (by decide +kernel))
    (by rw [pa1]; exact (stack_slot h g0 0x8 (by decide) (by decide)).2) boundary
    (hne _ (by decide) (by decide))
  have sp1 : stackPtr t1 = stackPtr s - BitVec.ofNat 64 0x8 := sp1x.trans pa1
  rw [pa1] at v1 g1
  have G1 := g0.trans g1
  have pa2 : pushAddr t1 = stackPtr s - BitVec.ofNat 64 0x10 := by
    simp only [pushAddr]
    rw [sp1]
    bv_omega
  obtain ⟨t2, a2, r2, c2, ip2, v2, sp2x, g2⟩ := push_frame_step
    (push_r64_rex_effect_step 0x100a81 0x41 0x57 (by unfold RexPrefix; decide) (by decide)) r1 c1
    (MemoryRoutines.Machine.program_text_slice c1 0xa81 2 (by decide +kernel))
    (ip1.trans (by decide))
    (by rw [pa2]; exact (stack_slot h G1 0x10 (by decide) (by decide)).1)
    (by rw [pa2]; exact stack_apart_code h G1 0x10 (by decide) (by decide) 0xa81 2 (by decide +kernel))
    (by rw [pa2]; exact (stack_slot h G1 0x10 (by decide) (by decide)).2) boundary
    (hne _ (by decide) (by decide))
  have sp2 : stackPtr t2 = stackPtr s - BitVec.ofNat 64 0x10 := sp2x.trans pa2
  rw [pa2] at v2 g2
  have G2 := G1.trans g2
  have pa3 : pushAddr t2 = stackPtr s - BitVec.ofNat 64 0x18 := by
    simp only [pushAddr]
    rw [sp2]
    bv_omega
  obtain ⟨t3, a3, r3, c3, ip3, v3, sp3x, g3⟩ := push_frame_step
    (push_r64_rex_effect_step 0x100a83 0x41 0x56 (by unfold RexPrefix; decide) (by decide)) r2 c2
    (MemoryRoutines.Machine.program_text_slice c2 0xa83 2 (by decide +kernel))
    (ip2.trans (by decide))
    (by rw [pa3]; exact (stack_slot h G2 0x18 (by decide) (by decide)).1)
    (by rw [pa3]; exact stack_apart_code h G2 0x18 (by decide) (by decide) 0xa83 2 (by decide +kernel))
    (by rw [pa3]; exact (stack_slot h G2 0x18 (by decide) (by decide)).2) boundary
    (hne _ (by decide) (by decide))
  have sp3 : stackPtr t3 = stackPtr s - BitVec.ofNat 64 0x18 := sp3x.trans pa3
  rw [pa3] at v3 g3
  have G3 := G2.trans g3
  have pa4 : pushAddr t3 = stackPtr s - BitVec.ofNat 64 0x20 := by
    simp only [pushAddr]
    rw [sp3]
    bv_omega
  obtain ⟨t4, a4, r4, c4, ip4, v4, sp4x, g4⟩ := push_frame_step
    (push_r64_rex_effect_step 0x100a85 0x41 0x55 (by unfold RexPrefix; decide) (by decide)) r3 c3
    (MemoryRoutines.Machine.program_text_slice c3 0xa85 2 (by decide +kernel))
    (ip3.trans (by decide))
    (by rw [pa4]; exact (stack_slot h G3 0x20 (by decide) (by decide)).1)
    (by rw [pa4]; exact stack_apart_code h G3 0x20 (by decide) (by decide) 0xa85 2 (by decide +kernel))
    (by rw [pa4]; exact (stack_slot h G3 0x20 (by decide) (by decide)).2) boundary
    (hne _ (by decide) (by decide))
  have sp4 : stackPtr t4 = stackPtr s - BitVec.ofNat 64 0x20 := sp4x.trans pa4
  rw [pa4] at v4 g4
  have G4 := G3.trans g4
  have pa5 : pushAddr t4 = stackPtr s - BitVec.ofNat 64 0x28 := by
    simp only [pushAddr]
    rw [sp4]
    bv_omega
  obtain ⟨t5, a5, r5, c5, ip5, v5, sp5x, g5⟩ := push_frame_step
    (push_r64_rex_effect_step 0x100a87 0x41 0x54 (by unfold RexPrefix; decide) (by decide)) r4 c4
    (MemoryRoutines.Machine.program_text_slice c4 0xa87 2 (by decide +kernel))
    (ip4.trans (by decide))
    (by rw [pa5]; exact (stack_slot h G4 0x28 (by decide) (by decide)).1)
    (by rw [pa5]; exact stack_apart_code h G4 0x28 (by decide) (by decide) 0xa87 2 (by decide +kernel))
    (by rw [pa5]; exact (stack_slot h G4 0x28 (by decide) (by decide)).2) boundary
    (hne _ (by decide) (by decide))
  have sp5 : stackPtr t5 = stackPtr s - BitVec.ofNat 64 0x28 := sp5x.trans pa5
  rw [pa5] at v5 g5
  have G5 := G4.trans g5
  have pa6 : pushAddr t5 = stackPtr s - BitVec.ofNat 64 0x30 := by
    simp only [pushAddr]
    rw [sp5]
    bv_omega
  obtain ⟨t6, a6, r6, c6, ip6, v6, sp6x, g6⟩ := push_frame_step
    (push_r64_effect_step 0x100a89 0x53 (by decide)) r5 c5
    (MemoryRoutines.Machine.program_text_slice c5 0xa89 1 (by decide +kernel))
    (ip5.trans (by decide))
    (by rw [pa6]; exact (stack_slot h G5 0x30 (by decide) (by decide)).1)
    (by rw [pa6]; exact stack_apart_code h G5 0x30 (by decide) (by decide) 0xa89 1 (by decide +kernel))
    (by rw [pa6]; exact (stack_slot h G5 0x30 (by decide) (by decide)).2) boundary
    (hne _ (by decide) (by decide))
  have sp6 : stackPtr t6 = stackPtr s - BitVec.ofNat 64 0x30 := sp6x.trans pa6
  rw [pa6] at v6 g6
  have G6 := G5.trans g6
  have hcode7 : CodeIn (codeRange 0x100a8a (0x48 :: 0x81 :: 0xec :: immBytes 32 0x170)) t6 :=
    MemoryRoutines.Machine.program_text_slice c6 0xa8a 7 (by decide +kernel)
  obtain ⟨t7, a7, r7, e7⟩ := (sub_r64_imm32_effect_step 0x100a8a 0x48 0xec 0x170
    (by unfold RexWPrefix; decide) (by decide) (by decide)).advances r6 hcode7
    (by rw [ip6]; decide) (hne 0x100a91 (by decide) (by decide))
  have c7 := e7.codeIn (subR64Imm32Effect_avoids _ _ _ _ _) c6
  have sp7 : stackPtr t7 = stackPtr s - BitVec.ofNat 64 frameBytes := by
    have hw := e7.writes
    change stackPtr t7 = stackPtr t6 - (0x170#32).signExtend 64 at hw
    rw [hw, sp6, show (0x170#32).signExtend 64 = BitVec.ofNat 64 0x170 by decide]
    simp only [frameBytes]
    bv_omega
  have G7 := G6.trans e7.agrees
  have hd7 : gprNumber 0 (rexB (0x48 : UInt8).toBitVec) (modrmRm 0xec) = 4 := by decide
  have hd1 : gprNumber 0 0 (opcodeReg 0x55) = 5 := by decide
  rw [hd1] at v1
  have q1 : (Operand.mem (stackPtr s - BitVec.ofNat 64 0x8) : Operand 64).read t7 =
      (Operand.reg 5 : Operand 64).read s := by
    rw [mem_read_agrees ((((((g2).trans g3).trans g4).trans g5).trans g6).trans e7.agrees) _ ?_, v1]
    intro i hi c hc hcov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      subR64Imm32Effect_components, hd7, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h
    all_goals (try subst h); first
      | exact hcov
      | (simp only [Component.Covers] at hcov
         obtain ⟨j, hj, he⟩ := hcov
         exact slot_ne hlow hhigh (by decide) (by decide) (by decide) hi hj he)
  have hd2 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x57) = 15 := by decide
  rw [hd2] at v2
  have q2 : (Operand.mem (stackPtr s - BitVec.ofNat 64 0x10) : Operand 64).read t7 =
      (Operand.reg 15 : Operand 64).read s := by
    rw [mem_read_agrees (((((g3).trans g4).trans g5).trans g6).trans e7.agrees) _ ?_, v2]
    · exact G1.read (by simp)
    intro i hi c hc hcov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      subR64Imm32Effect_components, hd7, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h
    all_goals (try subst h); first
      | exact hcov
      | (simp only [Component.Covers] at hcov
         obtain ⟨j, hj, he⟩ := hcov
         exact slot_ne hlow hhigh (by decide) (by decide) (by decide) hi hj he)
  have hd3 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x56) = 14 := by decide
  rw [hd3] at v3
  have q3 : (Operand.mem (stackPtr s - BitVec.ofNat 64 0x18) : Operand 64).read t7 =
      (Operand.reg 14 : Operand 64).read s := by
    rw [mem_read_agrees ((((g4).trans g5).trans g6).trans e7.agrees) _ ?_, v3]
    · exact G2.read (by simp)
    intro i hi c hc hcov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      subR64Imm32Effect_components, hd7, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h
    all_goals (try subst h); first
      | exact hcov
      | (simp only [Component.Covers] at hcov
         obtain ⟨j, hj, he⟩ := hcov
         exact slot_ne hlow hhigh (by decide) (by decide) (by decide) hi hj he)
  have hd4 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x55) = 13 := by decide
  rw [hd4] at v4
  have q4 : (Operand.mem (stackPtr s - BitVec.ofNat 64 0x20) : Operand 64).read t7 =
      (Operand.reg 13 : Operand 64).read s := by
    rw [mem_read_agrees (((g5).trans g6).trans e7.agrees) _ ?_, v4]
    · exact G3.read (by simp)
    intro i hi c hc hcov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      subR64Imm32Effect_components, hd7, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h
    all_goals (try subst h); first
      | exact hcov
      | (simp only [Component.Covers] at hcov
         obtain ⟨j, hj, he⟩ := hcov
         exact slot_ne hlow hhigh (by decide) (by decide) (by decide) hi hj he)
  have hd5 : gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (opcodeReg 0x54) = 12 := by decide
  rw [hd5] at v5
  have q5 : (Operand.mem (stackPtr s - BitVec.ofNat 64 0x28) : Operand 64).read t7 =
      (Operand.reg 12 : Operand 64).read s := by
    rw [mem_read_agrees ((g6).trans e7.agrees) _ ?_, v5]
    · exact G4.read (by simp)
    intro i hi c hc hcov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      subR64Imm32Effect_components, hd7, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h
    all_goals (try subst h); first
      | exact hcov
      | (simp only [Component.Covers] at hcov
         obtain ⟨j, hj, he⟩ := hcov
         exact slot_ne hlow hhigh (by decide) (by decide) (by decide) hi hj he)
  have hd6 : gprNumber 0 0 (opcodeReg 0x53) = 3 := by decide
  rw [hd6] at v6
  have q6 : (Operand.mem (stackPtr s - BitVec.ofNat 64 0x30) : Operand 64).read t7 =
      (Operand.reg 3 : Operand 64).read s := by
    rw [mem_read_agrees (e7.agrees) _ ?_, v6]
    · exact G5.read (by simp)
    intro i hi c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      subR64Imm32Effect_components, hd7] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h
    all_goals (try subst h); first
      | exact hcov
      | (simp only [Component.Covers] at hcov
         obtain ⟨j, hj, he⟩ := hcov
         exact slot_ne hlow hhigh (by decide) (by decide) (by decide) hi hj he)
  have ag : AgreesExcept (prologueChanges s) s t7 := by
    apply G7.widen
    · intro c hc hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        subR64Imm32Effect_components, List.nil_append, hd7, or_assoc] at hc
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h
      all_goals (try subst h); first
        | (simp [prologueChanges]; done)
        | (simp [Component.isMem] at hm; done)
    · intro x c hc hcov
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        subR64Imm32Effect_components, List.nil_append, hd7, or_assoc] at hc
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h
      all_goals (try subst h); first
        | exact hcov.elim
        | (simp only [Component.Covers] at hcov
           obtain ⟨i, hi, rfl⟩ := hcov
           refine ⟨.mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes,
             by simp [prologueChanges], ?_⟩
           exact slot_in_frame hlow hhigh (by decide) (by decide) hi)
  refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1, t7,
    (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7,
    ⟨r7, c7, sp7, ag.mono ?_, ?_⟩, by rw [e7.rip]; rfl, ag⟩
  · intro c hc
    simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp [callChanges]
  · intro e he
    simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact q6
    · exact q5
    · exact q4
    · exact q3
    · exact q2
    · exact q1


section Check

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def checkBytesA : List UInt8 :=
  [0x4c, 0x8b, 0x5e, 0x10, 0x44, 0x8b, 0x67, 0x30, 0x0f, 0xb6, 0x4f, 0x40,
    0x41, 0xba, 0x40, 0x00, 0x00, 0x00, 0x49, 0x29, 0xca, 0x4c, 0x89, 0xd8, 0x4c, 0x29, 0xd0]

theorem code_sub_at {p q : BitVec 64} {all bytes : List UInt8} (off : Nat)
    (hq : q = p + BitVec.ofNat 64 off) (hsub : (all.drop off).take bytes.length = bytes) :
    ∀ x ∈ codeRange q bytes, x ∈ codeRange p all :=
  hq ▸ codeRange_mem_of_drop off hsub

macro "chk_then " off:num h:ident t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => exact code_sub_at $off (by decide +kernel) (by decide +kernel)
  case full => x86_full
  case mid =>
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · first
      | exact hH.rip_of (by x86_norm)
      | exact ⟨hH.rip_of (by x86_norm)⟩
      | (refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
         x86_norm; first | exact hP.len | exact hP.ctr | exact hP.pos)
    · x86_avoid
  case boundary => intro _ _; x86_norm; exact $h _ (by decide) (by decide)
  case' k => x86_norm))

structure PreA (s : RamState) : Prop where
  rip : s.RIP = 0x100a91
  len : MemReadable s ((Operand.reg 6 : Operand 64).read s + 0x10) 8
  ctr : MemReadable s ((Operand.reg 7 : Operand 64).read s + 0x30) 4
  pos : MemReadable s ((Operand.reg 7 : Operand 64).read s + 0x40) 1

def lenA (s : RamState) : BitVec 64 :=
  (Operand.mem ((Operand.reg 6 : Operand 64).read s + 16#64) : Operand 64).read s

def ctrA (s : RamState) : BitVec 32 :=
  (Operand.mem ((Operand.reg 7 : Operand 64).read s + 48#64) : Operand 32).read s

def posA (s : RamState) : BitVec 8 :=
  (Operand.mem ((Operand.reg 7 : Operand 64).read s + 64#64) : Operand 8).read s

def effA (s : RamState) : Effect :=
  { rip := 0x100aac
    writes := [⟨(Operand.reg 11 : Operand 64), lenA s⟩, ⟨(Operand.reg 12 : Operand 64), (ctrA s).setWidth 64⟩,
      ⟨(Operand.reg 1 : Operand 64), (posA s).setWidth 64⟩,
      ⟨(Operand.reg 10 : Operand 64), 64#64 - (posA s).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), lenA s - (64#64 - (posA s).setWidth 64)⟩]
    flags := some (.ofStatusFlags (subSpec (lenA s) (64#64 - (posA s).setWidth 64)).2) }

set_option maxHeartbeats 4000000 in
theorem chunkA [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) :
    AdvancesBlock boundary PreA (codeRange 0x100a91 checkBytesA) effA := by
  have hne (pc : BitVec 64) (hl : 0x100a80 ≤ pc.toNat) (hu : pc.toNat < 0x1014bc) :
      pc ≠ boundary.rip := by intro he; subst pc; omega

  routine_run_begin (show StepEffect _ _ (movR64M64Effect _ 11 _) from mov_r64_m64_effect_step 0x100a91 0x4c (by unfold RexWPrefix; decide) 3
    (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide))
  case pre => intro s hP; refine ⟨hP.rip, ?_⟩; x86_norm; exact hP.len
  case boundary => intro _ _; exact hne 0x100a95 (by decide) (by decide)
  chk_then 4 hne (show StepEffect _ _ (movR32M32Effect _ 12 _) from mov_r32_m32_effect_step 0x100a95 0x44 (by unfold RexNoWPrefix; decide) 4
    (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide))
  chk_then 8 hne (show StepEffect _ _ (movzxR32M8Effect _ _ 1 _) from movzx_r32_m8_effect_step 0x100a99 1 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide))
  chk_then 12 hne (show StepEffect _ _ (movR32Imm32Effect _ _ 10 _) from mov_r32_imm32_rex_effect_step 0x100a9d 0x41 0xba (by unfold RexNoWPrefix; decide) (by decide) 0x40)
  chk_then 18 hne (show StepEffect _ _ (subR64R64Effect _ 10 1) from sub_r64_r64_effect_step 0x100aa3 0x49 0xca (by unfold RexWPrefix; decide) (by decide))
  chk_then 21 hne (show StepEffect _ _ (movR64R64Effect _ 0 11) from mov_r64_r64_effect_step 0x100aa6 0x4c 0xd8 (by unfold RexWPrefix; decide) (by decide))
  chk_then 24 hne (show StepEffect _ _ (subR64R64Effect _ 0 10) from sub_r64_r64_effect_step 0x100aa9 0x4c 0xd0 (by unfold RexWPrefix; decide) (by decide))
  apply AdvancesBlock.block_end
  intro s t _ hH
  x86_norm at hH
  exact hH

def checkBytesB : List UInt8 :=
  [0x44, 0x89, 0xe2, 0xf7, 0xd2, 0x49, 0x89, 0xc0, 0x49, 0xc1, 0xe8, 0x06, 0x83, 0xe0, 0x3f,
    0x48, 0x83, 0xf8, 0x01, 0x49, 0x83, 0xd8, 0xff, 0xb0, 0x01, 0x49, 0x39, 0xd0]

def PreB (c : Bool) (s : RamState) : Prop :=
  s.RIP = 0x100aae ∧
    (cmpSpec (BitVec.setWidth 64 ((Operand.reg 0 : Operand 32).read s &&& 63#32)) 1#64).CF = c

theorem reg_read_32 (s : RamState) (r : BitVec 5) :
    BitVec.setWidth 32 (BitVec.setWidth 64 ((Operand.reg r : Operand 64).read s)) =
      (Operand.reg r : Operand 32).read s := by
  simp [Operand.read]

def effB (c : Bool) (s : RamState) : Effect :=
  let r8 := (Operand.reg 0 : Operand 64).read s >>> (6 : Nat) - (18446744073709551615#64 + BitVec.ofNat 64 c.toNat)
  let edx := BitVec.setWidth 64 (~~~((Operand.reg 12 : Operand 32).read s))
  { rip := 0x100aca
    writes := [⟨(Operand.reg 2 : Operand 64), edx⟩, ⟨(Operand.reg 8 : Operand 64), r8⟩,
      ⟨(Operand.reg 0 : Operand 64),
        mergeGPR 8 (1#8) (BitVec.setWidth 64 ((Operand.reg 0 : Operand 32).read s &&& 63#32))⟩]
    flags := some (.ofStatusFlags (cmpSpec r8 edx)) }

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
theorem chunkB [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (c : Bool) :
    AdvancesBlock boundary (PreB c) (codeRange 0x100aae checkBytesB) (effB c) := by
  have hne (pc : BitVec 64) (hl : 0x100a80 ≤ pc.toNat) (hu : pc.toNat < 0x1014bc) :
      pc ≠ boundary.rip := by intro he; subst pc; omega
  refine AdvancesBlock.block_first ?k (show StepEffect _ _ (movR32R32Effect _ _ 2 12) from mov_r32_r32_rex_effect_step 0x100aae 0x44 0xe2 (by unfold RexNoWPrefix; decide) (by decide)) ?sub ?pre ?av ?boundary
  case sub => exact codeRange_mem_of_take (by decide +kernel)
  case pre => intro s hP; exact hP.1
  case av => intro _ _; x86_avoid
  case boundary => intro _ _; x86_norm; exact hne _ (by decide) (by decide)
  case' k => x86_norm
  chk_then 3 hne (show StepEffect _ _ (notR32Effect _ _ 2) from not_r32_effect_step 0x100ab1 0xd2 (by decide) (by decide))
  chk_then 5 hne (show StepEffect _ _ (movR64R64Effect _ 8 0) from mov_r64_r64_effect_step 0x100ab3 0x49 0xc0 (by unfold RexWPrefix; decide) (by decide))
  chk_then 8 hne (show StepEffect _ _ (shrR64Effect _ _ 8 6) from shr_r64_imm8_effect_step 0x100ab6 0x49 0xe8 0x06 (by unfold RexWPrefix; decide) (by decide) (by decide))
  chk_then 12 hne (show StepEffect _ _ (andR32Imm8Effect _ _ 0 _) from and_r32_imm8_effect_step 0x100aba 0xe0 0x3f (by decide) (by decide))
  chk_then 15 hne (show StepEffect _ _ (cmpR64Imm8Effect _ 0 _) from cmp_r64_imm8_effect_step 0x100abd 0x48 0xf8 0x01 (by unfold RexWPrefix; decide) (by decide) (by decide))
  refine AdvancesBlock.block_then ?k2 (show StepEffect _ _ (sbbR64Imm8Effect _ 8 _ c) from sbb_r64_imm8_effect_step 0x100ac1 0x49 0xd8 0xff c (by unfold RexWPrefix; decide) (by decide) (by decide)) ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => exact code_sub_at 19 (by decide +kernel) (by decide +kernel)
  case full => x86_full
  case mid =>
    intro s s' hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), ?_⟩, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · have h := hH.flag .CF
      x86_norm at h
      exact h.trans hP.2
    · x86_avoid
  case boundary => intro _ _; x86_norm; exact hne _ (by decide) (by decide)
  case' k2 => x86_norm
  chk_then 23 hne (show StepEffect _ _ (movR8Imm8NoRexEffect _ _ 0 _) from mov_r8_imm8_norex_effect_step 0x100ac5 0xb0 (by decide) 0x01)
  chk_then 25 hne (show StepEffect _ _ (cmpR64R64Effect _ 8 2) from cmp_r64_r64_effect_step 0x100ac7 0x49 0xd0 (by unfold RexWPrefix; decide) (by decide))
  apply AdvancesBlock.block_end
  intro s s' _ hH
  apply hH.weaken
  · x86_norm [effB]
  · x86_norm [effB]
    all_goals try simp (config := { decide := true }) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  · intro i; cases i <;> x86_norm [effB]
    all_goals try simp (config := { decide := true }) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  · x86_norm [effB]


theorem ja_iff (L : Nat) (hL : L ≤ 2^32) (ctr : BitVec 32) :
    condHolds 7 (cmpSpec (BitVec.ofNat 64 L >>> (6 : Nat) - (0xffffffffffffffff#64 + BitVec.ofNat 64
        (cmpSpec (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 L) &&& 63#32)) 1#64).CF.toNat))
      (BitVec.setWidth 64 (~~~ ctr))) = !decide (ctr.toNat + (L+63)/64 < 2^32) := by
  have h63 : ((BitVec.setWidth 32 (BitVec.ofNat 64 L) &&& 63#32)).toNat = L % 64 := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (63#32).toNat = 2^6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hc : (cmpSpec (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 L) &&& 63#32)) 1#64).CF
      = decide (L % 64 = 0) := by
    simp only [cmpSpec, subSpec, BitVec.toNat_setWidth, h63]
    by_cases h : L % 64 = 0 <;> simp [h] <;> omega
  rw [hc]
  have hr8 : (BitVec.ofNat 64 L >>> (6 : Nat) - (0xffffffffffffffff#64 +
      BitVec.ofNat 64 (decide (L % 64 = 0)).toNat)).toNat = (L + 63) / 64 := by
    have hs : (BitVec.ofNat 64 L >>> (6 : Nat)).toNat = L / 64 := by
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
    by_cases h : L % 64 = 0
    · simp only [h, decide_true, Bool.toNat_true]
      rw [BitVec.toNat_sub, hs]
      simp
      omega
    · simp only [h, decide_false, Bool.toNat_false]
      rw [BitVec.toNat_sub, hs]
      simp
      omega
  have hn : ctr.toNat < 2^32 := ctr.isLt
  have hd : (BitVec.setWidth 64 (~~~ ctr)).toNat = 2^32 - 1 - ctr.toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_not]; omega
  simp only [condHolds, cmpSpec, subSpec, BitVec.toNat_setWidth, BitVec.toNat_not]
  generalize hx : (BitVec.ofNat 64 L >>> (6 : Nat) - (0xffffffffffffffff#64 +
      BitVec.ofNat 64 (decide (L % 64 = 0)).toNat)) = x at hr8 ⊢
  generalize hy : BitVec.setWidth 64 (~~~ ctr) = y at hd ⊢
  have hz : (x - y == 0) = decide (x.toNat = y.toNat) := by
    by_cases e : x = y
    · subst e; simp
    · have : x.toNat ≠ y.toNat := fun h => e (BitVec.eq_of_toNat_eq h)
      simp only [this, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h0
      exact e (by bv_omega)
  rw [hz, hr8, hd]
  by_cases h1 : ctr.toNat + (L + 63) / 64 < 2 ^ 32 <;> simp [h1] <;> omega

theorem stateBytes_counter (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (i : Nat) (hi : i < 4) (hj : 48 + i < (stateBytes key counter nonce).size) :
    (stateBytes key counter nonce)[48 + i] = storedByte counter.toBitVec i := by
  have hc : (initialState key counter nonce)[12] = counter := by
    simp [initialState, chachaState, counterNonceWords]
  simp only [stateBytes, serialize]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals simp [ByteArray.getElem_eq_getElem_data, storedByte, hc]
  all_goals
    apply UInt8.toNat_inj.mp
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem frame_covers {s : RamState} (hlow : frameBytes ≤ (stackPtr s).toNat) {x : BitVec 64}
    (hc : (Component.mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes).Covers x) :
    (stackPtr s).toNat - frameBytes ≤ x.toNat ∧ x.toNat < (stackPtr s).toNat := by
  obtain ⟨j, hj, rfl⟩ := hc
  simp only [frameBytes] at hlow hj ⊢
  bv_omega

theorem entered_external [Bindings] {s t : RamState} {output : BitVec 64} {length : Nat}
    (hlow : frameBytes ≤ (stackPtr s).toNat) (he : Entered s t output length) {x : BitVec 64}
    (hx : x.toNat < (stackPtr s).toNat - frameBytes ∨ (stackPtr s).toNat ≤ x.toNat) :
    t.external[x]? = s.external[x]? := by
  apply he.agrees.byte
  intro c hc hcov
  simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact hcov
  · exact hcov
  · exact hcov
  · have := frame_covers hlow hcov
    omega

theorem outside_stack [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {r : MemoryRegion}
    (hd : r.Disjoint (stackRegion s)) {x : Nat} (hx : r.Contains x) :
    x < (stackPtr s).toNat - frameBytes ∨ (stackPtr s).toNat ≤ x := by
  have := hd x hx
  have hlow := h.stackLow
  simp only [MemoryRegion.Contains, stackRegion] at this
  omega

theorem off_toNat {a k : BitVec 64} (hk : a.toNat + k.toNat < 2 ^ 32) :
    (a + k).toNat = a.toNat + k.toNat := by
  rw [BitVec.toNat_add]
  omega

theorem addr_split (a k : BitVec 64) (i : Nat) :
    a + k + BitVec.ofNat 64 i = BitVec.ofNat 64 (a.toNat + (k.toNat + i)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem addr_zero (a : BitVec 64) (j : Nat) :
    a + BitVec.ofNat 64 j = BitVec.ofNat 64 (a.toNat + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem pre_values [Bindings] {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (he : Entered s t output message.size) :
    PreA t ∧ lenA t = BitVec.ofNat 64 message.size ∧ ctrA t = counter.toBitVec ∧
      posA t = 64#8 := by
  have hlow := h.stackLow
  have hsi : (Operand.reg 6 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s :=
    he.agrees.read (by simp [prologueChanges])
  have hdi : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    he.agrees.read (by simp [prologueChanges])
  have hbl := h.buf.low
  simp only [rsi] at hbl
  have hcl := h.cipher.low
  simp only [cipherRegion, cipherBytes, rdi] at hcl
  have hbuf : ∀ i < 24, t.external[BitVec.ofNat 64 (((Operand.reg 6 : Operand 64).read s).toNat + i)]? =
      s.external[BitVec.ofNat 64 (((Operand.reg 6 : Operand 64).read s).toNat + i)]? := by
    intro i hi
    apply entered_external hlow he
    apply outside_stack h h.bufStack
    simp only [MemoryRegion.Contains, bufRegion, rsi, BitVec.toNat_ofNat]
    omega
  have hcip : ∀ i < 0x80, t.external[BitVec.ofNat 64 (((Operand.reg 7 : Operand 64).read s).toNat + i)]? =
      s.external[BitVec.ofNat 64 (((Operand.reg 7 : Operand 64).read s).toNat + i)]? := by
    intro i hi
    apply entered_external hlow he
    apply outside_stack h h.cipherStack
    simp only [MemoryRegion.Contains, cipherRegion, cipherBytes, rdi, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨he.rip, ⟨?_, fun i hi => ?_⟩, ⟨?_, fun i hi => ?_⟩, ⟨?_, fun i hi => ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [hsi, off_toNat (by simp only [BitVec.reduceToNat]; omega)]
    simp only [BitVec.reduceToNat]; omega
  · rw [hsi, addr_split, hbuf _ (by simp only [BitVec.reduceToNat]; omega)]
    have := h.buf.mem (16 + i) (by omega)
    rw [addr_zero] at this
    simpa only [rsi, BitVec.reduceToNat] using this
  · rw [hdi, off_toNat (by simp only [BitVec.reduceToNat]; omega)]
    simp only [BitVec.reduceToNat]; omega
  · rw [hdi, addr_split, hcip _ (by simp only [BitVec.reduceToNat]; omega)]
    have := h.cipher.present (48 + i) (by simp only [cipherRegion, cipherBytes]; omega)
    simpa only [cipherRegion, rdi, BitVec.reduceToNat] using this
  · rw [hdi, off_toNat (by simp only [BitVec.reduceToNat]; omega)]
    simp only [BitVec.reduceToNat]; omega
  · rw [hdi, addr_split, hcip _ (by simp only [BitVec.reduceToNat]; omega)]
    have := h.cipher.present (64 + i) (by simp only [cipherRegion, cipherBytes]; omega)
    simpa only [cipherRegion, rdi, BitVec.reduceToNat] using this
  · unfold lenA
    rw [hsi]
    change memLoad t.external _ 64 = _
    rw [← Refine.memLoad_of_word64At h.length]
    apply memLoad_congr
    intro i hi
    simp only [memByte]
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [addr_split, ← BitVec.ofNat_add, hbuf _ (by simp only [BitVec.reduceToNat]; omega)]
    simp only [lengthSlot, rsi, BitVec.reduceToNat, Nat.add_assoc]
  · unfold ctrA
    rw [hdi]
    change memLoad t.external _ 32 = _
    apply memLoad_eq_of_memByte (by decide)
    intro i hi
    simp only [memByte]
    change (t.external[_]?).getD 0 = _
    have hsz := h.words.1
    simp only [MemoryRegion.HasLength, wordsRegion] at hsz
    have hw := h.words.2 ⟨48 + i, by omega⟩
    rw [addr_split, hcip _ (by simp only [BitVec.reduceToNat]; omega)]
    simp only [wordsRegion, rdi] at hw
    simp only [BitVec.reduceToNat]
    rw [hw]
    exact stateBytes_counter key counter nonce i (by omega) _
  · unfold posA
    rw [hdi]
    change memLoad t.external _ 8 = _
    apply memLoad_eq_of_memByte (by decide)
    intro i hi
    obtain rfl : i = 0 := by omega
    simp only [memByte]
    change (t.external[_]?).getD 0 = _
    have hw := h.position.2 ⟨0, by decide⟩
    rw [addr_split, hcip _ (by simp only [BitVec.reduceToNat]; omega)]
    simp only [positionRegion, rdi] at hw
    simp only [BitVec.reduceToNat]
    rw [hw]
    rfl

theorem reg32_eq (s : RamState) (r : BitVec 5) :
    (Operand.reg r : Operand 32).read s = ((Operand.reg r : Operand 64).read s).setWidth 32 := by
  simp [Operand.read]

theorem check [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (he : Entered s t output message.size) :
    ∃ fuel u, Advances boundary fuel t u ∧
      if Accepted counter message.size then Checked s u counter output message.size
      else Frame s u output message.size ∧ u.RIP = 0x1014aa ∧
        Status s u key counter nonce output message := by
  have hbb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat := by
    simpa only [entry, codeEnd, BitVec.reduceToNat] using hb
  have hne : ∀ x : BitVec 64, 0x100a80 ≤ x.toNat → x.toNat < 0x1014bc → x ≠ boundary.rip := by
    intro x h1 h2 he; subst he; omega
  have hf := he.frame
  have hL : message.size ≤ 2 ^ 32 := by have := h.messageLow; omega
  obtain ⟨hpre, hlen, hctr, hpos⟩ := pre_values h he
  obtain ⟨n1, u1, a1, r1, _, e1⟩ := chunkA boundary hbb t hf.ready
    (show CodeIn (codeRange 0x100a91 checkBytesA) t from
      MemoryRoutines.Machine.program_text_slice hf.code 0xa91 27 (by decide +kernel)) hpre
  have c1 : CodeIn Extracted.programImage u1 := e1.agrees.codeIn (by
    intro c hc x hx
    simp only [effA, Effect.components, List.map, List.mem_append, List.mem_cons,
      List.not_mem_nil, Write.component_reg] at hc
    rcases hc with ((h | h | h | h | h | h) | h | h) | h | h <;> (try subst h) <;> simp_all [Component.Covers]) hf.code
  obtain ⟨w11, w12, w1, w10, w0⟩ := e1.writes
  dsimp only [Write.AllHold] at w11 w12 w1 w10 w0
  have f1 := e1.flag .CF
  simp only [Effect.flag, effA, StatusFlagsOutcome.ofStatusFlags, StatusFlagsOutcome.get,
    FlagAllows, StatusFlags.get] at f1
  have hz : (64#64 - BitVec.setWidth 64 (64#8)) = 0 := by decide
  simp only [hlen, hpos, hctr, hz] at w11 w12 w1 w10 w0 f1
  have hcf : condHolds 2 (StatusFlags.ofRFLAGS u1.RFLAGS) = false := by
    simp only [condHolds, BitVec.reduceToNat]
    rw [f1]
    simp [subSpec]
  obtain ⟨u2, a2, r2, e2⟩ := (jcc_rel8_effect_step 0x100aac 2 0x22).advances r1
    (show CodeIn (codeRange 0x100aac (jccOpcode8 2 :: immBytes 8 0x22)) u1 from
      MemoryRoutines.Machine.program_text_slice c1 0xaac 2 (by decide +kernel))
    ⟨e1.rip, fun hc => absurd (hcf.symm.trans hc) (by decide)⟩ (by
      simp only [jccEffect, branchEffect, hcf, Bool.false_eq_true, ite_false]
      exact hne 0x100aae (by decide) (by decide))
  have e2' := jccEffect_not_taken hcf e2
  have c2 : CodeIn Extracted.programImage u2 := e2'.agrees.codeIn (by
    intro c hc x hx
    simp only [nopEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; exact hx) c1
  have rip2 : u2.RIP = 0x100aae := e2'.rip
  obtain ⟨n3, u3, a3, r3, _, e3⟩ := chunkB boundary hbb
    (cmpSpec (BitVec.setWidth 64 ((Operand.reg 0 : Operand 32).read u2 &&& 63#32)) 1#64).CF u2 r2
    (show CodeIn (codeRange 0x100aae checkBytesB) u2 from
      MemoryRoutines.Machine.program_text_slice c2 0xaae 28 (by decide +kernel)) ⟨rip2, rfl⟩
  have c3 : CodeIn Extracted.programImage u3 := e3.agrees.codeIn (by
    intro c hc x hx
    simp only [effB, Effect.components, List.map, List.mem_append, List.mem_cons,
      List.not_mem_nil, Write.component_reg] at hc
    rcases hc with ((h | h | h) | h | h) | h | h <;> (try subst h) <;> simp_all [Component.Covers]) c2
  have hjt : (branchTarget 0x100aca 6 ((0x9da : BitVec 32).signExtend 64)) = 0x1014aa := by decide
  obtain ⟨u4, a4, r4, e4⟩ := (jcc_rel32_effect_step 0x100aca 7 0x9da).advances r3
    (show CodeIn (codeRange 0x100aca (0x0F :: jccOpcode32 7 :: immBytes 32 0x9da)) u3 from
      MemoryRoutines.Machine.program_text_slice c3 0xaca 6 (by decide +kernel))
    ⟨e3.rip, fun _ => by rw [hjt]; decide⟩ (by
      simp only [jccEffect, branchEffect, hjt]
      split
      · exact hne 0x1014aa (by decide) (by decide)
      · exact hne 0x100ad0 (by decide) (by decide))
  have g2 := e2'.agrees
  have v0 : (Operand.reg 0 : Operand 64).read u2 = BitVec.ofNat 64 message.size := by
    rw [g2.read (by simp), w0]; simp
  have v12 : (Operand.reg 12 : Operand 64).read u2 = BitVec.setWidth 64 counter.toBitVec := by
    rw [g2.read (by simp), w12]
  obtain ⟨x2, x8, x0⟩ := e3.writes
  dsimp only [effB, Write.AllHold] at x2 x8 x0
  have f3c := e3.flag .CF
  have f3z := e3.flag .ZF
  simp only [Effect.flag, effB, StatusFlagsOutcome.ofStatusFlags, StatusFlagsOutcome.get,
    FlagAllows, StatusFlags.get] at f3c f3z
  simp only [reg32_eq, v0, v12] at x2 x8 x0 f3c f3z
  have hcond : condHolds 7 (StatusFlags.ofRFLAGS u3.RFLAGS) =
      !decide (counter.toNat + (message.size + 63) / 64 < 2 ^ 32) := by
    have hj := ja_iff message.size hL counter.toBitVec
    simp only [UInt32.toNat_toBitVec] at hj
    rw [← hj]
    simp (config := { decide := true }) only [condHolds, BitVec.reduceToNat, f3c, f3z,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have G := e1.agrees.trans (e2'.agrees.trans (e3.agrees.trans e4.agrees))
  have hG : ∀ c ∈ (effA t).components ++ ((nopEffect 0x100aac 2).components ++
      ((effB (cmpSpec (BitVec.setWidth 64 ((Operand.reg 0 : Operand 32).read u2 &&& 63#32)) 1#64).CF
        u2).components ++ (jccEffect 0x100aca 6 7 ((0x9da : BitVec 32).signExtend 64) u3).components)),
      c = .reg 0 ∨ c = .reg 1 ∨ c = .reg 2 ∨ c = .reg 8 ∨ c = .reg 10 ∨ c = .reg 11 ∨
        c = .reg 12 ∨ c = .flags ∨ c = .rip := by
    intro c hc
    simp only [jccEffect, branchEffect_components, nopEffect_components] at hc
    simp only [effA, effB, Effect.components, List.map, List.mem_cons, List.not_mem_nil,
      Write.component_reg, or_false, List.cons_append, List.nil_append] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  have hnc : ∀ c ∈ (effA t).components ++ ((nopEffect 0x100aac 2).components ++
      ((effB (cmpSpec (BitVec.setWidth 64 ((Operand.reg 0 : Operand 32).read u2 &&& 63#32)) 1#64).CF
        u2).components ++ (jccEffect 0x100aca 6 7 ((0x9da : BitVec 32).signExtend 64) u3).components)),
      ∀ x, ¬ c.Covers x := by
    intro c hc x hx
    rcases hG c hc with h | h | h | h | h | h | h | h | h <;> subst h <;> exact hx
  have hext : u4.external = t.external := G.external hnc
  have c4 : CodeIn Extracted.programImage u4 := G.codeIn hnc hf.code
  have hsp : stackPtr u4 = stackPtr t := by
    have := G.agree (.reg 4) (by intro hm; have := hG _ hm; simp at this) rfl
    exact this
  have H := e2'.agrees.trans (e3.agrees.trans e4.agrees)
  have v11 : (Operand.reg 11 : Operand 64).read u4 = BitVec.ofNat 64 message.size := by
    rw [H.read (by simp only [jccEffect, branchEffect_components, nopEffect_components]; simp [effB, Effect.components]), w11]
  have v10 : (Operand.reg 10 : Operand 64).read u4 = 0 := by
    rw [H.read (by simp only [jccEffect, branchEffect_components, nopEffect_components]; simp [effB, Effect.components]), w10]
  have v1 : (Operand.reg 1 : Operand 64).read u4 = 0x40 := by
    rw [H.read (by simp only [jccEffect, branchEffect_components, nopEffect_components]; simp [effB, Effect.components]), w1]; decide
  have v12' : (Operand.reg 12 : Operand 64).read u4 = counter.toBitVec.setWidth 64 := by
    rw [H.read (by simp only [jccEffect, branchEffect_components, nopEffect_components]; simp [effB, Effect.components]), w12]
  have v0' : (Operand.reg 0 : Operand 64).read u4 = (Operand.reg 0 : Operand 64).read u3 :=
    e4.agrees.read (by simp only [jccEffect, branchEffect_components]; simp)
  have hfr : Frame s u4 output message.size := by
    refine ⟨r4, c4, hsp.trans hf.rsp, (hf.agrees.trans G).mono ?_, ?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hc
      · rcases hG c hc with h | h | h | h | h | h | h | h | h <;> subst h <;>
          simp [callChanges, savedChanges]
    · intro e he
      rw [mem_read_congr hext]
      exact hf.saved e he
  refine ⟨n1 + (1 + (n3 + 1)), u4, a1.trans (a2.trans (a3.trans a4)), ?_⟩
  by_cases hacc : Accepted counter message.size
  · have hc7 : condHolds 7 (StatusFlags.ofRFLAGS u3.RFLAGS) = false := by
      rw [hcond]; simpa using hacc
    have e4' := jccEffect_not_taken hc7 e4
    simp only [hacc, ite_true]
    refine ⟨hfr, by rw [e4'.rip]; decide, (he.agrees.trans G).mono ?_, v11, v10, v1, v12'⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · rcases hG c hc with h | h | h | h | h | h | h | h | h <;> subst h <;> simp [prologueChanges]
  · have hc7 : condHolds 7 (StatusFlags.ofRFLAGS u3.RFLAGS) = true := by
      rw [hcond]; simpa using hacc
    have e4' := jccEffect_taken hc7 e4
    simp only [hacc, ite_false]
    refine ⟨hfr, by rw [e4'.rip]; exact hjt, ?_⟩
    unfold Status
    simp only [hacc, ite_false]
    refine ⟨by rw [v0', x0, setWidth_mergeGPR8]; rfl, fun a ha => ?_⟩
    rw [hext]
    apply entered_external h.stackLow he
    have := ha ⟨(stackPtr s).toNat - frameBytes, frameBytes⟩ (by simp)
    simp only [MemoryRegion.Contains] at this
    omega

end Check

theorem accepted_run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hacc : Accepted counter message.size) (hc : Checked s t counter output message.size) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u output message.size ∧
      u.RIP = 0x1014aa ∧ Status s u key counter nonce output message :=
  Run.accepted_run boundary hb h hacc hc

theorem after_prologue [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (he : Entered s t output message.size) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u output message.size ∧
      u.RIP = 0x1014aa ∧ Status s u key counter nonce output message := by
  obtain ⟨n, u, ha, hu⟩ := check boundary hb h he
  by_cases hacc : Accepted counter message.size
  · simp only [hacc, ↓reduceIte] at hu
    obtain ⟨m, v, ha', hv⟩ := accepted_run boundary hb h hacc hu
    exact ⟨n + m, v, ha.trans ha', hv⟩
  · simp only [hacc, ↓reduceIte] at hu
    exact ⟨n, u, ha, hu⟩

theorem run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) :
    ∃ fuel t, Advances boundary fuel s t ∧ Frame s t output message.size ∧
      t.RIP = 0x1014aa ∧ Status s t key counter nonce output message := by
  obtain ⟨n, t, ha, he⟩ := prologue boundary hb h
  obtain ⟨m, u, ha', hf, hip, hst⟩ := after_prologue boundary hb h he
  exact ⟨n + m, u, ha.trans ha', hf, hip, hst⟩

theorem body [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyResult s t key counter nonce output message := by
  obtain ⟨n, t, ha, hf, hip, hst⟩ := run boundary hb h
  obtain ⟨m, u, ha', hr, hc, hip', hsp, hag, hrax, hext⟩ := epilogue boundary hb h hf hip
  exact ⟨n + m, u, ha.trans ha', hr, hc, hip', hsp, hag, hst.transfer hrax hext⟩

theorem covers_toNat {a x : BitVec 64} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64)
    (h : ∃ j < n, x = a + BitVec.ofNat 64 j) : ∃ j < n, x.toNat = a.toNat + j := by
  obtain ⟨j, hj, rfl⟩ := h
  refine ⟨j, hj, ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem returnSlot_byte [Bindings] {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (ha : AgreesExcept (callChanges s output message.size) s t) (i : Nat) (hi : i < 8) :
    t.external[stackPtr s + BitVec.ofNat 64 i]? = s.external[stackPtr s + BitVec.ofNat 64 i]? := by
  have hsl := h.stack.low
  have hcl := h.cipher.low
  have hol := h.out.low
  have hlow := h.stackLow
  simp only [stackRegion, cipherRegion, outputRegion, cipherBytes, frameBytes] at hsl hcl hol hlow
  have hx : (stackPtr s + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hinStack : (stackRegion s).Contains (stackPtr s + BitVec.ofNat 64 i).toNat := by
    simp only [stackRegion, MemoryRegion.Contains, frameBytes, hx]; omega
  apply ha.byte
  intro c hc hcover
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals try exact hcover
  · obtain ⟨j, hj, he⟩ := covers_toNat (by omega) hcover
    exact h.outStack _ (by simp only [outputRegion, MemoryRegion.Contains]; omega) hinStack
  · have hr : (rdi.read s + 0x30).toNat = (rdi.read s).toNat + 0x30 := by
      rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
    obtain ⟨j, hj, he⟩ := covers_toNat (by omega) hcover
    exact h.cipherStack _ (by simp only [cipherRegion, MemoryRegion.Contains, cipherBytes]; omega)
      hinStack
  · have hr : (rdi.read s + 0x40).toNat = (rdi.read s).toNat + 0x40 := by
      rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
    obtain ⟨j, hj, he⟩ := covers_toNat (by omega) hcover
    exact h.cipherStack _ (by simp only [cipherRegion, MemoryRegion.Contains, cipherBytes]; omega)
      hinStack
  · have hr : (stackPtr s - BitVec.ofNat 64 frameBytes).toNat = (stackPtr s).toNat - 0x1a0 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; simp [frameBytes]; omega)]
      simp [frameBytes]
    obtain ⟨j, hj, he⟩ := covers_toNat (by simp only [frameBytes] at *; omega) hcover
    simp only [frameBytes] at hj
    omega

theorem returnSlot_readable [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) : MemReadable s (stackPtr s) 8 := by
  have hsl := h.stack.low
  have hlow := h.stackLow
  simp only [stackRegion, frameBytes] at hsl hlow
  refine ⟨by omega, fun i hi ↦ ?_⟩
  have hp := h.stack.present (frameBytes + i) (by simp only [stackRegion, frameBytes]; omega)
  have he : BitVec.ofNat 64 ((stackRegion s).start + (frameBytes + i)) =
      stackPtr s + BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [stackRegion, frameBytes]
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rwa [he] at hp

theorem ret_step [Bindings] {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hbody : BodyResult s t key counter nonce output message) :
    ∃ u, Machine.step t = some (.next u) ∧ CallResult s u key counter nonce output message := by
  have htop : stackTop t = (returnBoundary s).rip := by
    change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
    rw [hbody.rsp]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 ↦ byte.getD 0) (returnSlot_byte h hbody.agrees i hi)
  have hread : MemReadable t (stackPtr t) 8 := by
    rw [hbody.rsp]
    have hr := returnSlot_readable h
    exact ⟨hr.low, fun i hi ↦ hbody.agrees.grow _ (hr.mem i hi)⟩
  have hcode : CodeIn (codeRange retAddress [0xc3]) t :=
    MemoryRoutines.Machine.program_text_slice hbody.code 0x14bb 1 (by decide +kernel)
  obtain ⟨u, hstep, hready, he⟩ := ret_effect_step retAddress t hbody.ready hcode
    ⟨⟨hbody.rip, hread⟩, by rw [htop]; exact h.returnLow⟩
  have hext : u.external = t.external := he.agrees.external (by simp [Component.Covers])
  have hrax : rax.read u = rax.read t := he.agrees.read (by simp)
  refine ⟨u, hstep, ⟨hready, ?_, he.rip.trans htop, ?_, ?_, ?_⟩⟩
  · exact he.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components t) _) hbody.code
  · exact he.writes.trans (congrArg (· + 8) hbody.rsp)
  · apply (hbody.agrees.trans he.agrees).mono
    simp [callChanges]
  · have hs := hbody.status
    split at hs <;> rename_i hacc <;> simp only [hacc, ↓reduceIte, hrax] at hs ⊢
    · exact ⟨hs.1, by rw [hext]; exact hs.2⟩
    · refine ⟨hs.1, fun a ha ↦ ?_⟩
      have hu : u.external[a]? = t.external[a]? := by rw [hext]
      rw [hu]
      exact hs.2 a ha

theorem call [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧
      CallResult s t key counter nonce output message := by
  obtain ⟨fuel, t, hrun, hbody⟩ := body (returnBoundary s) h.returnOutside h
  obtain ⟨u, hstep, hres⟩ := ret_step h hbody
  exact ⟨fuel + 1, u, hrun.returns (Returns.of_step hstep hres.rip hres.rsp), hres⟩

theorem call_advances [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallResult s t key counter nonce output message := by
  obtain ⟨fuel, t, hrun, hbody⟩ := body boundary hb h
  obtain ⟨u, hstep, hres⟩ := ret_step h hbody
  exact ⟨fuel + 1, u, hrun.trans (Advances.of_step hstep (.inl (hres.rip ▸ hne))), hres⟩

theorem advances [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    (h : CallPre s key counter nonce input output message)
    (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallResult s t key counter nonce output message :=
  call_advances boundary hb h hne

end ChaCha20Poly1305.Proofs.Callee100a80
