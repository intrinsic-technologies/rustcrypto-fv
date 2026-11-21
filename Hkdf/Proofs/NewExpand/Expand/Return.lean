import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import Hkdf.Proofs.Common.Memory.Copy.Return
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm32.Triple
import X86Proofs.Instructions.Setcc.Generated.R8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

variable [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
  {key info : ByteArray} {ptr : BitVec 64} {length : Nat}

private def lengthAddress : AddrMode := .sib 4 none 0 (.d32 224)

private theorem statusSteps (pre : ExpandPre entry boundary key info ptr length)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f290) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10f29f ∧
      AgreesExcept [.flags, .rip, .reg 0, .rip] s t ∧
      (t.regValue .rax).setWidth 8 = (if 8160 < length then 1 else 0) := by
  have code := programLoaded_codeIn saved.loaded
  have lengthReadable : MemReadable s (lengthAddress.addr s 0x10f29c) 8 := by
    change MemReadable s (s.regValue .rsp + 224) 8
    rw [saved.sp, show entry.regValue .rsp - 536 + 224 = stackPtr entry - 312 from
      by simp only [stackPtr_eq_regValue_rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl]
    exact Common.CallFrame.stack_readable pre.call.stack saved.allocated (by decide) (by decide)
  have cmpCode : CodeIn (codeRange 0x10f290 [0x48, 0x81, 0xbc, 0x24, 0xe0, 0, 0, 0, 0xe1, 0x1f, 0, 0]) s :=
    programText_slice code 0xf290 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨u, cmpRun, cmpReady, cmpEffect⟩ :=
    (cmp_m64_imm32_effect_step 0x10f290 0x48 (by simp [RexWPrefix])
      lengthAddress (by decide) rfl rfl 8161).advances
      (supportedMachine_readyToStep saved.machine) cmpCode ⟨pc, lengthReadable⟩
      (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xf29c (by decide)))
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = decide (length < 8161) := by
    have cf : (StatusFlags.ofRFLAGS u.RFLAGS).CF = decide ((slot s 224).toNat < 8161) :=
      cmpEffect.flags.1
    rw [cf, saved.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    simpa only [← pre.lengthArg] using (entry.regValue .r8).isLt
  have condition : condHolds 3 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (8160 < length) := by
    rw [condHolds_3, carry, ← decide_not]
    have equivalent : ¬ length < 8161 ↔ 8160 < length := by omega
    simp only [equivalent]
  have memory : u.external = s.external := cmpEffect.agrees.external (by simp [Component.Covers])
  have setCode : CodeIn (codeRange 0x10f29c [0x0f, 0x93, 0xc0]) u :=
    programText_slice (code.of_external_eq memory) 0xf29c _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t, setRun, setReady, setEffect⟩ :=
    (setcc_r8_effect_step 0x10f29c 3 0xc0 (by decide) (by decide) (decide (8160 < length))).advances
      cmpReady setCode ⟨cmpEffect.rip, condition⟩
      (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xf29f (by decide)))
  refine ⟨t, cmpRun.trans setRun, setReady, setEffect.rip,
    cmpEffect.agrees.trans setEffect.agrees, ?_⟩
  have write : t.regValue .rax = mergeGPR 8 (if decide (8160 < length) then 1 else 0)
      (u.regValue .rax) := setEffect.writes
  rw [write, setWidth_mergeGPR8]
  by_cases over : 8160 < length <;> simp [over]

theorem finish (pre : ExpandPre entry boundary key info ptr length)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f290)
    (output : length ≤ 8160 → ∃ bytes, RFC5869.expandFromPrk .sha256 key info length = .ok bytes ∧
      (registerRegion entry .rcx length).HasBytes s.external bytes) :
    ∃ final, ExpandResult entry final boundary key info length := by
  have code := programLoaded_codeIn saved.loaded
  have hRead (offset : Nat) (within : offset ≤ 2264) :
      MemReadable s (stackPtr entry - BitVec.ofNat 64 offset) 8 :=
    Common.CallFrame.stack_readable pre.call.stack saved.allocated within (by omega)
  have savedAt (offset : BitVec 64) (n : Nat) (eq : (536 : BitVec 64) - offset = BitVec.ofNat 64 n) :
      slot s offset = memLoad s.external (stackPtr entry - BitVec.ofNat 64 n) 64 := by
    unfold slot
    change memLoad s.external (s.regValue .rsp + offset) 64 = _
    have address : s.regValue .rsp + offset = stackPtr entry - BitVec.ofNat 64 n := by
      rw [saved.sp, stackPtr_eq_regValue_rsp, ← eq]
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
    rw [address]
  obtain ⟨t₀, statusRun, statusReady, statusRip, statusEffect, statusValue⟩ := statusSteps pre saved pc
  have mem₀ : t₀.external = s.external := statusEffect.external (by simp [Component.Covers])
  have addCode : CodeIn (codeRange 0x10f29f [0x48, 0x81, 0xc4, 0xe8, 1, 0, 0]) t₀ :=
    programText_slice (code.of_external_eq mem₀) 0xf29f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t₁, addRun, addReady, addEffect⟩ :=
    (add_r64_imm32_effect_step 0x10f29f 0x48 0xc4 488
      (by simp [RexWPrefix]) (by decide) (by decide)).advances statusReady addCode statusRip
      (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xf2a6 (by decide)))
  have sp₁ : stackPtr t₁ = stackPtr entry - 48 := by
    have write : stackPtr t₁ = stackPtr t₀ + 488 := addEffect.writes
    have preserved : stackPtr t₀ = stackPtr s := statusEffect.read (n := 64) (r := 4) (by decide)
    rw [write, preserved, stackPtr_eq_regValue_rsp s, saved.sp, stackPtr_eq_regValue_rsp entry]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have mem₁ : t₁.external = s.external :=
    (addEffect.agrees.external (by simp [Component.Covers])).trans mem₀
  have pop {u : RamState} (off : Nat) (dst : BitVec 4) (depth slotOffset : Nat)
      (dstNE : dst.setWidth 5 ≠ 4) (depthLow : depth ≤ 2264) (depthHigh : 8 ≤ depth)
      (slotEq : (536 : BitVec 64) - BitVec.ofNat 64 slotOffset = BitVec.ofNat 64 depth)
      (ready : ReadyToStep u) (rip : u.RIP = Extracted.textAddress + BitVec.ofNat 64 off)
      (sp : stackPtr u = stackPtr entry - BitVec.ofNat 64 depth)
      (memory : u.external = s.external)
      (fetch : Extracted.textBytes.toListFrom off (encodePopR64 dst).length = encodePopR64 dst)
      (inText : off + (encodePopR64 dst).length < 115149) :
      ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧
        v.RIP = Extracted.textAddress + BitVec.ofNat 64 (off + (encodePopR64 dst).length) ∧
        stackPtr v = stackPtr entry - BitVec.ofNat 64 (depth - 8) ∧ v.external = s.external ∧
        (Operand.reg (dst.setWidth 5) : Operand 64).read v = slot s (BitVec.ofNat 64 slotOffset) ∧
        AgreesExcept [.reg (dst.setWidth 5), .reg 4, .rip] u v := by
    have read : MemReadable u (stackPtr u) 8 := sp ▸ (hRead depth depthLow).of_external_eq memory
    have bytes := programText_slice (code.of_external_eq memory) off
      (encodePopR64 dst) (Nat.le_of_lt inText) fetch
    have continues := boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset
      (off + (encodePopR64 dst).length) inText)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at continues
    obtain ⟨v, step, nextReady, effect⟩ :=
      (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step
        (Extracted.textAddress + BitVec.ofNat 64 off) dst dstNE).advances ready bytes
          ⟨rip, read⟩ continues
    refine ⟨v, step, nextReady, ?_, ?_,
      (effect.agrees.external (by simp [Component.Covers])).trans memory, ?_, effect.agrees⟩
    · have next : v.RIP = Extracted.textAddress + BitVec.ofNat 64 off
          + BitVec.ofNat 64 (encodePopR64 dst).length := effect.rip
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using next
    · have h := effect.writes.2
      change stackPtr v = stackPtr u + 8 at h
      rw [h, sp, ← BitVec.ofNat_sub_ofNat_of_le depth 8 (by omega) depthHigh]
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
      rfl
    · have h := effect.writes.1
      change (Operand.reg (dst.setWidth 5) : Operand 64).read v =
        memLoad u.external (stackPtr u) 64 at h
      rw [h, sp, memory, savedAt _ _ slotEq]
  obtain ⟨t₂, pop₂, ready₂, rip₂, sp₂, mem₂, reg₂, agree₂⟩ :=
    pop 0xf2a6 3 48 488 (by decide) (by decide) (by decide) (by decide)
      addReady addEffect.rip sp₁ mem₁ (by decide +kernel) (by decide)
  obtain ⟨t₃, pop₃, ready₃, rip₃, sp₃, mem₃, reg₃, agree₃⟩ :=
    pop 0xf2a7 12 40 496 (by decide) (by decide) (by decide) (by decide)
      ready₂ rip₂ sp₂ mem₂ (by decide +kernel) (by decide)
  obtain ⟨t₄, pop₄, ready₄, rip₄, sp₄, mem₄, reg₄, agree₄⟩ :=
    pop 0xf2a9 13 32 504 (by decide) (by decide) (by decide) (by decide)
      ready₃ rip₃ sp₃ mem₃ (by decide +kernel) (by decide)
  obtain ⟨t₅, pop₅, ready₅, rip₅, sp₅, mem₅, reg₅, agree₅⟩ :=
    pop 0xf2ab 14 24 512 (by decide) (by decide) (by decide) (by decide)
      ready₄ rip₄ sp₄ mem₄ (by decide +kernel) (by decide)
  obtain ⟨t₆, pop₆, ready₆, rip₆, sp₆, mem₆, reg₆, agree₆⟩ :=
    pop 0xf2ad 15 16 520 (by decide) (by decide) (by decide) (by decide)
      ready₅ rip₅ sp₅ mem₅ (by decide +kernel) (by decide)
  obtain ⟨t₇, pop₇, ready₇, rip₇, sp₇, mem₇, reg₇, agree₇⟩ :=
    pop 0xf2af 5 8 528 (by decide) (by decide) (by decide) (by decide)
      ready₆ rip₆ sp₆ mem₆ (by decide +kernel) (by decide)
  have lastSp : stackPtr t₇ = stackPtr entry := by
    change stackPtr t₇ = stackPtr entry - 0 at sp₇
    exact sp₇.trans (BitVec.sub_zero _)
  have retRead : MemReadable t₇ (stackPtr t₇) 8 := by
    rw [lastSp]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using (hRead 0 (by decide)).of_external_eq mem₇
  have top : stackTop t₇ = (returnBoundary entry).rip := by
    change memLoad t₇.external (stackPtr t₇) 64 = _
    rw [lastSp, mem₇, ← BitVec.sub_zero (stackPtr entry)]
    exact (savedAt 536 0 (by decide)).symm.trans saved.ret
  have retCode : CodeIn (codeRange 0x10f2b0 [0xc3]) t₇ :=
    programText_slice (code.of_external_eq mem₇) 0xf2b0 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨final, retRun, retReady, retEffect⟩ := (ret_effect_step 0x10f2b0).advances ready₇ retCode
    ⟨⟨rip₇, retRead⟩, top ▸ Common.Memory.Copy.inProgram_low pre.call.returnInProgram⟩
    (top ▸ boundary_ne_program pre.call.outerBoundary pre.call.returnInProgram)
  have memory : final.external = s.external :=
    (retEffect.agrees.external (by simp [Component.Covers])).trans mem₇
  have after₇ : AgreesExcept [.reg 4, .rip] t₇ final := retEffect.agrees
  have after₆ := agree₇.trans after₇
  have after₅ := agree₆.trans after₆
  have after₄ := agree₅.trans after₅
  have after₃ := agree₄.trans after₄
  have after₂ := agree₃.trans after₃
  have addAgrees : AgreesExcept [.reg 4, .flags, .rip] t₀ t₁ := addEffect.agrees
  have after₀ := addAgrees.trans (agree₂.trans after₂)
  have agrees := statusEffect.trans after₀
  obtain ⟨fuel, execution⟩ := saved.execution
  refine ⟨final, ⟨⟨fuel + 10, ?_⟩, retEffect.rip.trans top, ?_,
    supportedMachine_of_ready_agrees saved.machine retReady agrees, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ((((((((execution.trans statusRun).trans addRun).trans pop₂).trans pop₃).trans pop₄).trans
      pop₅).trans pop₆).trans pop₇).trans retRun
  · change stackPtr final = stackPtr entry + 8
    have write : stackPtr final = stackPtr t₇ + 8 := retEffect.writes
    rw [write, lastSp]
  · refine ⟨?_, agrees.directionFlagClear (by decide) saved.directionFlag,
      (agrees.mxcsr (by decide)).trans saved.mxcsr, (agrees.fcw (by decide)).trans saved.fcw⟩
    intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (after₂.read (n := 64) (r := 3) (by decide)).trans (reg₂.trans saved.rbx)
    · exact (after₇.read (n := 64) (r := 5) (by decide)).trans (reg₇.trans saved.rbp)
    · exact (after₃.read (n := 64) (r := 12) (by decide)).trans (reg₃.trans saved.r12)
    · exact (after₄.read (n := 64) (r := 13) (by decide)).trans (reg₄.trans saved.r13)
    · exact (after₅.read (n := 64) (r := 14) (by decide)).trans (reg₅.trans saved.r14)
    · exact (after₆.read (n := 64) (r := 15) (by decide)).trans (reg₆.trans saved.r15)
  · simpa only [MemoryWriteFrame, memory] using saved.frame
  · intro address byte fetch
    rw [memory]
    exact saved.loaded address byte fetch
  · intro address allocated
    rw [memory]
    exact saved.allocated address allocated
  · have same : final.regValue .rax = t₀.regValue .rax := after₀.read (n := 64) (r := 0) (by decide)
    rw [same, statusValue]
  · rw [memory]
    exact output

end Hkdf.Proofs.NewExpand.Expand
