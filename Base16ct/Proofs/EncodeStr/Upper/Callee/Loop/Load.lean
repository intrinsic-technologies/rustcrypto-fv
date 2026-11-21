import Base16ct.Proofs.EncodeStr.Upper.Callee.State
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_loop_load [Bindings] (c : CallContext) {i : Nat} {s : RamState}
    (hs : LoopState c i s) (hi : i < c.input.length)
    (hread : MemReadable s (c.initial.regValue .rdi + BitVec.ofNat 64 i) 1)
    (hbyte : memLoad s.external (c.initial.regValue .rdi + BitVec.ofNat 64 i) 8 =
      (c.input.getD i 0).toBitVec) :
    ∃ t, Advances (returnBoundary c.initial) 1 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 9, .rip] s t ∧ t.RIP = 0x1005f5 ∧
      t.regValue .r9 = (c.input.getD i 0).toBitVec.setWidth 64 := by
  have hstep : StepEffect
      (LoadPre 0x1005f0 (fun t ↦
        (AddrMode.sib 6 (some 8) 0 .none).addr t 0x1005f5) 1)
      (codeRange 0x1005f0 [0x46, 0x0f, 0xb6, 0x0c, 0x06])
      (movzxR32M8Effect 0x1005f0 5 9 (.sib 6 (some 8) 0 .none)) :=
    movzx_r_m8_rex_effect_step 0x1005f0 0x46
      (by unfold RexPrefix; decide +kernel) 32 (Or.inr rfl) (by intro seg; rfl)
      1 (.sib 6 (some 8) 0 .none) (by unfold AddrMode.Valid; decide +kernel) rfl rfl
  have hcode : CodeIn (codeRange 0x1005f0 [0x46, 0x0f, 0xb6, 0x0c, 0x06]) s := by
    have he : Extracted.textBytes.toListFrom 0x5f0 5 =
        [0x46, 0x0f, 0xb6, 0x0c, 0x06] := by decide +kernel
    simpa only [he, show Extracted.textAddress + BitVec.ofNat 64 0x5f0 =
      (0x1005f0 : BitVec 64) by decide +kernel] using program_text_slice hs.invariant.code 0x5f0 5 (by decide +kernel)
  have haddr : (AddrMode.sib 6 (some 8) 0 .none).addr s 0x1005f5 =
      c.initial.regValue .rdi + BitVec.ofNat 64 i := by
    change s.regValue .rsi + (s.regValue .r8 <<< (0 : Nat)) + 0 = _
    simp only [BitVec.shiftLeft_zero, hs.src, hs.index]
    exact BitVec.add_zero _
  have hpre : LoadPre 0x1005f0 (fun t ↦
      (AddrMode.sib 6 (some 8) 0 .none).addr t 0x1005f5) 1 s := by
    refine ⟨?_, ?_⟩
    · simpa only [ite_eq_left hi] using hs.rip
    · simpa only [haddr] using hread
  have hne : (movzxR32M8Effect 0x1005f0 5 9 (.sib 6 (some 8) 0 .none) s).rip ≠
      (returnBoundary c.initial).rip :=
    text_address_ne_return (returnBoundary_valid c.valid.stack c.valid.returnAddress).2
      0x5f5 (by decide +kernel)
  obtain ⟨t, ha, hr, he⟩ := hstep.advances hs.invariant.ready hcode hpre hne
  refine ⟨t, ha, hr, he.agrees, he.rip, ?_⟩
  have hw := he.writes
  change t.regValue .r9 = _ at hw
  change t.regValue .r9 =
    (memLoad s.external ((AddrMode.sib 6 (some 8) 0 .none).addr s 0x1005f5) 8).setWidth 64 at hw
  simpa only [haddr, hbyte] using hw

end Base16ct.Proofs.EncodeStr.Upper
