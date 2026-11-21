import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import X86Proofs.Instructions.Call.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem common_return [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002fa ∨ s.RIP = 0x100305 ∨ s.RIP = 0x10030b)
    (hStack : MemReadable s (stackPtr s) 8)
    (hReturn : stackTop s = boundary.rip) (hRsp : stackPtr s + 8 = boundary.rsp)
    (hLow : boundary.rip.toNat < userAddressLimit) :
    ∃ t, Returns boundary 1 s t ∧ t.RIP = boundary.rip ∧ stackPtr t = boundary.rsp ∧
      ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      AgreesExcept [.reg 4, .rip] s t := by
  have bytes : CodeIn (codeRange s.RIP [0xc3]) s := by
    rcases hRip with h | h | h
    · rw [h]; exact program_text_slice hCode 0x2fa 1 (by decide +kernel)
    · rw [h]; exact program_text_slice hCode 0x305 1 (by decide +kernel)
    · rw [h]; exact program_text_slice hCode 0x30b 1 (by decide +kernel)
  obtain ⟨t, step, ready, effect⟩ := ret_effect_step s.RIP s hReady bytes
    ⟨⟨rfl, hStack⟩, by rw [hReturn]; exact hLow⟩
  refine ⟨t, Returns.of_step step (effect.rip.trans hReturn) (effect.writes.trans hRsp),
    effect.rip.trans hReturn, effect.writes.trans hRsp,
    ready, effect.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components s) _) hCode,
    effect.agrees⟩
end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
