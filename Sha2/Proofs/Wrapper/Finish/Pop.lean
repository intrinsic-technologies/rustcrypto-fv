import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import Sha2.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Finish

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem pop_saved [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    (codeOffset stackOffset : Nat) (dst : BitVec 4)
    (dstRsp : dst.setWidth 5 ≠ 4)
    (codeBound : codeOffset + (encodePopR64 dst).length < 71757)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset (encodePopR64 dst).length =
      encodePopR64 dst) (stackBound : stackOffset ≤ 48)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 stackOffset) :
    ∃ t, State initial t v ∧
      (popR64Effect (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
        (encodePopR64 dst).length (dst.setWidth 5) s).Holds s t := by
  have initialRead := validCall_stack_sub_readable ctx.call (offset := stackOffset) (len := 8)
    (by omega) (by omega)
  have readable : MemReadable s (stackPtr s) 8 := by
    rw [rsp]
    exact ⟨initialRead.low, fun i hi => state.allocated _ (initialRead.mem i hi)⟩
  obtain ⟨t, run, ready, effect⟩ :=
    (Common.Encoding.Serialize.pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) dst dstRsp).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) codeOffset (encodePopR64 dst)
        (by omega) codeBytes) ⟨rip, readable⟩ (by
          change Extracted.textAddress + BitVec.ofNat 64 codeOffset +
            BitVec.ofNat 64 (encodePopR64 dst).length ≠ (returnBoundary initial).rip
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
            (inProgram_of_textOffset _ codeBound))
  refine ⟨t, state.of_agrees ctx run ready effect.agrees ?_ ?_, effect⟩
  · simp [WritesWithin, Effect.components, popR64Effect, Write.component, Operand.component,
      Component.Covers]
  · simp [Effect.components, popR64Effect, Write.component, Operand.component, Component.Covers]

end Sha2.Proofs.Wrapper.Finish
