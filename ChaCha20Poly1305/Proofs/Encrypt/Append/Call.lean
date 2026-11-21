import ChaCha20Poly1305.Proofs.Encrypt.Append.Prefix
import ChaCha20Poly1305.Proofs.MemoryContracts

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine Core.Absorb

theorem append_memcpy_entry [Bindings] {s u : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip)
    (atCopy : AppendAtCopy s u buffer length) :
    ∃ c, Advances boundary 1 u c ∧ ReadyToStep c ∧ CodeIn Extracted.programImage c ∧
      c.RIP = 0x102dc0 ∧ stackPtr c = stackPtr s - BitVec.ofNat 64 48 ∧
      returnBoundary c = { rip := 0x101fe2, rsp := stackPtr s - BitVec.ofNat 64 40 } ∧
      AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c := by
  have hav := pre.separation.2.2 (Stack.region s 48) (by simp)
  have pa : pushAddr u = stackPtr s - BitVec.ofNat 64 48 := by
    rw [pushAddr, atCopy.rsp]
    bv_omega
  have target : callMemPtr 0x101fdc (.rip 0xff3c6) u = 0x102dc0 := by
    exact MemoryContracts.memcpy_slot u atCopy.code
  have cp : CallMemPre 0x101fdc (.rip 0xff3c6) u := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact stack_store_pre pre.stack hav atCopy.agrees.grow (by omega) atCopy.rip pa
        (code_inProgram 0x1fdc 6 (by omega))
    · rw [target]; decide
    · exact rodata_readable atCopy.code 0x13a8 (by decide +kernel)
  obtain ⟨c, adv, ready, eff⟩ :=
    (call_m64_effect_step 0x101fdc (.rip 0xff3c6) trivial rfl rfl).advances atCopy.ready
      (program_text_slice atCopy.code 0x1fdc 6 (by decide +kernel)) cp
      (by change callMemPtr 0x101fdc (.rip 0xff3c6) u ≠ boundary.rip
          rw [target]; exact code_ne_boundary outside 0x2dc0 (by omega))
  have code : CodeIn Extracted.programImage c := by
    apply eff.codeIn _ atCopy.code
    intro x hx c hc hcover
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover.elim
    · rw [pa] at hcover
      exact stack_slot_avoids pre.stack hav (by omega) x.1 hcover (inProgram_of_mem hx)
    · exact hcover.elim
  refine ⟨c, adv, ready, code, eff.rip.trans target, (callEffect_rsp eff).trans pa, ?_, ?_⟩
  · rw [callEffect_returnBoundary eff, atCopy.rsp]
    rfl
  · have h := eff.agrees
    simpa only [pushEffect_components, pa] using h

end ChaCha20Poly1305.Proofs.Encrypt
