import ChaCha20Poly1305.Proofs.DecryptInPlace.Regions

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable [b : Bindings] {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

omit b in
private theorem epilogueCode (code : CodeIn Decrypt.Lifted.fnCode u)
    (off len : Nat) (bound : off + len ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 off)
      (Extracted.textBytes.toListFrom off len)) u :=
  code.slice_of_section (sec := Decrypt.Lifted.textSection) (by
    change Decrypt.Lifted.textSection ∈ [Decrypt.Lifted.textSection]
    exact .head _) off len bound

private theorem normalizeStatus (outside : ¬ InProgram (returnBoundary s).rip)
    {normalize accepted : Bool} (start : AtEpilogue s u normalize accepted) :
    ∃ k v, Advances (returnBoundary s) k u v ∧ AtEpilogue s v false accepted ∧
      v.external = u.external := by
  cases normalize
  · exact ⟨0, u, (advances_zero _ _ _).2 rfl, start, rfl⟩
  · obtain ⟨v, adv, ready, effect⟩ :=
      (movzx_r32_r8_effect_step 0x1016bb 0xc0 (by decide) (by decide)).advances
        start.ready.ready (epilogueCode start.ready.code 0x16bb 3 (by decide +kernel))
        start.rip (ChaCha20Poly1305.Proofs.Wrapper.code_ne_boundary outside 0x16be (by decide))
    change (movzxR32R8Effect 0x1016bb 3 0 0 u).Holds u v at effect
    have ag : AgreesExcept [.reg 0, .rip] u v := effect.agrees
    have mem := ag.external (by simp [Component.Covers])
    have saved := savedOfAgrees ag (by decide)
    refine ⟨1, v, adv, ⟨⟨ready, SupportedSSE.of_agreesExcept ag start.ready.sse,
      CodeIn.of_external_eq mem start.ready.code⟩, effect.rip, ?_, ?_, ?_,
      ag.directionFlagClear (by decide) start.df, ?_⟩, mem⟩
    · rw [stackPtr_eq_read, ag.read (by decide), ← stackPtr_eq_read, start.rsp]
    · have status : (u.regValue .rax).setWidth 8 = (if accepted then 0 else 1) := start.status
      have written : v.regValue .rax = ((u.regValue .rax).setWidth 8).setWidth 64 :=
        effect.writes
      change (v.regValue .rax).setWidth 32 = _
      rw [written, status]
      cases accepted <;> rfl
    · exact fun r hr => (saved r hr).trans (start.saved r hr)
    · rw [mem]
      exact start.frame

theorem epilogue (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    {normalize accepted : Bool} (start : AtEpilogue s u normalize accepted) :
    ∃ n t, Returns (returnBoundary s) n u t ∧
      SupportedIntegerMachineState b.processor t ∧
      CalleeSavedRegistersUnchanged s t ∧ DirectionFlagUnset t ∧
      EntryReady Decrypt.Lifted.fnCode t ∧ t.external = u.external ∧
      (t.regValue .rax).setWidth 32 = (if accepted then 0 else 1) := by
  have outside := boundaryOutside hc
  obtain ⟨k, v, normalizeAdvance, normalized, normalizedMem⟩ := normalizeStatus outside start
  obtain ⟨w, addAdvance, addReady, addEffect⟩ :=
    (add_r64_imm8_effect_step 0x1016be 0x48 0xc4 0x48 (by decide) (by decide)
      (by decide)).advances normalized.ready.ready
      (epilogueCode normalized.ready.code 0x16be 4 (by decide +kernel)) normalized.rip
      (ChaCha20Poly1305.Proofs.Wrapper.code_ne_boundary outside 0x16c2 (by decide))
  change (addR64Imm8Effect 0x1016be 4 0x48 v).Holds v w at addEffect
  have addAgrees : AgreesExcept [.reg 4, .flags, .rip] v w := addEffect.agrees
  have addMem := addAgrees.external (by simp [Component.Covers])
  have rsp : stackPtr w = stackPtr s := by
    have written : stackPtr w = stackPtr v + 72 := addEffect.writes
    rw [written, normalized.rsp, BitVec.sub_add_cancel]
  have slot : MemReadable w (stackPtr w) 8 := by
    rw [rsp]
    have original := ChaCha20Poly1305.Proofs.Wrapper.stack_return_readable hc.stackAvailable
    refine ⟨original.low, fun i hi => ?_⟩
    rw [addMem]
    exact normalized.frame.present _ (original.mem i hi)
  have target : memLoad w.external (stackPtr w) 64 = (returnBoundary s).rip := by
    rw [rsp, addMem]
    exact returnSlotKept hc normalized.frame
  have low : (returnBoundary s).rip.toNat < 2 ^ 32 := by
    obtain ⟨ret, slot, hlow, _⟩ := hc.returnAddress
    change (memLoad s.external (s.regValue .rsp) 64).toNat < 2 ^ 32
    rw [memLoad_returnSlot slot]
    exact hlow
  obtain ⟨t, step, ready, retEffect⟩ := ret_effect_step 0x1016c2 w addReady
    (epilogueCode (CodeIn.of_external_eq addMem normalized.ready.code) 0x16c2 1 (by decide +kernel))
    ⟨⟨addEffect.rip, slot⟩, by
      change (memLoad w.external (stackPtr w) 64).toNat < 2 ^ 32
      rw [target]
      exact low⟩
  have returned : Returns (returnBoundary s) 1 w t := by
    apply Returns.of_step step
    · exact retEffect.rip.trans target
    · change stackPtr t = stackPtr s + 8
      exact (show stackPtr t = stackPtr w + 8 from retEffect.writes).trans (by rw [rsp])
  have retAgrees : AgreesExcept [.reg 4, .rip] w t := retEffect.agrees
  have agrees := addAgrees.trans retAgrees
  have saved := savedOfAgrees agrees (by decide)
  have mem := agrees.external (by simp [Component.Covers])
  have sse := SupportedSSE.of_agreesExcept agrees normalized.ready.sse
  refine ⟨k + 1 + 1, t, (normalizeAdvance.trans addAdvance).returns returned,
    ⟨ready.cpu, sse, ready.memory, ready.ready⟩,
    fun r hr => (saved r hr).trans (normalized.saved r hr),
    agrees.directionFlagClear (by decide) normalized.df,
    ⟨ready, sse, CodeIn.of_external_eq mem normalized.ready.code⟩,
    mem.trans normalizedMem, ?_⟩
  exact (agrees.read (r := 0) (by decide) : (t.regValue .rax).setWidth 32 =
    (v.regValue .rax).setWidth 32).trans normalized.status

end ChaCha20Poly1305.Proofs.DecryptInPlace
