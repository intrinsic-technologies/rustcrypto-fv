import P256.Proofs.Nonce.UpdateValue.Absorb.Buffer.State
import P256.Proofs.Nonce.UpdateValue.Absorb.Buffer.Finish

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem buffer [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (entered : Entered initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Buffered initial t state := by
  obtain ⟨fuel, u, runU, readyU, _, effectU⟩ := Buffer.run boundary pre.outerBoundary s
    (readyToStep entered.machine entered.bindingsSupported) (Buffer.code entered.loaded)
    (Buffer.block_pre pre entered)
  have writesU := Buffer.block_writes pre entered
  have frameU := Buffer.frame_after pre entered.toFrameState readyU effectU.agrees writesU
    (by simp [Buffer.effect, Effect.components, Write.component, Operand.component])
  have positionU : u.regValue .r15 = 0 :=
    (effectU.agrees.read (n := 64) (r := 15) (by
      simp [Buffer.effect, Effect.components, Write.component, Operand.component])).trans entered.position
  obtain ⟨t, runT, readyT, ripT, agreesT, positionT⟩ :=
    Buffer.finish pre frameU effectU.rip positionU
  have writesT : WritesWithin [.reg 15, .flags, .mem (stackPtr u + 231) 1, .rip]
      #v[Buffer.region initial] := by
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨Buffer.region initial, by simp, ?_⟩
    have base : stackPtr u + 168 = stackPtr initial - 320 := by
      simpa using ScalarFrame.scalar_stack_address frameU.rsp (by decide) (by decide : 168 ≤ 488)
    rw [show stackPtr u + 231 = stackPtr u + 168 + 63 by
      simp [BitVec.add_assoc], base, BitVec.add_assoc,
      show (63 : BitVec 64) = BitVec.ofNat 64 63 from rfl, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add (Buffer.region_bounded pre) (Nat.le_refl _) (Nat.le_refl _)
      (by change 63 + i < 64; omega)
  have frameT := Buffer.frame_after pre frameU readyT agreesT writesT (by simp)
  have memory := memoryWriteFrame_trans (effectU.agrees.memoryWriteFrame writesU)
    (agreesT.memoryWriteFrame writesT)
  have bytesU := Buffer.block_bytes pre entered effectU
  have bytesT : (MemoryRegion.mk (scratch initial + 168).toNat 32).HasBytes t.external state.value := by
    apply hasBytes_copy bytesU
    intro i hi
    apply agreesT.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    have rsp : stackPtr u = scratch initial := frameU.rsp
    rw [← rsp] at eq
    exact RangeApart.offsets (stackPtr u) (a := 231) (b := 168) (len := 1) (count := 32)
      (by decide) (by decide) (.inr (by decide)) j hj i hi eq.symm
  have hmac : HMAC.HmacStateAt t (scratch initial + 104) state.key state.value := by
    apply hmacStateAt_absorb_short entered.hmac (by rw [entered.drbg.value_size]; decide)
    · simpa [entered.drbg.value_size, BitVec.add_assoc] using bytesT
    · simpa [entered.drbg.value_size, frameU.rsp, scratch, BitVec.add_assoc] using positionT
    · exact Buffer.hmac_preserved pre memory
  refine ⟨fuel + 3, t, runU.trans runT, frameT, ripT, ?_, Buffer.drbg_after pre entered.drbg memory, hmac⟩
  exact (agreesT.read (n := 64) (r := 3) (by simp)).trans
    ((effectU.agrees.read (n := 64) (r := 3) (by
      simp [Buffer.effect, Effect.components, Write.component, Operand.component])).trans entered.valuePointer)

end P256.Proofs.Nonce.UpdateValue.Absorb
