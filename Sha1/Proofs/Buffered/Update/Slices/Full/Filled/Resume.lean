import Sha1.Proofs.Buffered.Update.Slices.Full.Contracts
import Sha1.Proofs.Buffered.DigestPrepare.Initialize.Store8
import Sha1.Proofs.Buffered.DigestPrepare.Position
import Sha1.Proofs.Buffered.Update.Memory
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.MemoryRoutines.Register.Compose
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Buffered.Update.Slices.Full.Filled

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

open Sha1.Proofs.Compress.Machine (AdvancesBlock program_text_slice)
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

structure AfterCompress [Bindings] (boundary : ReturnBoundary) (message input : ByteArray)
    (s u : RamState) : Prop where
  advances : ∃ n, Advances boundary n s u
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  rip : u.RIP = 0x101d51
  agrees : AgreesExcept (UpdateKind.updateFinalize.changes s) s u
  next : (Operand.reg 3 : Operand 64).read u =
    (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 (64 - message.size % 64)
  remaining : (Operand.reg 5 : Operand 64).read u = BitVec.ofNat 64 (input.size - (64 - message.size % 64))
  state : (⟨(UpdateKind.updateFinalize.context s + 72).toNat, 20⟩ : MemoryRegion).HasBytes
    u.external (absorbedStateBytes (message ++ input.extract 0 (64 - message.size % 64)))
  counter : (Operand.mem (UpdateKind.updateFinalize.context s + 64) : Operand 64).read u =
    BitVec.ofNat 64 (message.size / 64 + 1)

private theorem clear_position [Bindings] {boundary : ReturnBoundary} {u : RamState}
    (hout : ¬ InProgram boundary.rip) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hip : u.RIP = 0x101d51)
    (hw : MemoryRoutines.WritableRange u (stackPtr u + 279) 1) :
    ∃ t, Advances boundary 1 u t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101d59 ∧ AgreesExcept [.mem (stackPtr u + 279) 1, .rip] u t := by
  let addr (v : RamState) := stackPtr v + 279
  let effect := storeEffect 0x101d51 8 addr (fun _ ↦ (0 : BitVec 8))
  have hstep := DigestPrepare.Initialize.mov_m8_imm8_effect_step 0x101d51
    (.sib 4 none 0 (.d32 279)) (by decide) (by decide) (by decide) 0
  change StepEffect (Common.Instructions.StorePre.StorePre 0x101d51 8 addr 1)
    (codeRange 0x101d51 [0xc6, 0x84, 0x24, 0x17, 1, 0, 0, 0]) effect at hstep
  have hb := program_text_slice hc 0x1d51 8 (by decide +kernel)
  have hp : Common.Instructions.StorePre.StorePre 0x101d51 8 addr 1 u :=
    ⟨hip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩,
      rangeApart_text hw.code (by decide +kernel : 0x1d51 + 8 ≤ Extracted.textBytes.size)⟩
  obtain ⟨t, ha, ht, he⟩ := hstep.advances hr hb hp
    (text_address_ne_return hout 0x1d59 (by decide +kernel))
  have hcomponents : (effect u).components = [.mem (stackPtr u + 279) 1, .rip] := by
    simp only [effect, addr, storeEffect_components]
  exact ⟨t, ha, ht, he.codeIn (DigestPrepare.store_avoids_program hcomponents hw.code) hc,
    he.rip, hcomponents ▸ he.agrees⟩

private def resumeBytes : List UInt8 :=
  [0x49, 0x89, 0xde, 0x48, 0x89, 0xea, 0x48, 0xc1, 0xea, 0x06]

private def resumeEffect (s : RamState) : Effect where
  rip := 0x101d63
  writes := [⟨(.reg 14 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), (Operand.reg 5 : Operand 64).read s >>> 6⟩]
  flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((Operand.reg 5 : Operand 64).read s))

private theorem resume_registers [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) : AdvancesBlock boundary (fun s ↦ s.RIP = 0x101d59)
      (codeRange 0x101d59 resumeBytes) resumeEffect := by
  unfold resumeBytes
  md5_run_begin mov_r64_r64_effect_step 0x101d59 0x49 0xde
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d5c (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101d5c 0x48 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d59) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d5f (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x101d5f 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d59) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d63 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resumeEffect, shiftCount]
  · x86_norm [resumeEffect, shiftCount]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [resumeEffect, shiftCount] <;> rfl
  · x86_norm [resumeEffect, shiftCount] <;> rfl

theorem resume [Bindings] {boundary : ReturnBoundary} {message input : ByteArray} {s u : RamState}
    (h : UpdatePre .updateFinalize boundary message input s)
    (b : AfterCompress boundary message input s u) (hsize : 64 - message.size % 64 ≤ input.size) :
    ∃ v, BatchReady boundary message input s (64 - message.size % 64) v := by
  let offset := 64 - message.size % 64
  let base := UpdateKind.updateFinalize.context s
  let blocks := (input.size - offset) / 64
  have hsp : stackPtr u = stackPtr s :=
    b.agrees.read (n := 64) (r := 4) (by simp [UpdateKind.changes, UpdateKind.workRegisters])
  have hpos : stackPtr u + 279 = base + 63 := by
    rw [hsp]
    change stackPtr s + 279 = stackPtr s + 216 + 63
    rw [BitVec.add_assoc]
    rfl
  have hhigh : (stackPtr s).toNat + 216 + 92 < 2^32 := h.stackHigh
  have hbase : base.toNat = (stackPtr s).toNat + 216 := toNat_add_ofNat _ 216 (by omega)
  have hpn : (stackPtr u + 279).toNat = (stackPtr s).toNat + 279 := by
    rw [hsp]
    exact toNat_add_ofNat _ 279 (by omega)
  have hw : MemoryRoutines.WritableRange u (stackPtr u + 279) 1 := by
    refine DigestPrepare.writableRange_of_region ?_
      (Update.allocated_of_agrees b.agrees h.contextAllocated) h.contextAvoids ?_ ?_
    · change base.toNat + 92 < 2^32
      omega
    · change base.toNat ≤ _
      omega
    · change _ ≤ base.toNat + 92
      omega
  obtain ⟨w, hClear, wReady, wCode, wRip, hStore⟩ :=
    clear_position (boundary := boundary) h.boundaryOutside b.ready b.code b.rip hw
  rw [hpos] at hStore
  have countCode : CodeIn (codeRange 0x101d59 resumeBytes) w :=
    program_text_slice wCode 0x1d59 10 (by decide +kernel)
  obtain ⟨_, t, hCount, tReady, _, ht⟩ :=
    resume_registers boundary h.boundaryOutside w wReady countCode wRip
  have hRemaining : (Operand.reg 5 : Operand 64).read w = BitVec.ofNat 64 (input.size - offset) :=
    (hStore.read (by simp)).trans b.remaining
  have hRemainingBound : input.size - offset < 2^64 := by have := h.totalSize; omega
  have hBlocksBound : blocks < 2^64 := by dsimp only [blocks]; omega
  have hBlockCount : (Operand.reg 5 : Operand 64).read w >>> 6 = BitVec.ofNat 64 blocks := by
    rw [hRemaining]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hRemainingBound, Nat.mod_eq_of_lt hBlocksBound, blocks]
  have hZero : (BitVec.ofNat 64 blocks = 0) ↔ blocks = 0 := by
    constructor
    · intro he
      have hn := congrArg BitVec.toNat he
      change (BitVec.ofNat 64 blocks).toNat = 0 at hn
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hBlocksBound] using hn
    · intro he
      rw [he]
      rfl
  have hCond : condHolds 4 (StatusFlags.ofRFLAGS t.RFLAGS) = (BitVec.ofNat 64 blocks == 0) := by
    have hz := ht.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      ((Operand.reg 5 : Operand 64).read w >>> 6 == 0) at hz
    rw [condHolds_4, hz, hBlockCount]
  have hNext : (jccEffect 0x101d63 2 4 ((0x18#8).signExtend 64) t).rip =
      if blocks = 0 then 0x101d7d else 0x101d65 := by
    simp only [jccEffect, hCond, branchEffect, beq_iff_eq, hZero]
    split <;> rfl
  have hNextOutside : (jccEffect 0x101d63 2 4 ((0x18#8).signExtend 64) t).rip ≠ boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return h.boundaryOutside 0x1d7d (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1d65 (by decide +kernel)
  have tCode := ht.agrees.codeIn (by simp [resumeEffect, Effect.components, Component.Covers]) wCode
  have branchCode : CodeIn (codeRange 0x101d63 [0x74, 0x18]) t :=
    program_text_slice tCode 0x1d63 2 (by decide +kernel)
  obtain ⟨v, hBranch, vReady, hv⟩ := (jcc_rel8_effect_step 0x101d63 4 0x18).advances
    tReady branchCode ⟨ht.rip, fun _ ↦ by decide +kernel⟩ hNextOutside
  have hBranchAgrees : AgreesExcept [.rip] t v := hv.agrees
  have hCountAgrees : AgreesExcept [.reg 14, .reg 2, .flags, .rip] w t := ht.agrees
  have hRegisters : AgreesExcept [.reg 14, .reg 2, .flags, .rip] w v :=
    (hCountAgrees.trans hBranchAgrees).mono (by simp)
  have hFrame : AgreesExcept (UpdateKind.updateFinalize.changes s) u v := by
    apply (hStore.trans hRegisters).widen
    · intro c hc hn
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [UpdateKind.changes, UpdateKind.workRegisters, Component.isMem] at hn ⊢
    · intro x c hc hx
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hx.elim
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨.mem base 92, by simp [base, UpdateKind.changes], 63 + i, by omega,
        by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl⟩
  have hByte {i : Nat} (hlo : 63 < i) (hhi : i < 92) :
      v.external[base + BitVec.ofNat 64 i]? = u.external[base + BitVec.ofNat 64 i]? := by
    have hExternal := hRegisters.external (by simp [Component.Covers])
    rw [hExternal]
    apply hStore.byte
    intro c hc hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := hx
      rw [show j = 0 by omega] at he
      change base + BitVec.ofNat 64 i = base + 63 + 0#64 at he
      rw [BitVec.add_zero] at he
      have hn := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp he)
      change (BitVec.ofNat 64 i).toNat = 63 at hn
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64)] at hn
      omega
    · exact hx
  obtain ⟨_, hEntry⟩ := b.advances
  refine ⟨v, ⟨⟨⟨_, ((hEntry.trans hClear).trans hCount).trans hBranch⟩, vReady,
    hv.codeIn (branchEffect_avoids _ _ _ _) tCode, (b.agrees.trans hFrame).mono (by simp),
    hsize, ?_, ?_⟩, hv.rip.trans hNext, ?_, ?_, ?_, ?_⟩⟩
  · exact (hBranchAgrees.read (by decide)).trans
      (ht.writes.1.trans ((hStore.read (by simp)).trans b.next))
  · exact (hRegisters.read (by decide)).trans hRemaining
  · exact (hBranchAgrees.read (by decide)).trans (ht.writes.2.trans hBlockCount)
  · omega
  · refine ⟨b.state.1, fun i ↦ Eq.trans ?_ (b.state.2 i)⟩
    have hi : i.val < 20 := (absorbedStateBytes_size _) ▸ i.isLt
    simpa only [base, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using hByte (i := 72 + i.val) (by omega) (by omega)
  · have hquot : (message.size + offset) / 64 = message.size / 64 + 1 := by
      dsimp only [offset]
      omega
    rw [hquot, ← b.counter]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change v.external[base + 64 + BitVec.ofNat 64 i]? = u.external[base + 64 + BitVec.ofNat 64 i]?
    simpa only [base, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      hByte (i := 64 + i) (by omega) (by omega)

end Sha1.Proofs.Buffered.Update.Slices.Full.Filled
