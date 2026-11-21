import Sha1.Proofs.Buffered.DigestContracts
import Sha1.Proofs.Buffered.Finalize.Digest
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Common.Output
import Sha1.Proofs.Buffered.DigestFinish.Output
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Sha1.Proofs.Buffered

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST Standards.NIST.SHA1 Standards.NIST.SHA2
open Sha1.Proofs.Compress.Machine Sha1.Proofs.Buffered.DigestFinish

theorem digest_text_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

theorem digest_epilogue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002a2)
    (hSlots : ∀ i < 5, MemReadable s (stackPtr s + BitVec.ofNat 64 (280 + 8 * i)) 8)
    (hReturn : boundary.rip = (Operand.mem (stackPtr s + 312) : Operand 64).read s)
    (hRsp : boundary.rsp = stackPtr s + 320)
    (hLow : boundary.rip.toNat < userAddressLimit)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Returns boundary 6 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 3, .reg 4, .reg 12, .reg 14, .reg 15, .flags, .rip] s t ∧
      t.regValue .rbx = (Operand.mem (stackPtr s + 280) : Operand 64).read s ∧
      t.regValue .r12 = (Operand.mem (stackPtr s + 288) : Operand 64).read s ∧
      t.regValue .r14 = (Operand.mem (stackPtr s + 296) : Operand 64).read s ∧
      t.regValue .r15 = (Operand.mem (stackPtr s + 304) : Operand 64).read s := by
  have hb0 : CodeIn (codeRange 0x1002a2 [0x48, 0x81, 0xc4, 0x18, 0x01, 0x00, 0x00]) s :=
    program_text_slice hCode 0x2a2 7 (by decide +kernel)
  obtain ⟨s1, ha1, hr1, he1⟩ :=
    (add_r64_imm32_effect_step 0x1002a2 0x48 0xc4 0x118
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hReady hb0 hRip (digest_text_ne_return hOutside 0x2a9 (by decide +kernel))
  change (addR64Imm32Effect 0x1002a2 4 280 s).Holds s s1 at he1
  have hs1 : stackPtr s1 = stackPtr s + 280 := he1.writes
  have hm1 : s1.external = s.external := he1.agrees.external (by simp [Component.Covers])
  have hc1 := he1.codeIn (addR64Imm32Effect_avoids _ _ _ _ _) hCode
  have hb1 : CodeIn (codeRange 0x1002a9 [0x5b]) s1 :=
    program_text_slice hc1 0x2a9 1 (by decide +kernel)
  have hp1 : PopPre 0x1002a9 s1 := by
    refine ⟨he1.rip, ?_⟩
    rw [hs1]
    exact (hSlots 0 (by decide +kernel)).of_external_eq hm1
  obtain ⟨s2, ha2, hr2, he2⟩ :=
    (pop_r64_effect_step 0x1002a9 0x5b
      (by decide +kernel) (by decide +kernel)).advances hr1 hb1 hp1
      (digest_text_ne_return hOutside 0x2aa (by decide +kernel))
  change (popR64Effect 0x1002a9 1 3 s1).Holds s1 s2 at he2
  have hs2 : stackPtr s2 = stackPtr s + 288 := by
    have h := he2.writes.2
    change stackPtr s2 = stackPtr s1 + 8 at h
    rw [hs1, BitVec.add_assoc] at h
    exact h
  have hm2 : s2.external = s.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hc2 := he2.codeIn (popR64Effect_avoids _ _ _ _ _) hc1
  have hv3 : (Operand.reg 3 : Operand 64).read s2 =
      (Operand.mem (stackPtr s + 280) : Operand 64).read s := by
    have h := he2.writes.1
    simpa only [hs1, Operand.read, hm1] using h
  have hb2 : CodeIn (codeRange 0x1002aa [0x41, 0x5c]) s2 :=
    program_text_slice hc2 0x2aa 2 (by decide +kernel)
  have hp2 : PopPre 0x1002aa s2 := by
    refine ⟨he2.rip, ?_⟩
    rw [hs2]
    exact (hSlots 1 (by decide +kernel)).of_external_eq hm2
  obtain ⟨s3, ha3, hr3, he3⟩ :=
    (pop_r64_rex_effect_step 0x1002aa 0x41 0x5c
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr2 hb2 hp2 (digest_text_ne_return hOutside 0x2ac (by decide +kernel))
  change (popR64Effect 0x1002aa 2 12 s2).Holds s2 s3 at he3
  have hs3 : stackPtr s3 = stackPtr s + 296 := by
    have h := he3.writes.2
    change stackPtr s3 = stackPtr s2 + 8 at h
    rw [hs2, BitVec.add_assoc] at h
    exact h
  have hm3 : s3.external = s.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hc3 := he3.codeIn (popR64Effect_avoids _ _ _ _ _) hc2
  have hv12 : (Operand.reg 12 : Operand 64).read s3 =
      (Operand.mem (stackPtr s + 288) : Operand 64).read s := by
    have h := he3.writes.1
    simpa only [hs2, Operand.read, hm2] using h
  have hb3 : CodeIn (codeRange 0x1002ac [0x41, 0x5e]) s3 :=
    program_text_slice hc3 0x2ac 2 (by decide +kernel)
  have hp3 : PopPre 0x1002ac s3 := by
    refine ⟨he3.rip, ?_⟩
    rw [hs3]
    exact (hSlots 2 (by decide +kernel)).of_external_eq hm3
  obtain ⟨s4, ha4, hr4, he4⟩ :=
    (pop_r64_rex_effect_step 0x1002ac 0x41 0x5e
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr3 hb3 hp3 (digest_text_ne_return hOutside 0x2ae (by decide +kernel))
  change (popR64Effect 0x1002ac 2 14 s3).Holds s3 s4 at he4
  have hs4 : stackPtr s4 = stackPtr s + 304 := by
    have h := he4.writes.2
    change stackPtr s4 = stackPtr s3 + 8 at h
    rw [hs3, BitVec.add_assoc] at h
    exact h
  have hm4 : s4.external = s.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hc4 := he4.codeIn (popR64Effect_avoids _ _ _ _ _) hc3
  have hv14 : (Operand.reg 14 : Operand 64).read s4 =
      (Operand.mem (stackPtr s + 296) : Operand 64).read s := by
    have h := he4.writes.1
    simpa only [hs3, Operand.read, hm3] using h
  have hb4 : CodeIn (codeRange 0x1002ae [0x41, 0x5f]) s4 :=
    program_text_slice hc4 0x2ae 2 (by decide +kernel)
  have hp4 : PopPre 0x1002ae s4 := by
    refine ⟨he4.rip, ?_⟩
    rw [hs4]
    exact (hSlots 3 (by decide +kernel)).of_external_eq hm4
  obtain ⟨s5, ha5, hr5, he5⟩ :=
    (pop_r64_rex_effect_step 0x1002ae 0x41 0x5f
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr4 hb4 hp4 (digest_text_ne_return hOutside 0x2b0 (by decide +kernel))
  change (popR64Effect 0x1002ae 2 15 s4).Holds s4 s5 at he5
  have hs5 : stackPtr s5 = stackPtr s + 312 := by
    have h := he5.writes.2
    change stackPtr s5 = stackPtr s4 + 8 at h
    rw [hs4, BitVec.add_assoc] at h
    exact h
  have hm5 : s5.external = s.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hc5 := he5.codeIn (popR64Effect_avoids _ _ _ _ _) hc4
  have hv15 : (Operand.reg 15 : Operand 64).read s5 =
      (Operand.mem (stackPtr s + 304) : Operand 64).read s := by
    have h := he5.writes.1
    simpa only [hs4, Operand.read, hm4] using h
  have hb5 : CodeIn (codeRange 0x1002b0 [0xc3]) s5 :=
    program_text_slice hc5 0x2b0 1 (by decide +kernel)
  have ht : stackTop s5 = boundary.rip := by
    rw [hReturn]
    simp only [stackTop, hs5, Operand.read, hm5]
  have hp5 : RetPre 0x1002b0 s5 := by
    refine ⟨⟨he5.rip, ?_⟩, ?_⟩
    · rw [hs5]
      exact (hSlots 4 (by decide +kernel)).of_external_eq hm5
    · rw [ht]
      exact hLow
  obtain ⟨t, hstep, hr, he⟩ := ret_effect_step 0x1002b0 s5 hr5 hb5 hp5
  have hret : Returns boundary 1 s5 t := by
    apply Returns.of_step hstep (he.rip.trans ht)
    have h := he.writes
    change stackPtr t = stackPtr s5 + 8 at h
    rw [hs5, BitVec.add_assoc] at h
    exact h.trans hRsp.symm
  have hAll := ((((he1.agrees.trans he2.agrees).trans he3.agrees).trans
    he4.agrees).trans he5.agrees).trans he.agrees
  refine ⟨t, ha1.returns (ha2.returns (ha3.returns (ha4.returns (ha5.returns hret)))),
    hr, hAll.mono (by simp), ?_, ?_, ?_, ?_⟩
  · exact (((he3.agrees.trans he4.agrees).trans he5.agrees).trans he.agrees).read
      (n := 64) (r := 3) (by simp) |>.trans hv3
  · exact ((he4.agrees.trans he5.agrees).trans he.agrees).read
      (n := 64) (r := 12) (by simp) |>.trans hv12
  · exact (he5.agrees.trans he.agrees).read
      (n := 64) (r := 14) (by simp) |>.trans hv14
  · exact he.agrees.read (n := 64) (r := 15) (by simp) |>.trans hv15

section

variable [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {input : ByteArray}

omit bindings in
theorem digest_region_contains {region : MemoryRegion} (hb : region.Bounded) {i : Nat}
    (hi : i < region.size) :
    region.Contains (BitVec.ofNat 64 region.start + BitVec.ofNat 64 i).toNat := by
  unfold MemoryRegion.Bounded userAddressLimit at hb
  unfold MemoryRegion.Contains
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

omit bindings in
theorem digest_stack_bounds (hs : Stack.Valid initial Digest.minStackBytes) :
    656 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2 ^ 32 := by
  obtain ⟨hb, -, hu, -⟩ := hs
  change (stackPtr initial).toNat - 656 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 656)) < 2 ^ 32 at hb
  change 656 ≤ (stackPtr initial).toNat at hu
  omega

omit bindings in
theorem digest_stack_contains (hs : Stack.Valid initial Digest.minStackBytes) {a : Nat}
    (h1 : (stackPtr initial).toNat - 656 ≤ a) (h2 : a < (stackPtr initial).toNat + 8) :
    (Stack.region initial Digest.minStackBytes).Contains a := by
  have hB := digest_stack_bounds hs
  change (stackPtr initial).toNat - 656 ≤ a ∧ a < (stackPtr initial).toNat - 656 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 656))
  omega

theorem digest_output_contains (hCall : Digest.ValidCall bindings initial input) {i : Nat}
    (hi : i < 20) :
    (Digest.outputRegion initial).Contains (initial.regValue .rdx + BitVec.ofNat 64 i).toNat ∧
      (initial.regValue .rdx + BitVec.ofNat 64 i).toNat = (initial.regValue .rdx).toNat + i := by
  have hb : (initial.regValue .rdx).toNat + 20 < 2 ^ 32 := hCall.outputInMemory.2.1
  have he : (initial.regValue .rdx + BitVec.ofNat 64 i).toNat =
      (initial.regValue .rdx).toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, he⟩
  rw [he]
  change (initial.regValue .rdx).toNat ≤ _ ∧ _ < (initial.regValue .rdx).toNat + 20
  omega

theorem digest_output_not_stack (hCall : Digest.ValidCall bindings initial input) {i : Nat}
    (hi : i < 20) :
    ¬ (Stack.region initial Digest.minStackBytes).Contains
      (initial.regValue .rdx + BitVec.ofNat 64 i).toNat :=
  hCall.separation.1 _ (digest_output_contains hCall hi).1

set_option maxRecDepth 4096 in
theorem digest_finish (hCall : Digest.ValidCall bindings initial input)
    (hp : DigestPrepared initial boundary input s)
    (hq : Finalize.Post .digestCopy boundary input s t)
    (hBoundaryRsp : boundary.rsp = stackPtr initial + 8)
    (hLow : boundary.rip.toNat < userAddressLimit) :
    ∃ fuel final cs, Returns boundary fuel s final ∧ ReadyToStep final ∧
      CodeIn Sha1.Spec.Program.Extracted.programImage final ∧
      AgreesExcept cs initial final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final =
        .ok (SHA1.SHA1 (SHA2.bytesToBits input)).bytes ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      fixedPart final = fixedPart initial := by
  have hS := hCall.stackAvailable
  have hB := digest_stack_bounds hS
  have hsNat : (stackPtr s).toNat = (stackPtr initial).toNat - 312 := by
    rw [hp.stack]
    bv_omega
  have hAddr (k : Nat) (hk : k ≤ 320) :
      (stackPtr s + BitVec.ofNat 64 k).toNat = (stackPtr initial).toNat - 312 + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hsNat]
    omega
  have hRbx : (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx := hp.output
  have hRbxT : t.regValue .rbx = initial.regValue .rdx := by
    refine Eq.trans ?_ hRbx
    exact hq.agrees.read (n := 64) (r := 3)
      (by simp [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges])
  have hSlotKeep (j : Nat) (hj : j < 40) :
      ∀ c ∈ Finalize.Kind.changes .digestCopy s,
        ¬ c.Covers (stackPtr s + BitVec.ofNat 64 (280 + j)) := by
    intro c hc hcov
    simp only [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges,
      Finalize.Kind.stackBytes, List.map, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i, hi, heq⟩ := hcov
    have h := congrArg BitVec.toNat heq
    rw [hAddr _ (by omega)] at h
    have hl : (stackPtr s - Finalize.Kind.frameBytes + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - 656 + i := by
      have hframe := Finalize.Kind.frameBytes_eq
      have hlow : Finalize.Kind.frameBytes ≤ (stackPtr s).toNat := by omega
      have hsub : (stackPtr s - Finalize.Kind.frameBytes).toNat =
          (stackPtr s).toNat - Finalize.Kind.frameBytes := by
        rw [BitVec.toNat_sub_of_le]
        simp [hframe]
        exact hlow
      rw [BitVec.toNat_add, hsub, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hl] at h
    have hi' : i < Finalize.Kind.frameBytes + 280 := by omega
    have hj' : j < 40 := hj
    have hframe := Finalize.Kind.frameBytes_eq
    omega
  have hSlotOut (j : Nat) (hj : j < 40) :
      ∀ c ∈ outputChanges t, ¬ c.Covers (stackPtr s + BitVec.ofNat 64 (280 + j)) := by
    intro c hc hcov
    simp only [outputChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i, hi, heq⟩ := hcov
    rw [hRbxT] at heq
    apply digest_output_not_stack hCall hi
    rw [← heq, hAddr _ (by omega)]
    exact digest_stack_contains hS (by omega) (by omega)
  have hStackT : (⟨(stackPtr t).toNat, 20⟩ : MemoryRegion).HasBytes t.external
      ⟨(Hasher.stateBytes (SHA1.hashComputation
        (SHA2.SHA256.parse (SHA2.SHA256.pad (SHA2.bytesToBits input))))).toArray⟩ := by
    rw [hq.rsp]
    exact hq.digest
  have hStackLow : (stackPtr t).toNat + 20 ≤ 2 ^ 32 := by
    rw [hq.rsp, hsNat]
    omega
  have hst : Prelude.Stack.region initial Digest.minStackBytes =
      ⟨(stackPtr initial).toNat - 656, (stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 656)⟩ := rfl
  have hOut : Common.StoreRegion Extracted.programImage t.external
      ⟨(t.regValue .rbx).toNat, 20⟩ := by
    rw [hRbxT]
    refine ⟨hCall.outputInMemory.2.1, ?_, ?_⟩
    · intro a ha
      exact Option.isSome_iff_exists.mp ((hp.agrees.trans hq.agrees).grow a
        (Option.isSome_iff_exists.mpr (hCall.outputInMemory.2.2 a ha)))
    · exact (hCall.separation.2 (Digest.outputRegion initial) (by simp)).2
  obtain ⟨u, hOutRun, huReady, huCode, huRip, huAgrees, huBytes⟩ :=
    digest_output hq.ready hq.code hq.rip hp.boundaryOutside hStackT hStackLow hOut
  have huRsp : stackPtr u = stackPtr t :=
    huAgrees.read (n := 64) (r := 4) (by simp [outputChanges])
  have hSaved (k : Nat) (hl : 280 ≤ k) (hh : k + 8 ≤ 320) :
      (Operand.mem (stackPtr u + BitVec.ofNat 64 k) : Operand 64).read u =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 k) : Operand 64).read s := by
    rw [huRsp, hq.rsp]
    apply memLoad_congr
    intro i hi
    unfold memByte
    apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
    have he : stackPtr s + BitVec.ofNat 64 k + BitVec.ofNat 64 i =
        stackPtr s + BitVec.ofNat 64 (280 + (k - 280 + i)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [he]
    exact (huAgrees.byte (hSlotOut _ (by omega))).trans (hq.agrees.byte (hSlotKeep _ (by omega)))
  have hSlots : ∀ i < 5,
      MemReadable u (stackPtr u + BitVec.ofNat 64 (280 + 8 * i)) 8 := by
    intro i hi
    rw [huRsp, hq.rsp]
    refine ⟨?_, ?_⟩
    · rw [hAddr _ (by omega)]
      omega
    · intro j hj
      apply ((hp.agrees.trans hq.agrees).trans huAgrees).grow
      apply Option.isSome_iff_exists.mpr
      apply hS.2.1
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hAddr _ (by omega)]
      exact digest_stack_contains hS (by omega) (by omega)
  have hRet : boundary.rip = (Operand.mem (stackPtr u + 312) : Operand 64).read u :=
    ((hSaved 312 (by decide) (by decide)).trans hp.returnSlot).symm
  have hRsp : boundary.rsp = stackPtr u + 320 := by
    rw [huRsp, hq.rsp, hp.stack, hBoundaryRsp]
    bv_omega
  obtain ⟨final, hReturn, hfReady, hfAgrees, hfRbx, hfR12, hfR14, hfR15⟩ :=
    digest_epilogue huReady huCode huRip hSlots hRet hRsp hLow hp.boundaryOutside
  have hFinalMemory : final.external = u.external :=
    hfAgrees.external (by simp [Component.Covers])
  have hAll := ((hp.agrees.trans hq.agrees).trans huAgrees).trans hfAgrees
  have hNot : ∀ r : BitVec 5, r ∈ [5, 13] →
      Component.reg r ∉ digestPreparationChanges initial ++
        Finalize.Kind.changes .digestCopy s ++ outputChanges t ++
        [.reg 3, .reg 4, .reg 12, .reg 14, .reg 15, .flags, .rip] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp [digestPreparationChanges, Finalize.Kind.changes, Finalize.Kind.workRegisters,
        Finalize.Kind.localChanges, outputChanges]
  have hRegion : (⟨(t.regValue .rbx).toNat, 20⟩ : MemoryRegion) = Digest.outputRegion initial := by
    rw [hRbxT]
    rfl
  obtain ⟨n, hFinalize⟩ := hq.advances
  refine ⟨n + (15 + 6), final, _, hFinalize.returns (hOutRun.returns hReturn), hfReady,
    hfAgrees.codeIn (by simp [Component.Covers]) huCode, hAll, ?_, ?_, ?_,
    hAll.directionFlagClear (by
      simp [digestPreparationChanges, Finalize.Kind.changes, Finalize.Kind.workRegisters,
        Finalize.Kind.localChanges, outputChanges]) hCall.directionFlagUnset, hAll.rest⟩
  · apply hAll.memoryWriteFrame
    intro c hc x hx
    cases c with
    | mem a len =>
      simp only [digestPreparationChanges, Finalize.Kind.changes, Finalize.Kind.workRegisters,
        Finalize.Kind.localChanges, Finalize.Kind.stackBytes, outputChanges,
        List.map, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, false_or, Component.mem.injEq] at hc
      obtain ⟨i, hi, rfl⟩ := hx
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, by simp, digest_region_contains hS.1 hi⟩
      · refine ⟨Stack.region initial Digest.minStackBytes, by simp, ?_⟩
        have hl : (stackPtr s - Finalize.Kind.frameBytes + BitVec.ofNat 64 i).toNat =
            (stackPtr initial).toNat - 656 + i := by
          have hframe := Finalize.Kind.frameBytes_eq
          have hlow : Finalize.Kind.frameBytes ≤ (stackPtr s).toNat := by omega
          have hsub : (stackPtr s - Finalize.Kind.frameBytes).toNat =
              (stackPtr s).toNat - Finalize.Kind.frameBytes := by
            rw [BitVec.toNat_sub_of_le]
            simp [hframe]
            exact hlow
          rw [BitVec.toNat_add, hsub, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hl]
        have hB' := digest_stack_bounds hS
        have hframe := Finalize.Kind.frameBytes_eq
        apply digest_stack_contains hS
        · omega
        · have hB'' := digest_stack_bounds hS
          omega
      · refine ⟨Digest.outputRegion initial, by simp, ?_⟩
        rw [hRbxT]
        exact (digest_output_contains hCall hi).1
    | _ => exact absurd hx (by simp [Component.Covers])
  · unfold Digest.readOutput
    have hd := huBytes
    rw [stateBytes_bswap_eq_toDigest, hRegion, ← hFinalMemory] at hd
    exact Common.readBytes_of_hasBytes (initial := initial) hd
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfRbx.trans ((hSaved 280 (by decide) (by decide)).trans hp.savedRbx)
    · exact hAll.read (n := 64) (r := 5) (hNot 5 (by simp))
    · exact hfR12.trans ((hSaved 288 (by decide) (by decide)).trans hp.savedR12)
    · exact hAll.read (n := 64) (r := 13) (hNot 13 (by simp))
    · exact hfR14.trans ((hSaved 296 (by decide) (by decide)).trans hp.savedR14)
    · exact hfR15.trans ((hSaved 304 (by decide) (by decide)).trans hp.savedR15)

end

end Sha1.Proofs.Buffered
