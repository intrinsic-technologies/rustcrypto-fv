import Sha1.Proofs.Buffered.DigestPrepare.Long.Compression.Interface
import Sha1.Proofs.Buffered.DigestPrepare.Long.Compression.Frame
import Sha1.Proofs.Buffered.DigestPrepare.Long.Preservation
import Sha1.Proofs.Buffered.DigestPrepare.Position
import Sha1.Proofs.Compress.Routine.Public

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Common.Instructions
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem compress [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hBridge : CompressionCall) (hStride : UnitStringStride bindings)
    (hCall : Digest.ValidCall bindings initial input) (h : Prepared initial input s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Compressed initial input t := by
  have hs := hCall.stackAvailable
  have hst := h.toFrame.storage hCall
  have hb := stack_bounds hs
  have hn := h.toFrame.stackNat hs
  have hw := h.toFrame.scratchWritable hCall (AgreesExcept.refl [] s) 8 8 (by decide) (by decide)
  have hpre : StorePre.PushPre 0x1000b9 5 s :=
    ⟨h.rip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩,
      rangeApart_text hw.code (by decide +kernel : 0xb9 + 5 ≤ Extracted.textBytes.size)⟩
  have hbytes : CodeIn (codeRange 0x1000b9 (encodeCallRel32 0x2422)) s :=
    Sha1.Proofs.Compress.Machine.program_text_slice h.code 0xb9 5 (by decide +kernel)
  have hstep := MovStore.call_rel32_effect_step 0x1000b9 0x2422 (by decide +kernel)
  obtain ⟨u, hcall, hu, he⟩ := hstep.advances h.ready hbytes hpre
    (text_address_ne_return h.boundaryOutside 0x24e0 (by decide +kernel))
  have hcu := callEffect_code he h.code hw.code
  have hret := callEffect_returnBoundary he
  have husp : stackPtr u = stackPtr s - 8 := callEffect_rsp he
  have hlow := hst.stackLow
  have hfb : Finalize.Kind.frameBytes = 344 := rfl
  have hhigh : (stackPtr s).toNat + 0x118 < 2^32 := hst.stackHigh
  have hin : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  have hin0 : (initial.regValue .rdi).toNat ≠ 0 := hCall.inputInMemory.1
  have husn : (stackPtr u).toNat = (stackPtr s).toNat - 8 := by
    rw [husp, BitVec.toNat_sub_of_le]
    · rfl
    · change 8 ≤ (stackPtr s).toNat
      omega
  have hunchanged (x : BitVec 64)
      (hx : x.toNat < (stackPtr s).toNat - 8 ∨ (stackPtr s).toNat ≤ x.toNat) :
      u.external[x]? = s.external[x]? := by
    apply he.agrees.byte
    intro c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨j, hj, rfl⟩ := hcov
      have hp : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
        rw [pushAddr, BitVec.toNat_sub_of_le]
        · rfl
        · change 8 ≤ (stackPtr s).toNat
          omega
      rw [toNat_add_ofNat _ _ (by rw [hp]; omega), hp] at hx
      omega
    · exact hcov
  have hdi : u.regValue .rdi = stackPtr s + 0x100 :=
    (callEffect_read he (r := 7) (by decide)).trans h.statePointerArg
  have hsi : u.regValue .rsi = initial.regValue .rdi :=
    (callEffect_read he (r := 6) (by decide)).trans h.inputPointer
  have hdx : u.regValue .rdx = BitVec.ofNat 64 (input.size / 64) :=
    (callEffect_read he (r := 2) (by decide)).trans h.blockCount
  have hdin : (u.regValue .rdi).toNat = (stackPtr s).toNat + 0x100 := by
    rw [hdi]
    exact h.toFrame.address hs (by decide)
  have hrsp : (u.regValue .rsp).toNat = (stackPtr s).toNat - 8 := husn
  have hinStack (address : Nat)
      (ha : (stackPtr s).toNat - 344 ≤ address ∧ address < (stackPtr s).toNat + 280) :
      (Stack.region initial Digest.minStackBytes).Contains address :=
    stack_region_contains hs (by omega) (by omega)
  have hsep := hCall.separation.2 (Stack.region initial Digest.minStackBytes) (by simp)
  have hinputDisjoint := hsep.1 (Digest.inputRegion initial input) (by simp)
  have hfull : (fullBytes input).size = 64 * (input.size / 64) := size_fullBytes input
  have hData : Sha1.Proofs.Compress.Routine.CallData
      ⟨u, Standards.NIST.SHA1.initialHashValue, fullBytes input⟩ := by
    refine ⟨he.agrees.directionFlagClear (by simp [pushEffect_components]) h.df,
      fun a b hm ↦ (hcu (a, b) hm).2, ?_, ?_, ?_, ?_, ?_⟩
    · change 64 * (u.regValue .rdx).toNat = (fullBytes input).size
      rw [hdx, hfull, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · change (⟨(u.regValue .rsi).toNat, (fullBytes input).size⟩ : MemoryRegion).start ≠ 0 ∧
        (⟨(u.regValue .rsi).toNat, (fullBytes input).size⟩ : MemoryRegion).Bounded ∧
        (⟨(u.regValue .rsi).toNat, (fullBytes input).size⟩ : MemoryRegion).HasBytes
          u.external (fullBytes input)
      rw [hsi]
      refine ⟨hin0, by show (initial.regValue .rdi).toNat + (fullBytes input).size < 2^32; omega,
        ?_⟩
      have hx : (⟨(initial.regValue .rdi).toNat, (fullBytes input).size⟩ : MemoryRegion).HasBytes
          s.external (fullBytes input) := by
        simpa only [fullBytes, Wrapper.Absorb.fullBlocks, Nat.add_zero, Digest.inputRegion,
          registerRegion] using
          hasBytes_extract (h.toFrame.inputBytes hCall) 0 (64 * (input.size / 64))
      refine ⟨hx.1, fun i ↦ ?_⟩
      have hi := i.isLt
      rw [← hx.2 i]
      apply hunchanged
      have hd := hinputDisjoint ((initial.regValue .rdi).toNat + i.val)
        ⟨by simp [Digest.inputRegion, registerRegion],
          by simp only [Digest.inputRegion, registerRegion]; omega⟩
      change (BitVec.ofNat 64 ((initial.regValue .rdi).toNat + i.val)).toNat < _ ∨ _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rcases Nat.lt_or_ge ((initial.regValue .rdi).toNat + i.val) ((stackPtr s).toNat - 8)
        with h1 | h1
      · exact Or.inl h1
      rcases Nat.lt_or_ge ((initial.regValue .rdi).toNat + i.val) (stackPtr s).toNat with h2 | h2
      · exact absurd (hinStack _ ⟨by omega, by omega⟩) hd
      · exact Or.inr h2
    · change (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion).start ≠ 0 ∧
        (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion).Bounded ∧
        (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion).HasBytes u.external
          (Wrapper.Hash.Serialize.stateBytes Standards.NIST.SHA1.initialHashValue)
      rw [hdin]
      refine ⟨by change _ + _ ≠ 0; omega, by change _ + _ + 20 < 2^32; omega,
        h.hash.1, fun i ↦ ?_⟩
      rw [← h.hash.2 i]
      have hi : i.val < 20 := by
        have := i.isLt
        simpa only [Wrapper.Hash.Serialize.stateBytes_size] using this
      apply hunchanged
      change (BitVec.ofNat 64 ((stackPtr s).toNat + 0x100 + i.val)).toNat < _ ∨
        _ ≤ (BitVec.ofNat 64 ((stackPtr s).toNat + 0x100 + i.val)).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change (u.regValue .rsp).toNat - 336 +
          ((u.regValue .rsp).toNat + 8 - ((u.regValue .rsp).toNat - 336)) < 2^32
        omega
      · intro address ha
        change (u.regValue .rsp).toNat - 336 ≤ address.toNat ∧
          address.toNat < (u.regValue .rsp).toNat - 336 +
            ((u.regValue .rsp).toNat + 8 - ((u.regValue .rsp).toNat - 336)) at ha
        apply Option.isSome_iff_exists.mp
        apply he.agrees.grow
        apply h.agrees.grow
        exact Option.isSome_iff_exists.mpr (hs.2.1 address (hinStack _ (by omega)))
      · change 336 ≤ (u.regValue .rsp).toNat
        omega
      · change (u.regValue .rsp).toNat % 16 = 8
        have := hst.stackAligned
        omega
    · refine ⟨?_, ?_⟩
      · intro address ho hk
        change (u.regValue .rdi).toNat ≤ address ∧ address < (u.regValue .rdi).toNat + 20 at ho
        change (u.regValue .rsp).toNat - 336 ≤ address ∧ address < (u.regValue .rsp).toNat - 336 +
          ((u.regValue .rsp).toNat + 8 - ((u.regValue .rsp).toNat - 336)) at hk
        omega
      · intro region hr
        simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        have hsub : ∀ address, region.Contains address →
            (stackPtr s).toNat - 344 ≤ address ∧ address < (stackPtr s).toNat + 280 := by
          rcases hr with rfl | rfl
          · intro address ha
            change (u.regValue .rdi).toNat ≤ address ∧
              address < (u.regValue .rdi).toNat + 20 at ha
            omega
          · intro address ha
            change (u.regValue .rsp).toNat - 336 ≤ address ∧
              address < (u.regValue .rsp).toNat - 336 +
                ((u.regValue .rsp).toNat + 8 - ((u.regValue .rsp).toNat - 336)) at ha
            omega
        refine ⟨?_, fun address ha ↦ hsep.2 address (hinStack _ (hsub _ ha))⟩
        intro read hread address hra hrb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
        subst hread
        change (u.regValue .rsi).toNat ≤ address ∧
          address < (u.regValue .rsi).toNat + (fullBytes input).size at hra
        rw [hsi] at hra
        apply hinputDisjoint address
        · change (initial.regValue .rdi).toNat ≤ address ∧
            address < (initial.regValue .rdi).toNat + input.size
          omega
        · exact hinStack _ (hsub _ hrb)
  have hentry : u.RIP = 0x1024e0 := he.rip.trans (by rfl)
  obtain ⟨m, t, hadv, ht, hct, htrip, htsp, hag, hsaved, hout⟩ := hBridge
    (returnBoundary initial) hStride hu hcu hentry hData
    (by rw [hret]; show (0x1000b9 + 5 : BitVec 64).toNat < userAddressLimit; decide)
    (by rw [hret]; left; show (0x1000b9 + 5 : BitVec 64).toNat < 0x1024e0; decide)
    (Sha1.Proofs.Compress.Routine.outsideCompression_of_notInProgram h.boundaryOutside)
    (by rw [hret]; exact (text_address_ne_return h.boundaryOutside 0xbe (by decide +kernel)).symm)
  rw [hret] at htrip htsp
  have hsubset (c : Component)
      (hc : c ∈ Sha1.Proofs.Compress.Routine.compressionChanges
        ⟨u, Standards.NIST.SHA1.initialHashValue, fullBytes input⟩) :
      c ∈ compressionChanges u := by
    simpa [Sha1.Proofs.Compress.Routine.compressionChanges, compressionChanges,
      Sha1.Proofs.Compress.Routine.Context.stack,
      Sha1.Proofs.Compress.Routine.Context.sp,
      Sha1.Proofs.Compress.Routine.frameComponents,
      Sha1.Proofs.Compress.Machine.scratchComponents] using hc
  have hag' : AgreesExcept (compressionChanges u) u t := by
    apply hag.widen
    · intro c hc hm
      exact hsubset c hc
    · intro x c hc hcov
      exact ⟨c, hsubset c hc, hcov⟩
  have hall : AgreesExcept ([.reg 4, .mem (pushAddr s) 8, .rip] ++ compressionChanges u) s t :=
    (he.agrees.mono (by intro c hc; simpa [pushEffect_components] using hc)).trans hag'
  have hcover (c : Component) (hc : c ∈ [.reg 4, .mem (pushAddr s) 8, .rip] ++
      compressionChanges u) (address : BitVec 64) (hcov : c.Covers address) :
      ((stackPtr s).toNat - 344 ≤ address.toNat ∧ address.toNat < (stackPtr s).toNat) ∨
      ((stackPtr s).toNat + 0x100 ≤ address.toNat ∧
        address.toNat < (stackPtr s).toNat + 0x114) := by
    simp only [compressionChanges, Sha1.Proofs.Compress.Routine.frameComponents,
      Sha1.Proofs.Compress.Machine.scratchComponents, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    repeat' rcases hc with rfl | hc
    have hp : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
      rw [pushAddr, BitVec.toNat_sub_of_le]
      · rfl
      · change 8 ≤ (stackPtr s).toNat
        omega
    all_goals try exact hcov.elim
    all_goals obtain ⟨j, hj, rfl⟩ := hcov
    all_goals first
      | (rw [toNat_add_ofNat _ _ (by rw [hp]; omega), hp]; omega)
      | (have hreg : (Stack.region u Compress.minStackBytes).start =
            (stackPtr u).toNat - 336 := by
           change (stackPtr u).toNat - 336 = (stackPtr u).toNat - 336
         have hregSize : (Stack.region u Compress.minStackBytes).size = 344 := by
           change 336 + 8 = 344
           decide
         have hj' : j < 344 := by rw [hregSize] at hj; exact hj
         rw [hreg, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega)]
         rw [husp, pushAddr]
         omega)
      | (change j < (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336) at hj
         have hk : (BitVec.ofNat 64 (Stack.region u Compress.minStackBytes).start +
             BitVec.ofNat 64 j).toNat = (stackPtr u).toNat - 336 + j := by
           change (BitVec.ofNat 64 ((stackPtr u).toNat - 336) + BitVec.ofNat 64 j).toNat = _
           rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
         rw [hk]
         omega)
      | (simp at hj ⊢
         rw [husp, pushAddr] at *
         omega)
      | (rw [hdi]; bv_omega)
      | (rw [husp]; simp only [pushAddr] at *; bv_omega)
  have hsv3 : (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s :=
    (hsaved .rbx (by decide)).trans (callEffect_read he (r := 3) (by decide))
  have hsv14 : (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s :=
    (hsaved .r14 (by decide)).trans (callEffect_read he (r := 14) (by decide))
  have hsv12 : (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
    (hsaved .r12 (by decide)).trans (callEffect_read he (r := 12) (by decide))
  have hsv15 : (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s :=
    (hsaved .r15 (by decide)).trans (callEffect_read he (r := 15) (by decide))
  have hsv5 : (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s :=
    (hsaved .rbp (by decide)).trans (callEffect_read he (r := 5) (by decide))
  have hsv13 : (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s :=
    (hsaved .r13 (by decide)).trans (callEffect_read he (r := 13) (by decide))
  have htf : Frame initial (returnBoundary initial) t := by
    apply Frame.preserve_wide h.toFrame hs hall ht hct
    · intro c hc hm
      simp only [compressionChanges, Sha1.Proofs.Compress.Routine.frameComponents,
        Sha1.Proofs.Compress.Machine.scratchComponents, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      repeat' rcases hc with rfl | hc
      all_goals first
        | (simp [Component.isMem] at hm; done)
        | exact Or.inr (by
            change t.GPR[gprIndex 5] = s.GPR[gprIndex 5]
            simpa [Operand.read] using hsv5)
        | exact Or.inr (by
            change t.GPR[gprIndex 13] = s.GPR[gprIndex 13]
            simpa [Operand.read] using hsv13)
        | exact Or.inl (by simp [digestPreparationChanges])
    · intro c hc address hcov
      have := hcover c hc address hcov
      omega
    · exact htsp
    · exact hsv3
    · exact hsv14
  refine ⟨1 + m, t, hcall.trans hadv, ⟨⟨htf, ?_, ?_, ?_, ?_⟩, htrip⟩⟩
  · rw [htsp]
    have ho : Compress.outputRegion u = ⟨(stackPtr s).toNat + 0x100, 20⟩ := by
      change (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion) = _
      rw [hdin]
    rw [ho] at hout
    exact hout
  · rw [htsp]
    apply Eq.trans _ h.blocks
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    apply hall.byte
    intro c hc hcov
    have hx := hcover c hc _ hcov
    have hn : (stackPtr s + 0xf8 + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat + 0xf8 + i := by
      change (stackPtr s + BitVec.ofNat 64 0xf8 + BitVec.ofNat 64 i).toNat = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address hs (by omega)]
      omega
    rw [hn] at hx
    omega
  · exact hsv12.trans h.tailPointer
  · exact hsv15.trans h.tailSize

end Sha1.Proofs.Buffered.DigestPrepare.Long
