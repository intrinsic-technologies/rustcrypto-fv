import Sha1.Proofs.Buffered.Update.Slices.Full.Contracts
import Sha1.Proofs.Buffered.Update.Slices.Full.Tail.Steps
import Sha1.Proofs.Buffered.Update.Slices.Frame
import Sha1.Proofs.Buffered.DigestPrepare.Long.Preparation.Arithmetic

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (program_text_slice)
open Sha1.Proofs.Buffered.DigestPrepare.Long (fullBlockMask_toNat tailMask_toNat)
open Sha1.Proofs.Wrapper.Absorb (remainderBytes)

private theorem tailBytes_extract {message input : ByteArray} {offset : Nat}
    (halign : (message.size + offset) % 64 = 0) (hoff : offset ≤ input.size) :
    tailBytes (message ++ input) =
      input.extract (offset + (input.size - offset) / 64 * 64) input.size := by
  unfold tailBytes remainderBytes
  rw [ByteArray.size_append, show 64 * ((message.size + input.size) / 64) =
    message.size + (offset + (input.size - offset) / 64 * 64) by omega,
    ByteArray.extract_append_size_add]

private theorem context_position (s : RamState) :
    stackPtr s + 279 = UpdateKind.updateFinalize.context s + 63 := by
  change stackPtr s + 279 = stackPtr s + 216 + 63
  rw [BitVec.add_assoc]
  rfl

private theorem copy_preserves_context [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s q v : RamState} {len : Nat} (h : UpdatePre .updateFinalize boundary message input s)
    (copy : MemcpySiteResult boundary 0x101daf q v)
    (hsp : stackPtr q = stackPtr s)
    (hdi : rdi.read q = UpdateKind.updateFinalize.context s)
    (hlen : (MemoryRoutines.rdx.read q).toNat = len)
    {i : Nat} (hi : len ≤ i) (hi' : i < 92) :
    v.external[UpdateKind.updateFinalize.context s + BitVec.ofNat 64 i]? =
      q.external[UpdateKind.updateFinalize.context s + BitVec.ofNat 64 i]? := by
  have hlo := h.stackLow
  have hhi : (stackPtr s).toNat + 216 + 92 < 2^32 := h.stackHigh
  have hctx : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 216 :=
    toNat_add_ofNat _ 216 (by omega)
  have hslot : (pushAddr q).toNat = (stackPtr s).toNat - 8 := by
    rw [pushAddr, hsp, BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr s).toNat; omega)]
    rfl
  apply copy.agrees.byte
  intro c hc hx
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hx.elim
  all_goals obtain ⟨j, hj, he⟩ := hx
  · rw [hdi] at he
    rw [hlen] at hj
    have he := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at he
    omega
  · have he := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at he
    omega

private theorem context_read {s t : RamState} {base : BitVec 64}
    {off n : Nat}
    (h : ∀ i < n / 8, t.external[base + BitVec.ofNat 64 (off + i)]? =
      s.external[base + BitVec.ofNat 64 (off + i)]?) :
    (Operand.mem (base + BitVec.ofNat 64 off) : Operand n).read t =
      (Operand.mem (base + BitVec.ofNat 64 off) : Operand n).read s := by
  change memLoad t.external _ n = memLoad s.external _ n
  apply memLoad_congr
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun b : Option UInt8 ↦ b.getD 0) (h i hi)

set_option maxRecDepth 2048 in
theorem tail [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset : Nat} (h : UpdatePre .updateFinalize boundary message input s)
    (b : TailReady boundary message input s offset u) :
    ∃ v, UpdatePost .updateFinalize boundary message input s v := by
  let rem := input.size - offset
  let len := rem % 64
  let src := offset + rem / 64 * 64
  let ctx := UpdateKind.updateFinalize.context s
  have hOffset := b.offsetBound
  have hInput : ((Operand.reg 14 : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
  have hHigh : (stackPtr s).toNat + 216 + 92 < 2^32 := h.stackHigh
  have hCtx : ctx.toNat = (stackPtr s).toNat + 216 := toNat_add_ofNat _ 216 (by omega)
  have hSum : src + len = input.size := by dsimp [src, len, rem]; omega
  have hLen : len < 64 := Nat.mod_lt _ (by decide)
  have hTail : tailBytes (message ++ input) = input.extract src input.size :=
    tailBytes_extract b.aligned b.offsetBound
  have hTailSize : (tailBytes (message ++ input)).size = len := by
    rw [hTail, ByteArray.size_extract, Nat.min_self]
    omega
  have hBytes : CodeIn (codeRange 0x101d7d tailArithmeticBytes) u :=
    program_text_slice b.code 0x1d7d 22 (by decide +kernel)
  obtain ⟨na, a, hRunA, hReadyA, _, hA⟩ :=
    tail_arithmetic boundary h.boundaryOutside u b.ready hBytes b.rip
  have hCodeA := hA.agrees.codeIn
    (by simp [tailArithmeticEffect, Effect.components, Component.Covers]) b.code
  have hspA : stackPtr a = stackPtr s := (hA.agrees.read (n := 64) (r := 4)
    (by simp [tailArithmeticEffect, Effect.components])).trans
      (b.agrees.read (by simp [UpdateKind.changes, UpdateKind.workRegisters]))
  have hRemain : ((Operand.reg 5 : Operand 64).read u).toNat = rem := by
    rw [b.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [rem]; omega)]
  have hFullMask :
      (Operand.reg 5 : Operand 64).read u &&& 0x7fffffffffffffc0 =
        BitVec.ofNat 64 (rem / 64 * 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [fullBlockMask_toNat _ (by rw [hRemain]; dsimp [rem]; omega), hRemain,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hLenReg : (Operand.reg 5 : Operand 64).read a = BitVec.ofNat 64 len := by
    rw [hA.writes.2.2.1]
    change (((Operand.reg 5 : Operand 64).read u).setWidth 32 &&& 63).setWidth 64 = _
    apply BitVec.eq_of_toNat_eq
    rw [tailMask_toNat, hRemain, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := len) (by omega)]
  have hSrcReg : (Operand.reg 14 : Operand 64).read a =
      (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 src := by
    rw [hA.writes.2.2.2, hFullMask, b.pointer, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hPosAddr : stackPtr a + 279 = ctx + 63 := by rw [hspA]; exact context_position s
  have hPosNat : (stackPtr a + 279).toNat = (stackPtr s).toNat + 279 := by
    rw [hspA]
    exact toNat_add_ofNat _ 279 (by omega)
  have hWritable : MemoryRoutines.WritableRange a (stackPtr a + 279) 1 := by
    refine DigestPrepare.writableRange_of_region ?_
      (allocated_of_agrees (b.agrees.trans hA.agrees) h.contextAllocated) h.contextAvoids ?_ ?_
    · change ctx.toNat + 92 < 2^32
      omega
    · change ctx.toNat ≤ _
      omega
    · change _ ≤ ctx.toNat + 92
      omega
  obtain ⟨p, hRunP, hReadyP, hCodeP, hP⟩ :=
    tail_position h.boundaryOutside hReadyA hCodeA hA.rip hWritable
  have hArgBytes : CodeIn (codeRange 0x101d9b tailArgumentsBytes) p :=
    program_text_slice hCodeP 0x1d9b 14 (by decide +kernel)
  obtain ⟨nq, q, hRunQ, hReadyQ, _, hQ⟩ :=
    tail_arguments boundary h.boundaryOutside p hReadyP hArgBytes hP.rip
  have hCodeQ := hQ.agrees.codeIn
    (by simp [tailArgumentsEffect, Effect.components, Component.Covers]) hCodeP
  have hspP : stackPtr p = stackPtr a :=
    hP.agrees.read (n := 64) (r := 4) (by simp [tailPositionEffect, storeEffect_components])
  have hspQ : stackPtr q = stackPtr s :=
    (hQ.agrees.read (n := 64) (r := 4) (by simp [tailArgumentsEffect, Effect.components])).trans
      (hspP.trans hspA)
  have hDest : rdi.read q = ctx := by
    rw [hQ.writes.1, hspP, hspA]
    rfl
  have hSrc : rsi.read q = (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 src :=
    hQ.writes.2.1.trans ((hP.agrees.read (by simp [tailPositionEffect, storeEffect_components])).trans hSrcReg)
  have hLength : MemoryRoutines.rdx.read q = BitVec.ofNat 64 len :=
    hQ.writes.2.2.trans ((hP.agrees.read (by simp [tailPositionEffect, storeEffect_components])).trans hLenReg)
  have hLengthNat : (MemoryRoutines.rdx.read q).toNat = len := by
    rw [hLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hSetup := (hA.agrees.trans hP.agrees).trans hQ.agrees
  have hComponentsA : (tailArithmeticEffect u).components =
      [.reg 1, .reg 0, .reg 5, .reg 14, .flags, .rip] := rfl
  have hComponentsP : (tailPositionEffect a).components =
      [.mem (stackPtr a + 279) 1, .rip] := by
    simp only [tailPositionEffect, storeEffect_components]
  have hComponentsQ : (tailArgumentsEffect p).components = [.reg 7, .reg 6, .reg 2, .rip] := rfl
  rw [hComponentsA, hComponentsP, hComponentsQ, hPosAddr] at hSetup
  have hSetupWide : AgreesExcept (UpdateKind.updateFinalize.changes s) u q := by
    apply hSetup.widen
    · intro c hc hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl) | rfl | rfl | rfl | rfl
      all_goals first | contradiction | simp [UpdateKind.changes, UpdateKind.workRegisters]
    · intro x c hc hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl) | rfl | rfl | rfl | rfl
      all_goals try exact hx.elim
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨.mem ctx 92, by simp [ctx, UpdateKind.changes], 63 + i, by omega, ?_⟩
      rw [BitVec.add_assoc, BitVec.ofNat_add]
      rfl
  have hBefore : AgreesExcept (UpdateKind.updateFinalize.changes s) s q := (b.agrees.trans hSetupWide).mono (by simp)
  have hRipQ : q.RIP = 0x101da9 := hQ.rip
  obtain ⟨v, hCopy⟩ := copy_input h hBefore hspQ hReadyQ hCodeQ
    (hBefore.directionFlagClear (by simp [UpdateKind.changes, UpdateKind.workRegisters]) ⟨h.df⟩).df
    hRipQ (.inr (.inr rfl)) (dst := 0) hSrc
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hDest) hLength
    (by omega) (by omega)
  have hCopyWide := copy_agrees (dst := 0) h hCopy hspQ
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hDest) hLength (by omega)
  have hInputQ := inputBytes_of_agrees h hBefore
  have hTailQ := hasBytes_extract hInputQ src input.size
  have hSrcNat : (rsi.read q).toNat = (UpdateKind.updateFinalize.inputRegion s input).start + src := by
    rw [hSrc, toNat_add_ofNat _ _ (by omega)]
    rfl
  rw [← hSrcNat, ← hTail] at hTailQ
  have hTailV := hasBytes_of_copy (dst := rdi.read q) (fun i hi ↦ hCopy.copy i
    (by rwa [hLengthNat, ← hTailSize])) hTailQ
  rw [hDest] at hTailV
  have hKeepSetup {i : Nat} (hi : i ≠ 63) (hi' : i < 92) :
      q.external[ctx + BitVec.ofNat 64 i]? = u.external[ctx + BitVec.ofNat 64 i]? := by
    apply hSetup.byte
    intro c hc hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl) | rfl | rfl | rfl | rfl
    all_goals try exact hx.elim
    obtain ⟨j, hj, he⟩ := hx
    have hji : j = 0 := by omega
    subst j
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at he
    have he := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by omega)] at he
    change ctx.toNat + i = (ctx + BitVec.ofNat 64 63).toNat at he
    rw [toNat_add_ofNat _ _ (by omega)] at he
    omega
  have hKeepCopy {i : Nat} (hi : len ≤ i) (hi' : i < 92) :
      v.external[ctx + BitVec.ofNat 64 i]? = q.external[ctx + BitVec.ofNat 64 i]? :=
    copy_preserves_context h hCopy hspQ hDest hLengthNat hi hi'
  have hKeep {i : Nat} (hi : len ≤ i) (hi' : i < 92) (hne : i ≠ 63) :
      v.external[ctx + BitVec.ofNat 64 i]? = u.external[ctx + BitVec.ofNat 64 i]? :=
    (hKeepCopy hi hi').trans (hKeepSetup hne hi')
  have hPositionQ : (Operand.mem (ctx + 63) : Operand 8).read q = BitVec.ofNat 8 len := by
    have hmem := hQ.agrees.external (by simp [tailArgumentsEffect, Effect.components, Component.Covers])
    change memLoad q.external (ctx + 63) 8 = _
    rw [hmem, ← hPosAddr]
    apply hP.writes.trans
    change ((Operand.reg 5 : Operand 64).read a).setWidth 8 = _
    rw [hLenReg, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
  have hPositionV := context_read (base := ctx) (off := 63) (n := 8)
    (fun i hi ↦ hKeepCopy (by omega) (by omega))
  have hCounterV := context_read (base := ctx) (off := 64) (n := 64)
    (fun i hi ↦ hKeep (by omega) (by omega) (by omega))
  have hStateV : (⟨(ctx + 72).toNat, 20⟩ : MemoryRegion).HasBytes
      v.external (absorbedStateBytes (message ++ input)) := by
    have hstate := b.state
    rw [← absorbedStateBytes_size (message ++ input)] at hstate ⊢
    apply hasBytes_of_copy _ hstate
    intro i hi
    rw [absorbedStateBytes_size] at hi
    rw [BitVec.add_assoc]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      hKeep (i := 72 + i) (by omega) (by omega) (by omega)
  obtain ⟨nb, hRunB⟩ := b.advances
  obtain ⟨nv, hRunV⟩ := hCopy.advances
  refine ⟨v, ⟨⟨nb + na + 1 + nq + nv, (((hRunB.trans hRunA).trans hRunP).trans hRunQ).trans hRunV⟩,
    hCopy.ready, hCopy.code, by simp [hCopy.rip, UpdateKind.exits],
    ⟨hStateV, hTailV, ?_, hCounterV.trans b.counter⟩, (hBefore.trans hCopyWide).mono (by simp)⟩⟩
  rw [hTailSize]
  exact hPositionV.trans hPositionQ

end Sha1.Proofs.Buffered.Update.Slices.Full
