import Sha1.Proofs.Buffered.Update.Slices.Copy
import Sha1.Proofs.Compress.Blocks
import Sha1.Proofs.Compress.Routine.Main
import Sha1.Proofs.Compress.Routine.Public
import Sha1.Proofs.Common.Instructions.MovStore.Stack

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def compressChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (UpdateKind.updateFinalize.context s + 72) 20,
    .mem (BitVec.ofNat 64 ((stackPtr s).toNat - 344)) 344]

structure Compressed [Bindings] (boundary : ReturnBoundary) (ret : BitVec 64)
    (s v : RamState) (hash : Vector (BitVec 32) 5) (blocks : ByteArray) (t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel v t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = ret
  agrees : AgreesExcept (compressChanges s) v t
  state : (⟨(UpdateKind.updateFinalize.context s + 72).toNat, 20⟩ : MemoryRegion).HasBytes
    t.external (Wrapper.Hash.Serialize.stateBytes (Wrapper.Absorb.compressBlocks hash blocks))

set_option maxRecDepth 4096 in
theorem compress [bindings : Bindings] {boundary : ReturnBoundary} {p : BitVec 64} {s v : RamState}
    {message input blocks : ByteArray} {hash : Vector (BitVec 32) 5} {changes : List Component}
    (h : UpdatePre .updateFinalize boundary message input s)
    (ha : AgreesExcept changes s v) (hsp : stackPtr v = stackPtr s)
    (hr : ReadyToStep v) (hc : CodeIn Extracted.programImage v) (hdf : DirectionFlagClear v.RFLAGS)
    (hrip : v.RIP = p) (hsite : p = 0x101d4c ∨ p = 0x101d78)
    (hdi : v.regValue .rdi = UpdateKind.updateFinalize.context s + 72)
    (hcount : 64 * (v.regValue .rdx).toNat = blocks.size)
    (hsrc : (v.regValue .rsi = UpdateKind.updateFinalize.context s ∧ blocks.size = 64) ∨
      ∃ off, v.regValue .rsi = (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 off ∧
        off + blocks.size ≤ input.size ∧ (UpdateKind.inputRegion .updateFinalize s input).start ≠ 0)
    (hbytes : (Compress.inputRegion v blocks).HasBytes v.external blocks)
    (hhash : (⟨(UpdateKind.updateFinalize.context s + 72).toNat, 20⟩ : MemoryRegion).HasBytes
      v.external (Wrapper.Hash.Serialize.stateBytes hash)) :
    ∃ t, Compressed boundary (p + 5) s v hash blocks t := by
  let scratch : MemoryRegion := ⟨(stackPtr s).toNat - 344, 344⟩
  let output : MemoryRegion := ⟨(UpdateKind.updateFinalize.context s + 72).toNat, 20⟩
  let src := Compress.inputRegion v blocks
  have hl := h.stackLow
  have hh : (stackPtr s).toNat + 216 + 92 < 2^32 := h.stackHigh
  have hctx : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 216 :=
    toNat_add_ofNat _ 216 (by omega)
  have hon : output.start = (stackPtr s).toNat + 288 := by
    dsimp only [output]
    change (UpdateKind.updateFinalize.context s + BitVec.ofNat 64 72).toNat = _
    rw [toNat_add_ofNat (UpdateKind.updateFinalize.context s) 72 (by rw [hctx]; omega), hctx]
  have hsub (i : Nat) (hi : output.Contains i) :
      (UpdateKind.updateFinalize.contextRegion s).Contains i := by
    change output.start ≤ i ∧ i < output.start + 20 at hi
    change (UpdateKind.updateFinalize.context s).toNat ≤ i ∧
      i < (UpdateKind.updateFinalize.context s).toNat + 92
    rw [hctx]
    omega
  have hsep : output.Disjoint scratch := by
    intro i hi hj
    change output.start ≤ i ∧ i < output.start + 20 at hi
    change _ ≤ i ∧ i < (stackPtr s).toNat - 344 + 344 at hj
    omega
  have hsrcGeo : src.start ≠ 0 ∧ src.Bounded ∧ src.Disjoint output ∧ src.Disjoint scratch := by
    change (v.regValue .rsi).toNat ≠ 0 ∧ (v.regValue .rsi).toNat + blocks.size < 2^32 ∧
      src.Disjoint output ∧ src.Disjoint scratch
    rcases hsrc with ⟨he, hs⟩ | ⟨off, he, ho, hpos⟩
    · rw [he, hctx, hs]
      have hn : src.start = (stackPtr s).toNat + 216 := by
        change (v.regValue .rsi).toNat = _
        rw [he, hctx]
      refine ⟨by omega, by omega, ?_, ?_⟩ <;> intro i hi hj
      all_goals change src.start ≤ i ∧ i < src.start + blocks.size at hi
      · change output.start ≤ i ∧ i < output.start + 20 at hj
        omega
      · change _ ≤ i ∧ i < (stackPtr s).toNat - 344 + 344 at hj
        omega
    · have hi : ((Operand.reg 14 : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
      change ((Operand.reg 14 : Operand 64).read s).toNat ≠ 0 at hpos
      have hn : (v.regValue .rsi).toNat = ((Operand.reg 14 : Operand 64).read s).toNat + off := by
        rw [he, toNat_add_ofNat _ _ (by omega)]
      have hs (i : Nat) (hx : src.Contains i) :
          (UpdateKind.updateFinalize.inputRegion s input).Contains i := by
        change (v.regValue .rsi).toNat ≤ i ∧ i < (v.regValue .rsi).toNat + blocks.size at hx
        change ((Operand.reg 14 : Operand 64).read s).toNat ≤ i ∧
          i < ((Operand.reg 14 : Operand 64).read s).toNat + input.size
        omega
      exact ⟨by omega, by omega, fun i hx hy ↦ h.inputContext i (hs i hx) (hsub i hy),
        fun i hx ↦ h.inputScratch i (hs i hx)⟩
  have hpush : (pushAddr v).toNat = (stackPtr s).toNat - 8 := by
    rw [pushAddr, hsp, BitVec.toNat_sub_of_le]
    · rfl
    · change 8 ≤ (stackPtr s).toNat
      omega
  have hscratch : scratch.Bounded := by
    change (stackPtr s).toNat - 344 + 344 < 2^32
    omega
  have hw : MemoryRoutines.WritableRange v (pushAddr v) 8 := by
    apply DigestPrepare.writableRange_of_region hscratch (allocated_of_agrees ha h.scratchAllocated)
      h.scratchAvoids
    · change (stackPtr s).toNat - 344 ≤ _
      omega
    · change _ ≤ (stackPtr s).toNat - 344 + 344
      omega
  let disp : BitVec 32 := (0x1024e0 - (p + 5)).setWidth 32
  have target : branchTarget p 5 (disp.signExtend 64) = 0x1024e0 := by
    rcases hsite with rfl | rfl <;> rfl
  have code : CodeIn (codeRange p (encodeCallRel32 disp)) v := by
    rcases hsite with rfl | rfl
    · change CodeIn (codeRange 0x101d4c (encodeCallRel32 0x78f)) v
      rw [show encodeCallRel32 0x78f = Extracted.textBytes.toListFrom 0x1d4c 5 by decide +kernel]
      exact Sha1.Proofs.Compress.Machine.program_text_slice hc 0x1d4c 5 (by decide +kernel)
    · change CodeIn (codeRange 0x101d78 (encodeCallRel32 0x763)) v
      rw [show encodeCallRel32 0x763 = Extracted.textBytes.toListFrom 0x1d78 5 by decide +kernel]
      exact Sha1.Proofs.Compress.Machine.program_text_slice hc 0x1d78 5 (by decide +kernel)
  have apart : RangeApart (pushAddr v) 8 p 5 := by
    rcases hsite with rfl | rfl
    · exact Finalize.rangeApart_text (offset := 0x1d4c) hw.code (by decide +kernel)
    · exact Finalize.rangeApart_text (offset := 0x1d78) hw.code (by decide +kernel)
  have step := Common.Instructions.MovStore.call_rel32_effect_step p disp (by rw [target]; decide)
  obtain ⟨u, adv, ready, he⟩ := step.advances hr code
    ⟨hrip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, apart⟩
    (boundary := boundary) (by
      change branchTarget p 5 (disp.signExtend 64) ≠ _
      rw [target]
      exact Finalize.text_address_ne_return h.boundaryOutside 0x24e0 (by decide +kernel))
  have hcode := callEffect_code he hc hw.code
  have hb := callEffect_returnBoundary he
  have hspu : (u.regValue .rsp).toNat = (stackPtr s).toNat - 8 :=
    (congrArg BitVec.toNat (callEffect_rsp he)).trans hpush
  have hstack : Stack.region u Compress.minStackBytes = scratch := by
    change (⟨(u.regValue .rsp).toNat - 336,
      (u.regValue .rsp).toNat + 8 - ((u.regValue .rsp).toNat - 336)⟩ : MemoryRegion) =
      ⟨(stackPtr s).toNat - 344, 344⟩
    congr 1 <;> omega
  have hdiu : u.regValue .rdi = UpdateKind.updateFinalize.context s + 72 :=
    (callEffect_read he (r := 7) (by decide)).trans hdi
  have houtput : Compress.outputRegion u = output := by
    unfold Compress.outputRegion registerRegion
    rw [hdiu]
  have hsource : Compress.inputRegion u blocks = src := by
    have hrsi : u.regValue .rsi = v.regValue .rsi := callEffect_read he (r := 6) (by decide)
    change (⟨(u.regValue .rsi).toNat, blocks.size⟩ : MemoryRegion) = ⟨(v.regValue .rsi).toNat, _⟩
    rw [hrsi]
  have hslot (x : BitVec 64) (hx : (Component.mem (pushAddr v) 8).Covers x) :
      scratch.Contains x.toNat := by
    obtain ⟨i, hi, rfl⟩ := hx
    change (stackPtr s).toNat - 344 ≤ _ ∧ _ < (stackPtr s).toNat - 344 + 344
    rw [toNat_add_ofNat _ _ (by omega), hpush]
    omega
  have hunchanged (x : BitVec 64) (hx : ¬ scratch.Contains x.toNat) :
      u.external[x]? = v.external[x]? := by
    apply he.agrees.byte
    intro c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact hx (hslot _ hcov)
    · exact hcov
  have preserve {r : MemoryRegion} {bytes : ByteArray} (hd : r.Disjoint scratch)
      (hrb : r.Bounded) (hm : r.HasBytes v.external bytes) : r.HasBytes u.external bytes := by
    refine ⟨hm.1, fun i ↦ ?_⟩
    rw [← hm.2 i]
    apply hunchanged
    apply hd
    have hi := i.isLt
    have hn : bytes.size = r.size := hm.1
    change r.start + r.size < 2^32 at hrb
    change r.start ≤ _ ∧ _ < r.start + r.size
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have houtBound : output.Bounded := by
    change output.start + 20 < 2^32
    omega
  have call : Sha1.Proofs.Compress.Routine.CallData ⟨u, hash, blocks⟩ := by
    refine ⟨he.agrees.directionFlagClear (by simp [pushEffect_components]) ⟨hdf⟩,
      fun a b hm ↦ (hcode (a,b) hm).2, ?_, ?_, ?_, ?_, ?_⟩
    · have hdx : u.regValue .rdx = v.regValue .rdx := callEffect_read he (r := 2) (by decide)
      change 64 * (u.regValue .rdx).toNat = blocks.size
      rwa [hdx]
    · change ValidInput u (Compress.inputRegion u blocks) blocks
      rw [hsource]
      exact ⟨hsrcGeo.1, hsrcGeo.2.1, preserve hsrcGeo.2.2.2 hsrcGeo.2.1 hbytes⟩
    · change (Compress.outputRegion u).start ≠ 0 ∧ (Compress.outputRegion u).Bounded ∧
        (Compress.outputRegion u).HasBytes u.external (Wrapper.Hash.Serialize.stateBytes hash)
      rw [houtput]
      exact ⟨by omega, houtBound, preserve hsep houtBound hhash⟩
    · change Stack.Valid u Compress.minStackBytes
      unfold Stack.Valid
      rw [hstack]
      refine ⟨hscratch, allocated_of_agrees (ha.trans he.agrees) h.scratchAllocated, ?_, ?_⟩
      · change 336 ≤ (u.regValue .rsp).toNat
        omega
      · change (u.regValue .rsp).toNat % 16 = 8
        have := h.stackAligned
        omega
    · change MemorySeparation [Compress.inputRegion u blocks] (Compress.outputRegion u)
        (Stack.region u Compress.minStackBytes)
      rw [hsource, houtput, hstack]
      refine ⟨hsep, ?_⟩
      intro region hm
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨fun r hr ↦ (List.mem_singleton.mp hr) ▸ hsrcGeo.2.2.1,
          fun x hx ↦ h.contextAvoids x (hsub _ hx)⟩
      · exact ⟨fun r hr ↦ (List.mem_singleton.mp hr) ▸ hsrcGeo.2.2.2, h.scratchAvoids⟩
  let ctx : Sha1.Proofs.Compress.Routine.Context := ⟨u, hash, blocks⟩
  have retNe : p + BitVec.ofNat 64 5 ≠ boundary.rip := by
    rcases hsite with rfl | rfl
    · exact Finalize.text_address_ne_return h.boundaryOutside 0x1d51 (by decide +kernel)
    · exact Finalize.text_address_ne_return h.boundaryOutside 0x1d7d (by decide +kernel)
  have retLow : (p + BitVec.ofNat 64 5).toNat < 0x1024e0 := by
    rcases hsite with rfl | rfl <;> decide
  have valid : ctx.Valid bindings := by
    refine ⟨⟨ready.smrr, ready.memoryType, h.stride, ready.features.lzcnt⟩, ready.cpu, ready,
      hcode, call, Or.inr (he.rip.trans target), ?_, ?_⟩
    · change (returnBoundary u).rip.toNat < 2^32
      rw [hb]
      exact Nat.lt_trans retLow (by decide)
    · change Sha1.Proofs.Compress.Machine.OutsideCompression (returnBoundary u).rip
      rw [hb]
      exact Or.inl retLow
  obtain ⟨fuel, t, hadv, ht, saved, _, mem, _, _, hag, trip, tsp, state⟩ :=
    Sha1.Proofs.Compress.Routine.execution_advance Sha1.Proofs.Compress.block_correct
      boundary bindings ctx valid
      (Sha1.Proofs.Compress.Routine.outsideCompression_of_notInProgram h.boundaryOutside)
      (by change boundary.rip ≠ (returnBoundary u).rip; rw [hb]; exact retNe.symm)
  change t.RIP = (returnBoundary u).rip at trip
  change stackPtr t = (returnBoundary u).rsp at tsp
  rw [hb] at trip tsp
  change MemoryWriteFrame u t #v[Compress.outputRegion u, Stack.region u Compress.minStackBytes] at mem
  rw [hstack, houtput] at mem
  have code' : CodeIn Extracted.programImage t := by
    intro x hx
    refine ⟨(hcode x hx).1, ?_⟩
    rw [mem]
    · exact (hcode x hx).2
    · intro r hrm hin
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hrm
      rcases hrm with rfl | rfl
      · exact h.contextAvoids _ (hsub _ hin) (.inl ⟨_,hx⟩)
      · exact h.scratchAvoids _ hin (.inl ⟨_,hx⟩)
  have covers (r : MemoryRegion) (x : BitVec 64) (hx : r.Contains x.toNat) :
      (Component.mem (BitVec.ofNat 64 r.start) r.size).Covers x := by
    refine ⟨x.toNat - r.start, by have := hx.1; have := hx.2; omega, ?_⟩
    rw [← BitVec.ofNat_add, Nat.add_sub_of_le hx.1, BitVec.ofNat_toNat]
    rfl
  have hall := he.agrees.trans hag
  have agrees : AgreesExcept (compressChanges s) v t := by
    refine ⟨?_, ?_, hall.rest, hall.grow⟩
    · intro c hn hm
      by_cases hc : c ∈ (callEffect (fun _ ↦ branchTarget p 5 (disp.signExtend 64))
            (p + BitVec.ofNat 64 5) v).components ++ Sha1.Proofs.Compress.Routine.compressionChanges ctx
      · simp only [pushEffect_components, Sha1.Proofs.Compress.Routine.compressionChanges,
          Sha1.Proofs.Compress.Routine.frameComponents, Sha1.Proofs.Compress.Machine.scratchComponents,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        repeat' rcases hc with rfl | hc
        all_goals first
          | exact Bool.noConfusion hm
          | exact tsp
          | exact (saved .rbx (by decide)).trans (callEffect_read he (r := 3) (by decide))
          | exact (saved .rbp (by decide)).trans (callEffect_read he (r := 5) (by decide))
          | exact (saved .r12 (by decide)).trans (callEffect_read he (r := 12) (by decide))
          | exact (saved .r13 (by decide)).trans (callEffect_read he (r := 13) (by decide))
          | exact (saved .r14 (by decide)).trans (callEffect_read he (r := 14) (by decide))
          | exact (saved .r15 (by decide)).trans (callEffect_read he (r := 15) (by decide))
          | (exfalso; apply hn; simp [compressChanges])
      · exact hall.agree c hc hm
    · intro x hx
      have ho : ¬output.Contains x.toNat := by
        intro hin
        apply hx (.mem (UpdateKind.updateFinalize.context s + 72) 20) (by simp [compressChanges])
        simpa only [output, BitVec.ofNat_toNat, BitVec.setWidth_eq] using covers output x hin
      have hs : ¬scratch.Contains x.toNat := by
        intro hin
        exact hx _ (by simp [scratch, compressChanges]) (covers scratch x hin)
      apply Eq.trans (mem x ?_) (hunchanged x hs)
      intro r hm
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ho
      · exact hs
  refine ⟨t, ⟨⟨_, adv.trans hadv⟩, ht, code', trip, agrees, ?_⟩⟩
  change (Compress.outputRegion u).HasBytes t.external
    ⟨(Hasher.stateBytes (ctx.state ctx.count)).toArray⟩ at state
  rw [houtput] at state
  simpa only [Sha1.Proofs.Compress.Routine.Context.state_count, ctx, Wrapper.Absorb.compressBlocks,
    Wrapper.Hash.Serialize.stateBytes] using state

end Sha1.Proofs.Buffered.Update.Slices.Full
