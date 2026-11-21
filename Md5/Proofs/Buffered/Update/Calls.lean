import Md5.Proofs.MemoryRoutines.Contracts
import Md5.Proofs.MemoryRoutines.Memset
import Md5.Proofs.MemoryRoutines.Memcpy
import Md5.Proofs.Buffered.Update.Memory
import X86Proofs.Instructions.Call.Triple

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem outside_text_range_of_not_inProgram {address : BitVec 64}
    (h : ¬ InProgram address) (lo hi : Nat) (hlo : 0x100000 ≤ lo)
    (hhi : hi ≤ 0x100000 + Extracted.textBytes.size) :
    address.toNat < lo ∨ hi ≤ address.toNat := by
  apply Classical.byContradiction
  intro hn
  have hlow : lo ≤ address.toNat := by omega
  have hhigh : address.toNat < hi := by omega
  have hoff : address.toNat - 0x100000 < Extracted.textBytes.size := by omega
  have heq : Extracted.textAddress + BitVec.ofNat 64 (address.toNat - 0x100000) =
      address := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (address.toNat - 0x100000) = address
    rw [← BitVec.ofNat_add,
      show 0x100000 + (address.toNat - 0x100000) = address.toNat by omega,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact h (heq ▸ Block.text_address_in_program _ hoff)

structure CallSitePre (entry : BitVec 64) (codeLength : Nat) (ret : BitVec 64)
    (s : RamState) : Prop where
  df : DirectionFlagClear s.RFLAGS
  dst : MemoryRoutines.WritableRange s (rdi.read s) (MemoryRoutines.rdx.read s).toNat
  slot : MemReadable s (pushAddr s) 8
  slotCode : ∀ i < 8, ¬ InProgram (pushAddr s + BitVec.ofNat 64 i)
  dstSlot : RangeApart (rdi.read s) (MemoryRoutines.rdx.read s).toNat (pushAddr s) 8
  returnLow : ret.toNat < 2^32
  returnOutside : ret.toNat < entry.toNat ∨ entry.toNat + codeLength ≤ ret.toNat

structure MemcpySitePre (ret : BitVec 64) (s : RamState) : Prop
    extends CallSitePre 0x1024b0 47 ret s where
  src : MemReadable s (rsi.read s) (MemoryRoutines.rdx.read s).toNat
  srcSlot : RangeApart (rsi.read s) (MemoryRoutines.rdx.read s).toNat (pushAddr s) 8
  disjoint : (rsi.read s).toNat + (MemoryRoutines.rdx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + (MemoryRoutines.rdx.read s).toNat ≤ (rsi.read s).toNat

abbrev MemsetSitePre := CallSitePre 0x102460 69

def callSiteChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (rdi.read s) (MemoryRoutines.rdx.read s).toNat, .mem (pushAddr s) 8]

structure CallSiteResult [Bindings] (boundary : ReturnBoundary) (ret : BitVec 64)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = ret
  rsp : stackPtr t = stackPtr s
  result : rax.read t = rdi.read s
  agrees : AgreesExcept (callSiteChanges s) s t

structure MemcpySiteResult [Bindings] (boundary : ReturnBoundary) (ret : BitVec 64)
    (s t : RamState) : Prop extends CallSiteResult boundary ret s t where
  copy : ∀ i < (MemoryRoutines.rdx.read s).toNat,
    t.external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]?

structure MemsetSiteResult [Bindings] (boundary : ReturnBoundary) (ret : BitVec 64)
    (s t : RamState) : Prop extends CallSiteResult boundary ret s t where
  fill : ∀ i < (MemoryRoutines.rdx.read s).toNat,
    t.external[rdi.read s + BitVec.ofNat 64 i]? =
      some (UInt8.ofBitVec ((rsi.read s).setWidth 8))

theorem callEffect_read {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u)
    {r : BitVec 5} (hr : r ≠ 4) :
    (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read s :=
  h.agrees.read (by
    simp only [pushEffect_components, List.mem_cons, Component.reg.injEq,
      reduceCtorEq, List.not_mem_nil, or_false]
    exact hr)

theorem callEffect_rsp {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u) :
    stackPtr u = pushAddr s := h.writes.1

theorem callEffect_returnBoundary {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u) :
    returnBoundary u = { rip := ret, rsp := stackPtr s } := by
  have hs := callEffect_stack h
  change ({ rip := stackTop u, rsp := stackPtr u + 8 } : ReturnBoundary) = _
  rw [hs.1, hs.2]

theorem callEffect_code {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u)
    (hc : CodeIn Extracted.programImage s)
    (ha : ∀ i < 8, ¬ InProgram (pushAddr s + BitVec.ofNat 64 i)) :
    CodeIn Extracted.programImage u := by
  apply CodeIn.of_agreesExcept h.agrees _ hc
  intro x hx c hc hcover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover
  · obtain ⟨i, hi, he⟩ := hcover
    exact ha i hi ⟨x.2, he ▸ hx⟩
  · exact hcover

theorem CallSitePre.after_call {entry ret : BitVec 64} {codeLength : Nat}
    {target : RamState → BitVec 64} {s u : RamState}
    (hp : CallSitePre entry codeLength ret s)
    (h : (callEffect target ret s).Holds s u) (htarget : target s = entry) :
    MemoryRoutines.CallPre entry codeLength u := by
  have hdi := callEffect_read h (r := 7) (by decide)
  have hdx := callEffect_read h (r := 2) (by decide)
  change rdi.read u = rdi.read s at hdi
  change MemoryRoutines.rdx.read u = MemoryRoutines.rdx.read s at hdx
  have hreturn := callEffect_returnBoundary h
  refine ⟨h.rip.trans htarget,
    (h.agrees.directionFlagClear (by simp [callEffect, pushEffect_components]) ⟨hp.df⟩).df,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdi, hdx]
    exact hp.dst.of_agrees h.agrees
  · rw [callEffect_rsp h]
    exact ⟨hp.slot.low, fun i hi ↦ h.agrees.grow _ (hp.slot.mem i hi)⟩
  · rw [hdi, hdx, callEffect_rsp h]
    exact hp.dstSlot
  · rw [hreturn]
    exact hp.returnLow
  · rw [hreturn]
    exact hp.returnOutside

theorem MemcpySitePre.after_call {ret : BitVec 64} {target : RamState → BitVec 64}
    {s u : RamState} (hp : MemcpySitePre ret s)
    (h : (callEffect target ret s).Holds s u) (htarget : target s = 0x1024b0) :
    MemoryRoutines.MemcpyPre u := by
  have hdi := callEffect_read h (r := 7) (by decide)
  have hsi := callEffect_read h (r := 6) (by decide)
  have hdx := callEffect_read h (r := 2) (by decide)
  change rdi.read u = rdi.read s at hdi
  change rsi.read u = rsi.read s at hsi
  change MemoryRoutines.rdx.read u = MemoryRoutines.rdx.read s at hdx
  refine ⟨hp.toCallSitePre.after_call h htarget, ?_, ?_⟩
  · rw [hsi, hdx]
    exact ⟨hp.src.low, fun i hi ↦ h.agrees.grow _ (hp.src.mem i hi)⟩
  · rw [hsi, hdx, hdi]
    exact hp.disjoint

theorem CallSiteResult.of_call_return [Bindings] {boundary : ReturnBoundary}
    {entry ret : BitVec 64} {codeLength : Nat} {target : RamState → BitVec 64}
    {s u t : RamState} {callFuel bodyFuel : Nat}
    (hp : CallSitePre entry codeLength ret s) (hc : CodeIn Extracted.programImage s)
    (he : (callEffect target ret s).Holds s u)
    (hcall : Advances boundary callFuel s u) (hbody : Advances boundary bodyFuel u t)
    (hr : MemoryRoutines.CallResult u t) : CallSiteResult boundary ret s t := by
  have hdi := callEffect_read he (r := 7) (by decide)
  have hdx := callEffect_read he (r := 2) (by decide)
  change rdi.read u = rdi.read s at hdi
  change MemoryRoutines.rdx.read u = MemoryRoutines.rdx.read s at hdx
  have hboundary := callEffect_returnBoundary he
  have hrsp : stackPtr t = stackPtr s := by
    rw [hr.rsp]
    exact (callEffect_stack he).2
  have hd : MemoryRoutines.WritableRange u (rdi.read u) (MemoryRoutines.rdx.read u).toNat := by
    rw [hdi, hdx]
    exact hp.dst.of_agrees he.agrees
  refine ⟨⟨callFuel + bodyFuel, hcall.trans hbody⟩, hr.ready,
    hr.codeIn hd (callEffect_code he hc hp.slotCode), ?_, hrsp, hr.result.trans hdi, ?_⟩
  · rw [hr.rip, hboundary]
  · have hchanges : MemoryRoutines.callChanges u = MemoryRoutines.callChanges s := by
      simp only [MemoryRoutines.callChanges, hdi, hdx]
    have hagrees := he.agrees.trans hr.agrees
    rw [hchanges] at hagrees
    have hw : AgreesExcept (.reg 4 :: callSiteChanges s) s t := hagrees.mono (by
      intro c hc
      simp only [pushEffect_components, MemoryRoutines.callChanges, callSiteChanges,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with (rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals simp)
    apply hw.narrow
    intro c hc hn
    have heq : c = .reg 4 := by simpa only [List.mem_cons, hn, or_false] using hc
    subst c
    exact hrsp

theorem MemcpySiteResult.of_call_return [Bindings] {boundary : ReturnBoundary}
    {ret : BitVec 64} {target : RamState → BitVec 64} {s u t : RamState}
    {callFuel bodyFuel : Nat} (hp : MemcpySitePre ret s)
    (hc : CodeIn Extracted.programImage s) (he : (callEffect target ret s).Holds s u)
    (hcall : Advances boundary callFuel s u) (hbody : Advances boundary bodyFuel u t)
    (hr : MemoryRoutines.MemcpyResult u t) : MemcpySiteResult boundary ret s t := by
  refine ⟨CallSiteResult.of_call_return hp.toCallSitePre hc he hcall hbody hr.toCallResult, ?_⟩
  have hdi := callEffect_read he (r := 7) (by decide)
  have hsi := callEffect_read he (r := 6) (by decide)
  have hdx := callEffect_read he (r := 2) (by decide)
  change rdi.read u = rdi.read s at hdi
  change rsi.read u = rsi.read s at hsi
  change MemoryRoutines.rdx.read u = MemoryRoutines.rdx.read s at hdx
  intro i hi
  have hh := hr.copy i (by simpa only [hdx] using hi)
  rw [hdi, hsi] at hh
  apply hh.trans
  apply he.agrees.byte
  intro c hc hcover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover
  · obtain ⟨j, hj, hjx⟩ := hcover
    exact hp.srcSlot i hi j hj hjx
  · exact hcover

theorem MemsetSiteResult.of_call_return [Bindings] {boundary : ReturnBoundary}
    {ret : BitVec 64} {target : RamState → BitVec 64} {s u t : RamState}
    {callFuel bodyFuel : Nat} (hp : MemsetSitePre ret s)
    (hc : CodeIn Extracted.programImage s) (he : (callEffect target ret s).Holds s u)
    (hcall : Advances boundary callFuel s u) (hbody : Advances boundary bodyFuel u t)
    (hr : MemoryRoutines.MemsetResult u t) : MemsetSiteResult boundary ret s t := by
  refine ⟨CallSiteResult.of_call_return hp hc he hcall hbody hr.toCallResult, ?_⟩
  have hdi := callEffect_read he (r := 7) (by decide)
  have hsi := callEffect_read he (r := 6) (by decide)
  have hdx := callEffect_read he (r := 2) (by decide)
  change rdi.read u = rdi.read s at hdi
  change rsi.read u = rsi.read s at hsi
  change MemoryRoutines.rdx.read u = MemoryRoutines.rdx.read s at hdx
  intro i hi
  simpa only [hdi, hsi] using hr.fill i (by simpa only [hdx] using hi)

theorem memcpy_call_of_advance [Bindings] {boundary : ReturnBoundary}
    {ret : BitVec 64} {target : RamState → BitVec 64} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : MemcpySitePre ret s)
    (htarget : target s = 0x1024b0) (hentryNe : 0x1024b0 ≠ boundary.rip)
    (hretNe : ret ≠ boundary.rip)
    (hRun : ∀ u, ReadyToStep u → CodeIn Extracted.programImage u →
      MemoryRoutines.MemcpyPre u → (returnBoundary u).rip ≠ boundary.rip →
      ∃ fuel t, Advances boundary fuel u t ∧ MemoryRoutines.MemcpyResult u t) :
    ∃ t, MemcpySiteResult boundary ret s t := by
  obtain ⟨u, ha, hu, he⟩ := hstep.advances hready hbytes hpre (htarget ▸ hentryNe)
  have hreturn := callEffect_returnBoundary he
  obtain ⟨fuel, t, hb, hr⟩ := hRun u hu (callEffect_code he hcode hp.slotCode)
    (hp.after_call he htarget) (by rw [hreturn]; exact hretNe)
  exact ⟨t, MemcpySiteResult.of_call_return hp hcode he ha hb hr⟩

theorem memset_call_of_advance [Bindings] {boundary : ReturnBoundary}
    {ret : BitVec 64} {target : RamState → BitVec 64} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : MemsetSitePre ret s)
    (htarget : target s = 0x102460) (hentryNe : 0x102460 ≠ boundary.rip)
    (hretNe : ret ≠ boundary.rip)
    (hRun : ∀ u, ReadyToStep u → CodeIn Extracted.programImage u →
      MemoryRoutines.MemsetPre u → (returnBoundary u).rip ≠ boundary.rip →
      ∃ fuel t, Advances boundary fuel u t ∧ MemoryRoutines.MemsetResult u t) :
    ∃ t, MemsetSiteResult boundary ret s t := by
  obtain ⟨u, ha, hu, he⟩ := hstep.advances hready hbytes hpre (htarget ▸ hentryNe)
  have hreturn := callEffect_returnBoundary he
  obtain ⟨fuel, t, hb, hr⟩ := hRun u hu (callEffect_code he hcode hp.slotCode)
    (hp.after_call he htarget) (by rw [hreturn]; exact hretNe)
  exact ⟨t, MemsetSiteResult.of_call_return hp hcode he ha hb hr⟩

theorem memset_call [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary}
    (hout : boundary.rip.toNat < 0x102460 ∨ 0x1024a5 ≤ boundary.rip.toNat)
    {ret : BitVec 64} {target : RamState → BitVec 64} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : MemsetSitePre ret s)
    (htarget : target s = 0x102460) (hretNe : ret ≠ boundary.rip) :
    ∃ t, MemsetSiteResult boundary ret s t := by
  have hentryNe : (0x102460 : BitVec 64) ≠ boundary.rip := by
    intro he
    have hn := congrArg BitVec.toNat he
    change 0x102460 = boundary.rip.toNat at hn
    omega
  exact memset_call_of_advance hstep hready hcode hbytes hpre hp htarget hentryNe hretNe
    (MemoryRoutines.memset_advances hstride boundary hout)

theorem memcpy_call [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary}
    (hout : boundary.rip.toNat < 0x1024b0 ∨ 0x1024df ≤ boundary.rip.toNat)
    {ret : BitVec 64} {target : RamState → BitVec 64} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : MemcpySitePre ret s)
    (htarget : target s = 0x1024b0) (hretNe : ret ≠ boundary.rip) :
    ∃ t, MemcpySiteResult boundary ret s t := by
  have hentryNe : (0x1024b0 : BitVec 64) ≠ boundary.rip := by
    intro he
    have hn := congrArg BitVec.toNat he
    change 0x1024b0 = boundary.rip.toNat at hn
    omega
  exact memcpy_call_of_advance hstep hready hcode hbytes hpre hp htarget hentryNe hretNe
    (MemoryRoutines.memcpy_advances hstride boundary hout)

theorem UpdatePre.memcpySitePre [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s t : RamState} (h : UpdatePre kind boundary message input s)
    {changes : List Component} (ha : AgreesExcept changes s t)
    {ret : BitVec 64} {pos offset count : Nat}
    (hsp : stackPtr t = stackPtr s)
    (hdi : rdi.read t = kind.context s + BitVec.ofNat 64 pos)
    (hsi : rsi.read t = (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset)
    (hdx : MemoryRoutines.rdx.read t = BitVec.ofNat 64 count)
    (hpos : pos + count ≤ 64) (hoff : offset + count ≤ input.size)
    (hret : ret.toNat < 2^32)
    (hout : ret.toNat < 0x1024b0 ∨ 0x1024df ≤ ret.toNat)
    (hd : Component.df ∉ changes := by simp [UpdateKind.changes, UpdateKind.workRegisters]) :
    MemcpySitePre ret t := by
  let src := (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset
  let dst := kind.context s + BitVec.ofNat 64 pos
  have hinput := h.inputBounded
  change ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + input.size < 2^32
    at hinput
  have hcontext := h.contextBounded
  change (kind.context s).toNat + 88 < 2^32 at hcontext
  have hsrc : src.toNat = ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + offset :=
    toNat_add_ofNat _ _ (by omega)
  have hdst : dst.toNat = (kind.context s).toNat + pos :=
    toNat_add_ofNat _ _ (by omega)
  have hslot : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
    change (stackPtr s - 8#64).toNat = _
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      have := h.stackLow
      change 8 ≤ (stackPtr s).toNat
      omega)]
    rfl
  have hcount : (MemoryRoutines.rdx.read t).toNat = count := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show count < 2^64 by omega)]
  have hpush : pushAddr t = pushAddr s := by simp only [pushAddr, hsp]
  have hdst' : dst = stackPtr s + BitVec.ofNat 64 (kind.contextOffset + pos) := by
    simp only [dst, UpdateKind.context, BitVec.ofNat_add, BitVec.add_assoc]
  have hwrite : MemoryRoutines.WritableRange t dst count := by
    rw [hdst']
    exact h.contextWritable_of_agrees ha pos count (by omega)
  have hsrcStart : (kind.inputRegion s input).start ≤ src.toNat := by
    change ((Operand.reg kind.inputRegister : Operand 64).read s).toNat ≤ _
    rw [hsrc]
    omega
  have hsrcEnd : src.toNat + count ≤
      (kind.inputRegion s input).start + (kind.inputRegion s input).size := by
    change _ ≤ ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + input.size
    rw [hsrc]
    omega
  have hdstStart : (kind.contextRegion s).start ≤ dst.toNat := by
    change (kind.context s).toNat ≤ _
    rw [hdst]
    omega
  have hdstEnd : dst.toNat + count ≤ (kind.contextRegion s).start + (kind.contextRegion s).size := by
    change _ ≤ (kind.context s).toNat + 88
    rw [hdst]
    omega
  have hslotStart : (UpdateKind.scratchRegion s).start ≤ (pushAddr s).toNat := by
    change (stackPtr s).toNat - 320 ≤ _
    rw [hslot]
    omega
  have hslotEnd : (pushAddr s).toNat + 8 ≤
      (UpdateKind.scratchRegion s).start + (UpdateKind.scratchRegion s).size := by
    change _ ≤ (stackPtr s).toNat - 320 + 320
    rw [hslot]
    have := h.stackLow
    omega
  have hcontextScratch : (kind.contextRegion s).Disjoint (UpdateKind.scratchRegion s) := by
    intro address hin hscratch
    change (kind.context s).toNat ≤ address ∧ address < (kind.context s).toNat + 88 at hin
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hscratch
    rw [h.context_toNat] at hin
    have := h.stackLow
    omega
  refine ⟨⟨(ha.directionFlagClear hd h.df).df, ?_, ?_, ?_, ?_, hret, hout⟩, ?_, ?_, ?_⟩
  · rw [hdi, hcount]
    exact hwrite
  · rw [hpush]
    exact (h.callSlotWritable_of_agrees ha).readable
  · rw [hpush]
    exact (h.scratchWritable_of_agrees ha 8 8 (by decide) (by decide)).code
  · rw [hdi, hcount, hpush]
    exact rangeApart_of_regions h.contextBounded h.scratchBounded hcontextScratch
      hdstStart hdstEnd hslotStart hslotEnd
  · rw [hsi, hcount]
    exact memReadable_of_allocated
      (allocated_of_agrees ha (allocated_of_hasBytes h.inputBytes))
      (by change src.toNat + count ≤ 2^32; rw [hsrc]; omega) hsrcStart hsrcEnd
  · rw [hsi, hcount, hpush]
    exact rangeApart_of_regions h.inputBounded h.scratchBounded h.inputScratch
      hsrcStart hsrcEnd hslotStart hslotEnd
  · rw [hsi, hdi, hcount]
    exact rangeApart_ordered (rangeApart_of_regions h.inputBounded h.contextBounded h.inputContext
      hsrcStart hsrcEnd hdstStart hdstEnd)

theorem CallSiteResult.update_agrees [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial) {ret : BitVec 64}
    (hr : CallSiteResult boundary ret s t) {pos : Nat}
    (hsp : stackPtr s = stackPtr initial)
    (hdi : rdi.read s = kind.context initial + BitVec.ofNat 64 pos)
    (hcount : pos + (MemoryRoutines.rdx.read s).toNat ≤ 88) :
    AgreesExcept (kind.changes initial) s t := by
  have hpush : pushAddr s =
      BitVec.ofNat 64 (UpdateKind.scratchRegion initial).start + BitVec.ofNat 64 312 := by
    have hval : stackPtr initial =
        BitVec.ofNat 64 ((stackPtr initial).toNat - 320) + 320#64 := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel h.stackLow,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    change pushAddr s = BitVec.ofNat 64 ((stackPtr initial).toNat - 320) + 312#64
    calc
      pushAddr s = stackPtr initial - 8#64 := by simp only [pushAddr, hsp]; rfl
      _ = (BitVec.ofNat 64 ((stackPtr initial).toNat - 320) + 320#64) - 8#64 :=
        congrArg (fun x ↦ x - 8#64) hval
      _ = BitVec.ofNat 64 ((stackPtr initial).toNat - 320) + 312#64 := by
        rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
  apply hr.agrees.widen
  · intro c hc hm
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [UpdateKind.changes, Component.isMem]
  · intro address c hc hcover
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    · refine ⟨.mem (kind.context initial) 88, by simp [UpdateKind.changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨pos + i, by omega, ?_⟩
      rw [hdi, BitVec.add_assoc, BitVec.ofNat_add]
    · refine ⟨.mem (BitVec.ofNat 64 (UpdateKind.scratchRegion initial).start) 320,
        by simp [UpdateKind.changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨312 + i, by omega, ?_⟩
      rw [hpush, BitVec.add_assoc, BitVec.ofNat_add]

theorem MemcpySiteResult.hasBytes [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {s t : RamState} {bytes : ByteArray} (h : MemcpySiteResult boundary ret s t)
    (hlen : (MemoryRoutines.rdx.read s).toNat = bytes.size)
    (hb : (⟨(rsi.read s).toNat, bytes.size⟩ : MemoryRegion).HasBytes s.external bytes) :
    (⟨(rdi.read s).toNat, bytes.size⟩ : MemoryRegion).HasBytes t.external bytes :=
  hasBytes_of_copy (fun i hi ↦ h.copy i (by simpa only [hlen] using hi)) hb

end Md5.Proofs.Buffered
