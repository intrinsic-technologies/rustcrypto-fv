import Sha1.Proofs.MemoryRoutines.Contracts
import Sha1.Proofs.MemoryRoutines.Memset
import Sha1.Proofs.MemoryRoutines.Memcpy
import X86Proofs.Instructions.Call.Triple

namespace Sha1.Proofs.Buffered

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

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
    extends CallSitePre 0x103730 47 ret s where
  src : MemReadable s (rsi.read s) (MemoryRoutines.rdx.read s).toNat
  srcSlot : RangeApart (rsi.read s) (MemoryRoutines.rdx.read s).toNat (pushAddr s) 8
  disjoint : (rsi.read s).toNat + (MemoryRoutines.rdx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + (MemoryRoutines.rdx.read s).toNat ≤ (rsi.read s).toNat

abbrev MemsetSitePre := CallSitePre 0x1036e0 69

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
    (h : (callEffect target ret s).Holds s u) (htarget : target s = 0x103730) :
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
    (htarget : target s = 0x103730) (hentryNe : 0x103730 ≠ boundary.rip)
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
    (htarget : target s = 0x1036e0) (hentryNe : 0x1036e0 ≠ boundary.rip)
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
    (hout : boundary.rip.toNat < 0x1036e0 ∨ 0x103725 ≤ boundary.rip.toNat)
    {ret : BitVec 64} {target : RamState → BitVec 64} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : MemsetSitePre ret s)
    (htarget : target s = 0x1036e0) (hretNe : ret ≠ boundary.rip) :
    ∃ t, MemsetSiteResult boundary ret s t := by
  have hentryNe : (0x1036e0 : BitVec 64) ≠ boundary.rip := by
    intro he
    have hn := congrArg BitVec.toNat he
    change 0x1036e0 = boundary.rip.toNat at hn
    omega
  exact memset_call_of_advance hstep hready hcode hbytes hpre hp htarget hentryNe hretNe
    (MemoryRoutines.memset_advances hstride boundary hout)

theorem memcpy_call [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary}
    (hout : boundary.rip.toNat < 0x103730 ∨ 0x10375f ≤ boundary.rip.toNat)
    {ret : BitVec 64} {target : RamState → BitVec 64} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : MemcpySitePre ret s)
    (htarget : target s = 0x103730) (hretNe : ret ≠ boundary.rip) :
    ∃ t, MemcpySiteResult boundary ret s t := by
  have hentryNe : (0x103730 : BitVec 64) ≠ boundary.rip := by
    intro he
    have hn := congrArg BitVec.toNat he
    change 0x103730 = boundary.rip.toNat at hn
    omega
  exact memcpy_call_of_advance hstep hready hcode hbytes hpre hp htarget hentryNe hretNe
    (MemoryRoutines.memcpy_advances hstride boundary hout)

end Sha1.Proofs.Buffered
