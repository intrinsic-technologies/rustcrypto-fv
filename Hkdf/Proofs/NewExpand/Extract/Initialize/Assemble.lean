import Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble.Bytes
import Hkdf.Proofs.NewExpand.Extract.Frame

set_option autoImplicit false
namespace Hkdf.Proofs.NewExpand.Extract.Initialize
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble
open Hkdf.Proofs.Common.Machine

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem assemble [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (frame : Frame initial s boundary)
    (rip : s.RIP = 0x10fbbf)
    (ikmPtr : s.regValue .r15 = initial.regValue .rcx)
    (ikmLen : s.regValue .r14 = initial.regValue .r8)
    (innerHash : HashStateAt s (base initial)
      (compressBlocks initialHash
        (HMAC.xorPad (HMAC.keyBlock (salt.getD (RFC5869.defaultSalt .sha256))) 0x36)))
    (innerBlocks : loadBytes s.external (base initial + 32) 8 = .ok 1)
    (outerHash : HashStateAt s (base initial + 40)
      (compressBlocks initialHash
        (HMAC.xorPad (HMAC.keyBlock (salt.getD (RFC5869.defaultSalt .sha256))) 0x5c)))
    (outerBlocks : loadBytes s.external (base initial + 72) 8 = .ok 1) :
    ∃ t, Initialized initial t boundary salt := by
  obtain ⟨low, high⟩ := CallFrame.stack_bounds pre.call.stack
  have address (offset : Nat) (h : offset ≤ 456) :
      base initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (456-offset) := by
    apply BitVec.eq_sub_iff_add_eq.mpr
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show offset + (456-offset) = 456 by omega]
    exact BitVec.sub_add_cancel _ _
  have addressNat (offset : Nat) (h : offset ≤ 456) :
      (base initial + BitVec.ofNat 64 offset).toNat = (stackPtr initial).toNat - (456-offset) := by
    rw [address offset h]
    exact CallFrame.stack_sub_toNat pre.call.stack (by omega)
  have rspS : rspOf s = base initial := frame.rsp
  have readable (offset len : Nat) (ho : offset ≤ 456) (hl : len ≤ 464-offset) :
      MemReadable s (base initial + BitVec.ofNat 64 offset) len := by
    rw [address offset ho]
    exact CallFrame.stack_readable pre.call.stack frame.allocated (by omega) (by omega)
  have writable (offset : Nat) (ho : offset ≤ 456) (ha : offset % 8 = 0) :
      MemWritable s (base initial + BitVec.ofNat 64 offset) 8 := by
    rw [address offset ho]
    exact CallFrame.stack_writable8 pre.call.stack pre.call.stackAvoid frame.allocated (by omega) (by omega)
  have avoidsStack : (Stack.region initial 2264).Avoids InProgram :=
    fun a ha h ↦ pre.call.stackAvoid a ha (.inl h)
  have codeApart (offset len codeOffset codeLen : Nat) (ho : offset ≤ 456)
      (hl : len ≤ 464-offset) (hb : codeOffset + codeLen ≤ 115149) :
      RangeApart (base initial + BitVec.ofNat 64 offset) len
        (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
    rw [address offset ho]
    exact CallFrame.stack_codeApart pre.call.stack avoidsStack (by omega) (by omega) hb
  have layoutPre : LayoutPre s := by
    refine ⟨rip, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [rspS]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact readable _ _ (by decide) (by decide)
    · intro i hi
      rw [rspS]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact writable _ (by decide) (by decide)
    · rw [rspS, show base initial + 183 = _ from address 183 (by decide)]
      exact CallFrame.stack_writable1 pre.call.stack pre.call.stackAvoid frame.allocated (by decide)
    · intro i hi
      rw [rspS]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact codeApart _ _ 0xfbbf _ (by decide) (by decide) (by decide)
    · rw [rspS]
      exact codeApart 183 1 0xfbbf 161 (by decide) (by decide) (by decide)
  have outside := pre.call.outerBoundary
  obtain ⟨_, u, runU, readyU, _, effectU⟩ := layout_run boundary outside s
    (supportedMachine_readyToStep frame.machine)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xfbbf layoutBytes
      (by decide) (by decide +kernel)) layoutPre
  let written : MemoryRegion := ⟨(base initial + BitVec.ofNat 64 183).toNat, 161⟩
  have contains {offset len : Nat} (low : 183 ≤ offset) (high : offset+len ≤ 344)
      {a : BitVec 64} (ha : (Component.mem
        (base initial + BitVec.ofNat 64 offset) len).Covers a) :
      written.Contains a.toNat := by
    obtain ⟨j, hj, rfl⟩ := ha
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, addressNat (offset+j) (by omega)]
    change (base initial + BitVec.ofNat 64 183).toNat ≤ _ ∧
      _ < (base initial + BitVec.ofNat 64 183).toNat + 161
    rw [addressNat 183 (by decide)]
    constructor <;> omega
  have footprintU : WritesWithin (layoutEffect s).components #v[written] := by
    intro c hc a ha
    simp only [layoutEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals rw [rspS] at ha
    all_goals exact ⟨written, by simp, contains (by decide) (by decide) ha⟩
  have inStack {a : Nat} (ha : written.Contains a) :
      (Stack.region initial 2264).Contains a := by
    change (base initial + BitVec.ofNat 64 183).toNat ≤ a ∧
      a < (base initial + BitVec.ofNat 64 183).toNat + 161 at ha
    rw [addressNat 183 (by decide)] at ha
    change (Stack.region initial 2264).Contains a
    unfold MemoryRegion.Contains
    rw [Hkdf.Proofs.Common.Machine.stack_region_end]
    change (stackPtr initial).toNat - 2264 ≤ a ∧ a < (stackPtr initial).toNat + 8
    constructor <;> omega
  have avoids : ∀ region ∈ #v[Stack.region initial 2264],
      region.Avoids InProgram := by
    intro region hr a ha hin
    have eq : region = Stack.region initial 2264 := by simpa using hr
    exact avoidsStack a (eq ▸ ha) hin
  have runningU := frame.toRunning.of_agrees runU readyU effectU.agrees
    (by intro c hc a ha
        obtain ⟨region, hr, hin⟩ := footprintU c hc a ha
        have eq : region = written := by simpa using hr
        subst region
        exact ⟨Stack.region initial 2264, by simp, inStack hin⟩)
    avoids (by simp [layoutEffect, Effect.components, Write.component, Operand.component])
  have frameU := effectU.agrees.memoryWriteFrame footprintU
  have stores := effectU.writes
  simp only [layoutEffect, Write.AllHold, Operand.read, rspS] at stores
  have outputU : rdi.read u = base initial + BitVec.ofNat 64 184 := stores.2.2.1
  have inputU : rsi.read u = base initial + BitVec.ofNat 64 264 := stores.2.2.2.1
  have countU : (rcx.read u).toNat = 10 := by
    have count : rcx.read u = 10 := stores.2.1
    rw [count]; rfl
  have uReadable (offset len : Nat) (ho : offset ≤ 456) (hl : len ≤ 464-offset) :
      MemReadable u (base initial + BitVec.ofNat 64 offset) len := by
    rw [address offset ho]
    exact CallFrame.stack_readable pre.call.stack runningU.allocated (by omega) (by omega)
  have targetWrite : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable u
      (base initial + BitVec.ofNat 64 184) 80 := by
    refine ⟨uReadable 184 80 (by decide) (by decide), ?_⟩
    apply tables_of_not_reserved (by decide)
      (uReadable 184 80 (by decide) (by decide)).low
    intro i hi reserved
    apply pre.call.stackAvoid _ ?_ (.inr reserved)
    apply inStack
    apply contains (offset := 184) (len := 80) (by decide) (by decide)
    exact ⟨i, hi, rfl⟩
  have repPre : Hkdf.Proofs.Common.Instructions.RepMovsq.RepMovsqPre 0x10fc60 u := by
    apply Hkdf.Proofs.Common.Instructions.RepMovsq.pre_of_memory effectU.rip
      runningU.directionFlag.df countU
    · rw [inputU]
      exact uReadable 264 80 (by decide) (by decide)
    · rw [outputU]
      exact targetWrite
    · rw [inputU, outputU, addressNat 264 (by decide), addressNat 184 (by decide)]
      right
      omega
    · rw [outputU]
      exact codeApart 184 80 0xfc60 3 (by decide) (by decide) (by decide)
  have rep := Hkdf.Proofs.Common.Instructions.RepMovsq.rep_movsq_execution
    pre.call.stride readyU
    (programText_slice (programLoaded_codeIn runningU.loaded) 0xfc60
      [0xf3,0x48,0xa5] (by decide) (by decide +kernel)) repPre countU
    (boundary_ne_program outside (inProgram_of_textOffset 0xfc60 (by decide)))
    (boundary_ne_program outside (inProgram_of_textOffset 0xfc63 (by decide)))
  change Advances boundary 10 u (nextStates 10 u) ∧
    ReadyToStep (nextStates 10 u) ∧
    (repMovsqEffect 0x10fc60 u).Holds u (nextStates 10 u) ∧
      (∀ i < 80, (nextStates 10 u).external[rdi.read u + BitVec.ofNat 64 i]? =
        u.external[rsi.read u + BitVec.ofNat 64 i]?) at rep
  generalize endpoint : nextStates 10 u = t at rep
  obtain ⟨runT, readyT, effectT, copied⟩ := rep
  have footprintT : WritesWithin (repMovsqEffect 0x10fc60 u).components #v[written] := by
    intro c hc a ha
    simp only [repMovsqEffect_components, countU, outputU, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨written, by simp, contains (offset := 184) (len := 80)
      (by decide) (by decide) ha⟩
  have runningT := runningU.of_agrees runT readyT effectT.agrees
    (by intro c hc a ha
        obtain ⟨region, hr, hin⟩ := footprintT c hc a ha
        have eq : region = written := by simpa using hr
        subst region
        exact ⟨Stack.region initial 2264, by simp, inStack hin⟩)
    avoids (by simp [repMovsqEffect_components])
  have finalFrame := memoryWriteFrame_trans frameU
    (effectT.agrees.memoryWriteFrame footprintT)
  have agrees := effectU.agrees.trans effectT.agrees
  have componentsU : (layoutEffect s).components =
      [.reg 0, .reg 1, .reg 7, .reg 6, .mem (rspOf s + 183) 1,
       .mem (rspOf s + 336) 8, .mem (rspOf s + 328) 8, .mem (rspOf s + 320) 8,
       .mem (rspOf s + 304) 8, .mem (rspOf s + 312) 8, .mem (rspOf s + 264) 8,
       .mem (rspOf s + 272) 8, .mem (rspOf s + 280) 8, .mem (rspOf s + 288) 8,
       .mem (rspOf s + 296) 8, .rip] := by
    simp [layoutEffect, Effect.components, Write.component, Operand.component]
  have intact (offset len : Nat) (ho : offset + len ≤ 183 ∨ 344 ≤ offset)
      (bound : offset ≤ 456) : ∀ region ∈ #v[written],
      (⟨(base initial + BitVec.ofNat 64 offset).toNat, len⟩ : MemoryRegion).Disjoint region := by
    intro region hr a ha hb
    have eq : region = written := by simpa using hr
    subst region
    change (base initial + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (base initial + BitVec.ofNat 64 offset).toNat + len at ha
    change (base initial + BitVec.ofNat 64 183).toNat ≤ a ∧
      a < (base initial + BitVec.ofNat 64 183).toNat + 161 at hb
    rw [addressNat offset bound] at ha
    rw [addressNat 183 (by decide)] at hb
    omega
  have savedApart := intact 408 56 (by decide) (by decide)
  rw [address 408 (by decide)] at savedApart
  have preserved : Frame initial t boundary := by
    apply Frame.of_frame pre.call.stack frame runningT finalFrame
    · exact agrees.read (n := 64) (r := 4) (by simp [componentsU, repMovsqEffect_components])
    · exact agrees.mxcsr (by simp [componentsU, repMovsqEffect_components])
    · exact agrees.fcw (by simp [componentsU, repMovsqEffect_components])
    · exact fun region hr ↦ ⟨savedApart region hr, intact 80 8 (by decide) (by decide) region hr⟩
  have packed := packed_bytes effectU (by
    rw [rspS]; simpa only [BitVec.add_zero] using readable 0 80 (by decide) (by decide))
    (by rw [rspS]; exact uReadable 264 80 (by decide) (by decide))
  rw [rspS] at packed
  have moved (i : Nat) (hi : i < 80) : t.external[base initial + 184 + BitVec.ofNat 64 i]? =
      s.external[base initial + BitVec.ofNat 64 i]? := by
    have step := copied i hi
    rw [outputU, inputU] at step
    exact step.trans (packed i hi)
  have lengthU : u.external[base initial + BitVec.ofNat 64 183]? = some 0 := by
    have bytes := Bytes.of_memLoad (n := 8) (uReadable 183 1 (by decide) (by decide)).mem
    have word : memLoad u.external (base initial + BitVec.ofNat 64 183) 8 = 0 :=
      stores.2.2.2.2.1
    rw [word] at bytes
    simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl]
      using bytes 0 (by decide)
  have lengthT : t.external[base initial + 183]? = some 0 := by
    have same := effectT.agrees.byte (x := base initial + BitVec.ofNat 64 183) (by
      intro c hc ha
      simp only [repMovsqEffect_components, countU, outputU, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨j, hj, eq⟩ := ha
      exact OffsetsApart.ne (c₁ := 183) (len₁ := 1) (c₂ := 184) (len₂ := 80)
        (by unfold OffsetsApart; decide +kernel) (base initial)
        (i := 0) (by decide) hj (by decide) (by simpa using eq))
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using same.trans lengthU
  refine ⟨t, ⟨preserved, effectT.rip, ?_, ?_, ?_, hmac_of_packed innerHash innerBlocks outerHash outerBlocks moved lengthT⟩⟩
  · exact (agrees.read (n := 64) (r := 15) (by simp [componentsU, repMovsqEffect_components])).trans ikmPtr
  · exact (agrees.read (n := 64) (r := 14) (by simp [componentsU, repMovsqEffect_components])).trans ikmLen
  · exact (effectT.agrees.read (n := 64) (r := 0) (by simp [repMovsqEffect_components])).trans stores.1

end Hkdf.Proofs.NewExpand.Extract.Initialize
