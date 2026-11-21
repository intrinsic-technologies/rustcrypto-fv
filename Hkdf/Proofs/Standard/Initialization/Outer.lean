import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Standard.Initialization.Inner

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

theorem outer_pre [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : OuterReady initial s salt) :
    OuterPre s := by
  refine ⟨state.rip, ?_, ?_⟩
  · intro offset member
    rw [Standard.stack_address state.rsp (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals
      exact CallFrame.stack_writable8 ctx.call.stack
        (ctx.call.stackSeparation.2 _ (by simp)).2 state.allocated (by decide) (by decide)
  · intro offset member
    rw [Standard.stack_address state.rsp (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals
      exact Standard.stack_codeApart ctx (codeOffset := 0x152e)
        (by decide) (by decide) (by decide)

theorem outer_hash [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (ready : ReadyToStep s)
    (state : OuterReady initial s salt) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      CompressedPads initial t salt := by
  obtain ⟨stageFuel, u, stageRun, readyU, _, effect⟩ :=
    outer_stage_run (returnBoundary initial) (Standard.returnBoundary_valid ctx).2.2
      s ready (programText_slice (programLoaded_codeIn state.loaded) 0x152e outerBytes
        (by decide) (by decide +kernel)) (outer_pre ctx state)
  have writes : WritesWithin (outerEffect s).components (innerWriteRegions initial 40 504) := by
    intro c hc a ha
    simp only [outerEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨⟨(stackPtr initial - BitVec.ofNat 64 504).toNat, 40⟩,
      by simp [innerWriteRegions], ?_⟩
    all_goals
      exact hash_output_memory (hashBytes := 40) ctx state.toPreserved
        (by decide) (by decide) (by decide) ha
  have stageFrame := effect.agrees.memoryWriteFrame writes
  have runningU := state.toRunning.of_agrees stageRun readyU effect.agrees
    (by intro c hc a ha
        obtain ⟨region, member, contains⟩ := writes c hc a ha
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          hash_write_regions_within (hashOffset := 504) (hashBytes := 40) ctx (by decide)
            region member a.toNat contains⟩)
    (by intro region member a contains inside
        exact (ctx.call.stackSeparation.2 region (by simpa using member)).2 a contains (.inl inside))
    (by simp [outerEffect, Effect.components, Write.component, Operand.component])
  have rspU : u.regValue .rsp = frameBase initial :=
    (effect.agrees.read (n := 64) (r := 4)
      (by simp [outerEffect, Effect.components, Write.component, Operand.component])).trans state.rsp
  have stateU := inner_preserved_of_frame ctx state.toPreserved runningU stageFrame rspU
  have stores := effect.writes
  simp only [outerEffect, Write.AllHold] at stores
  have outputU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 504 := by
    have value : (Operand.reg 7 : Operand 64).read u = rspOf s + BitVec.ofNat 64 16 :=
      stores.2.2.2.2.2.1
    rw [Standard.stack_address state.rsp (offset := 16) (by decide)] at value
    exact value
  have inputU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400 := by
    have value : (Operand.reg 6 : Operand 64).read u = rspOf s + BitVec.ofNat 64 120 :=
      stores.2.2.2.2.2.2.1
    rw [Standard.stack_address state.rsp (offset := 120) (by decide)] at value
    exact value
  have countU : u.regValue .rdx = BitVec.ofNat 64 1 := stores.2.2.2.2.2.2.2
  have address (offset : Nat) (bound : offset ≤ 520) :
      frameBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520-offset) := by
    have addr := Standard.stack_address state.rsp (offset := offset) bound
    rw [show rspOf s = frameBase initial from state.rsp] at addr
    exact addr
  have blockAddress : hmacBase initial = stackPtr initial - BitVec.ofNat 64 400 :=
    address 120 (by decide)
  have blockU := inner_hasBytes_of_frame ctx stageFrame (offset := 400) (len := 64)
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [blockAddress] using state.block)
  have packed : ∀ j < 4, memLoad u.external
      (stackPtr initial - BitVec.ofNat 64 504 + BitVec.ofNat 64 (8*j)) 64 = ivWords[j]! := by
    intro j hj
    rw [← Standard.stack_address state.rsp (offset := 16) (by decide),
      BitVec.add_assoc, ← BitVec.ofNat_add]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · have word := stores.2.2.2.1
      change memLoad u.external _ 64 = _ at word
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        using word.trans state.ivRegisters.2.2.2
    · have word := stores.2.2.1
      change memLoad u.external _ 64 = _ at word
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        using word.trans state.ivRegisters.2.2.1
    · have word := stores.2.1
      change memLoad u.external _ 64 = _ at word
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        using word.trans state.ivRegisters.2.1
    · have word := stores.1
      change memLoad u.external _ 64 = _ at word
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        using word.trans state.ivRegisters.1
  have hashU : HashStateAt u (stackPtr initial - BitVec.ofNat 64 504)
      Hkdf.Proofs.NIST.SHA256.initialHash :=
    Key.Hash.Initialize.hashStateAt_initialHash_of_packedWords
      (Standard.stack_readable ctx stateU.toState (by decide) (by decide)) packed
  obtain ⟨v, callRun, readyV, runningV, callEffect, callFrame, rspV, retV⟩ :=
    hash_call ctx stateU readyU effect.rip
      (call_rel32_effect_step 0x10155a 0x8061 (by decide))
      (programText_slice (programLoaded_codeIn stateU.loaded) 0x155a _
        (by decide) (by decide +kernel))
      (Standard.stack_codeApart ctx (codeOffset := 0x155a)
        (by decide) (by decide) (by decide))
  have inputV : v.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400 :=
    (callEffect.agrees.read (n := 64) (r := 6)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans inputU
  have outputV : v.regValue .rdi = stackPtr initial - BitVec.ofNat 64 504 :=
    (callEffect.agrees.read (n := 64) (r := 7)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans outputU
  have countV : v.regValue .rdx = BitVec.ofNat 64 1 :=
    (callEffect.agrees.read (n := 64) (r := 2)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans countU
  have blockV := inner_hasBytes_of_frame ctx callFrame (offset := 400) (len := 64)
    (by decide) (by decide) (by decide) (by decide) blockU
  have hashV := Hkdf.Proofs.Wrapper.hashState_of_bytes hashU
    (inner_frame_agrees ctx callFrame (offset := 504) (len := 32)
      (by decide) (by decide) (by decide) (by decide))
  have pre := hash_compression_pre ctx (by decide) (by decide) runningV callEffect.rip
    rspV outputV inputV (by rw [retV]; exact inProgram_of_textOffset 0x155f (by decide))
    countV blockV hashV
  obtain ⟨t, result⟩ := Common.SHA256.compression_correct pre
  have resultFrame := hash_compression_frame ctx (by decide) rspV outputV result.frame
  have laterFrame := memoryWriteFrame_trans (hash_zero_frame callFrame) resultFrame
  have fullFrame := memoryWriteFrame_trans stageFrame
    (inner_frame_mono laterFrame (by decide : 32 ≤ 40))
  have runningT := runningV.of_callee result.toCalleeResult
    (by intro region member a contains
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          stack_layout_within ctx.call.stack (hashCallLayout 504 (by decide))
            rspV outputV region member a contains⟩)
  have rspT : t.regValue .rsp = frameBase initial := by rw [result.rsp, retV]
  have stateT := inner_preserved_of_frame ctx state.toPreserved runningT fullFrame rspT
  have hashT : HashStateAt t (frameBase initial + 16)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
        (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x5c)) := by
    change HashStateAt t (frameBase initial + BitVec.ofNat 64 16) _
    have value := result.hashWords
    rw [outputV] at value
    rw [address 16 (by decide)]
    exact value
  have countWordU : memLoad u.external (stackPtr initial - BitVec.ofNat 64 472) 64 = 1 := by
    have word := stores.2.2.2.2.1
    change memLoad u.external (rspOf s + BitVec.ofNat 64 48) 64 = 1 at word
    rw [Standard.stack_address state.rsp (offset := 48) (by decide)] at word
    exact word
  have countWordT := (CallFrame.agrees_memLoad
    (inner_frame_agrees ctx laterFrame (offset := 472) (len := 8)
      (by decide) (by decide) (by decide) (by decide))).trans countWordU
  have countT : loadBytes t.external (frameBase initial + 48) 8 = .ok 1 := by
    change loadBytes t.external (frameBase initial + BitVec.ofNat 64 48) 8 = .ok 1
    have bytes := Bytes.of_memLoad (n := 64)
      (Standard.stack_readable ctx stateT.toState (offset := 472) (len := 8)
        (by decide) (by decide)).mem
    rw [countWordT] at bytes
    rw [address 48 (by decide)]
    exact bytes.loadBytes64
  have innerHash := Hkdf.Proofs.Wrapper.hashState_of_bytes state.innerHash
    (by change (Component.mem (frameBase initial + BitVec.ofNat 64 56) 32).Agrees s t
        rw [address 56 (by decide)]
        exact inner_frame_agrees ctx fullFrame (by decide) (by decide) (by decide) (by decide))
  have innerBlocks : loadBytes t.external (frameBase initial + 88) 8 = .ok 1 := by
    apply Eq.trans _ state.innerBlocks
    apply CallFrame.agrees_loadBytes
    change (Component.mem (frameBase initial + BitVec.ofNat 64 88) 8).Agrees s t
    rw [address 88 (by decide)]
    exact inner_frame_agrees ctx fullFrame (by decide) (by decide) (by decide) (by decide)
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨stageFuel+1+fuel, t, (stageRun.trans callRun).trans execution,
    supportedMachine_readyToStep result.machine, ?_⟩
  refine ⟨stateT, ?_, innerHash, innerBlocks, hashT, countT⟩
  rw [result.rip, retV]
  rfl

end Hkdf.Proofs.Standard.Initialization
