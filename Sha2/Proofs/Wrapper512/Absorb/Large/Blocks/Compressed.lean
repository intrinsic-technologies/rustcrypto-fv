import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.State
import Sha2.Proofs.Wrapper512.Absorb.Large.Arithmetic
import Sha2.Proofs.Wrapper512.Absorb.Large.Memory
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Compression
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Setup
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Select

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper (prefixMessage prefixMessage_succ)
open Sha2.Proofs.Wrapper512.Absorb.Blocks

theorem restore_source [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Program.Input} (ctx : Context v initial inputs form)
    (input : Preserved v initial s form)
    (restores : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset true)
    (rip : s.RIP = v.pc (compressionOffset form v + 5) form) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (compressionOffset form v + 8) form ∧
      v.sourceValue form t =
        (.reg (BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read s ∧
      AgreesExcept [.reg 6, .rip] s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) := by
  let modrm : UInt8 := if form = .finalizeIntoReset true then 0xee else 0xf6
  have target : v.pc (compressionOffset form v + 5) form + 3 =
      v.pc (compressionOffset form v + 8) form := by
    exact Variant.pc_add v (compressionOffset form v + 5) 3 form
  have code : CodeIn (codeRange (v.pc (compressionOffset form v + 5) form)
      [0x4c,0x89,modrm]) s := by
    apply programText_slice (programLoaded_codeIn input.loaded)
      (v.textOffset form + (compressionOffset form v + 5))
    · cases v <;> rcases restores with rfl | rfl | rfl <;> decide +kernel
    · cases v <;> rcases restores with rfl | rfl | rfl <;> decide +kernel
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  obtain ⟨t,run,ready,effect⟩ :=
    (mov_r64_r64_effect_step (v.pc (compressionOffset form v + 5) form) 0x4c modrm
      (by simp [RexWPrefix]) (by rcases restores with rfl | rfl | rfl <;> simp [modrm, modrmMod])).advances
      (supportedMachine_readyToStep input.machine) code rip
      (by change v.pc (compressionOffset form v + 5) form + 3 ≠ _
          rw [target]
          apply boundary_ne_program outside
          apply inProgram_of_textOffset
          cases v <;> rcases restores with rfl | rfl | rfl <;> decide +kernel)
  have dstEq : gprNumber 0 (rexB (UInt8.toBitVec 0x4c)) (modrmRm modrm) = 6 := by
    rcases restores with rfl | rfl | rfl <;> decide +kernel
  have srcEq : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (modrmReg modrm) =
      BitVec.ofNat 5 (v.traversal form).lengthReg := by
    cases v <;> rcases restores with rfl | rfl | rfl <;> decide +kernel
  have dataEq : BitVec.ofNat 5 (v.traversal form).dataReg = 6 := by
    cases v <;> rcases restores with rfl | rfl | rfl <;> decide +kernel
  have frame : AgreesExcept [.reg 6,.rip] s t := by
    simpa only [movR64R64Effect_components, dstEq] using effect.agrees
  have preserved := preserved_of_agrees ctx input run ready frame
    (by simp [LocalWrites,Component.Covers]) (by simp) (by simp)
    (by simp) (by intro h; rcases restores with rfl | rfl | rfl <;> cases h)
  refine ⟨t,preserved,effect.rip.trans target,?_,frame,⟨_,run⟩⟩
  change (.reg (BitVec.ofNat 5 (v.traversal form).dataReg) : Operand 64).read t = _
  rw [dataEq]
  simpa only [movR64R64Effect, Write.AllHold, dstEq, srcEq] using effect.writes


macro "compressed_cases" f:ident v:ident " {" t:tacticSeq "}" : tactic => `(tactic|
  (cases ($f) with
   | slices => cases ($v) <;> ($t)
   | digest => contradiction
   | reset k =>
     have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := by omega
     rcases h with h | h | h <;> subst k <;> cases ($v) <;> ($t)
   | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> cases ($v) <;> ($t)))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem compress [Bindings] (body : Compression.BlockCorrect) {variant : Variant} {form : Form}
    {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context variant initial inputs form)
    (input : Input variant initial s inputs index consumed form)
    (rip : s.RIP = compressPC variant form)
    (count : s.regValue .rdx = BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/128))
    (nonDigest : form ≠ .digest) :
    ∃ t, CompressedSlice variant initial t inputs index consumed form ∧ t.RIP = tailPC variant form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  have start : compressPC variant form = variant.pc (Counter.addOffset true variant form) form := by
    unfold compressPC countPC
    change variant.pc (countOffset variant false form) form + BitVec.ofNat 64 9 = _
    rw [Variant.pc_add variant _ _ form]
    congr 1
    compressed_cases form variant { decide +kernel }
  obtain ⟨u, preservedU, ripU, blocksU, highU, frameU, ⟨fuelU,runU⟩,stackU⟩ :=
    Counter.add_count ctx input.toPreserved (rip.trans start) nonDigest
  have wordsU := hashState_of_bytes input.hashWords
    (counter_bytes (offset := BitVec.ofNat 64 form.activeMemory.hash) (len := 64) frameU
      (by compressed_cases form variant { unfold OffsetsApart <;> decide +kernel })
      (by compressed_cases form variant { unfold OffsetsApart <;> decide +kernel }) (by decide))
  let effect := fun x => Setup.effectAt (variant.pc (Setup.offset variant form) form)
    (Setup.displacement form) x (Setup.moveRex form) (Setup.moveModrm form)
  have setupRip : u.RIP = variant.pc (Setup.offset variant form) form := by
    rw [ripU]
    congr 1
    compressed_cases form variant { decide +kernel }
  obtain ⟨v, preservedV, setup, ⟨fuelV,runV⟩,stackV⟩ := register_block
    (effect := effect) ctx preservedU
    (Setup.run_form variant form (returnBoundary initial)
      (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 nonDigest)
    (Setup.code_form preservedU.loaded nonDigest) setupRip
    (by simp [effect, Setup.effectAt, Effect.components, Component.Covers])
    (by compressed_cases form variant { simp [effect, Setup.effectAt, Setup.moveRex, Setup.moveModrm, Effect.components] <;> decide +kernel })
    (by simp [effect, Setup.effectAt, Effect.components])
    (by intro h; exact (nonDigest h).elim)
    (by intro h; subst form; left; cases variant <;> simp [effect, Setup.effectAt, Setup.moveRex, Setup.moveModrm, Effect.components] <;> decide +kernel)
  have rdiV : v.regValue .rdi = hashPointer initial form form.activeMemory := by
    have h := setup.writes.1
    change v.regValue .rdi = rspOf u + (Setup.displacement form).signExtend 64 at h
    rw [h]
    change stackPtr u + _ = _
    rw [preservedU.rsp]
    simp only [hashPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    cases form <;> rfl
  have dataU : variant.sourceValue form u = variant.sourceValue form s := by
    exact frameU.read (n := 64) (by simp)
  have rsiV : v.regValue .rsi = (inputs[index]'input.remaining).address + BitVec.ofNat 64 consumed := by
    rw [← input.source, ← dataU]
    have w := setup.writes.2
    have a := setup.agrees
    compressed_cases form variant {
      first | exact w | exact a.read (n := 64) (r := 6) (by simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel) }
  have rdxV : v.regValue .rdx = BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/128) :=
    (setup.agrees.read (n := 64) (r := 2)
      (by compressed_cases form variant { simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel })).trans
      ((frameU.read (n := 64) (r := 2) (by simp)).trans count)
  have memoryV := setup.agrees.external (by simp [effect,Setup.effectAt,Effect.components,Component.Covers])
  have wordsV := hashState_of_bytes wordsU (fun i _ => by rw [memoryV])
  have callRip : v.RIP = variant.pc (compressionOffset form variant) form := by
    rw [setup.rip]
    change variant.pc (Setup.offset variant form) form + BitVec.ofNat 64 11 = _
    rw [Variant.pc_add variant _ _ form]
    congr 1
    compressed_cases form variant { decide +kernel }
  obtain ⟨t,preservedT,ripT,wordsT,abiT,frameT,⟨fuelT,runT⟩,stackT⟩ := compress_slice body ctx preservedV
    ⟨index,input.remaining⟩ (by
      change consumed+128*(((inputs[index]'input.remaining).bytes.size-consumed)/128) ≤
        (inputs[index]'input.remaining).bytes.size
      have := input.consumedBound
      omega) callRip rdiV rsiV rdxV wordsV
  have reserve : form.frameBytes + 8 + 416 - form.frameBytes = 424 := by omega
  rw [← reserve] at frameT
  have loadT (offset : Nat) (low : offset ≤ form.frameBytes) (high : 8 ≤ offset)
      (apart : form.activeMemory.hash + 8 ≤ offset ∨ offset + 64 ≤ form.activeMemory.hash) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad u.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    rw [← memoryV]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (frame_bytes (output := form.activeMemory.hash) (count := 64)
        (reserve := form.frameBytes + 8 + 416) ctx frameT (by compressed_cases form variant { decide +kernel })
        (by compressed_cases form variant { decide +kernel }) (by omega)
        (by compressed_cases form variant { decide +kernel }) low high apart i hi)
  have hashEq := finish_hash variant.initialHash (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  have counts := finish_counts (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  have initialLow : memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs index ++ (inputs[index]'input.remaining).bytes.extract 0 consumed).size/128) := input.blockCount
  have initialHigh : memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
      BitVec.ofNat 64 (((prefixMessage inputs index ++ (inputs[index]'input.remaining).bytes.extract 0 consumed).size/128)/2^64) := input.blockCountHigh
  have blocksV : memLoad v.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size/128) := by
    rw [memoryV,blocksU,initialLow,count,← BitVec.ofNat_add,
      prefixMessage_succ inputs index input.remaining,counts.1]
  have blocksT : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size/128) := by
    rw [loadT form.activeMemory.countLow
      (by compressed_cases form variant { decide +kernel }) (by compressed_cases form variant { decide +kernel })
      (by compressed_cases form variant { decide +kernel }), ← memoryV]
    exact blocksV
  have highV : memLoad v.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
      BitVec.ofNat 64 (((prefixMessage inputs (index+1)).size/128)/2^64) := by
    rw [memoryV,highU,initialHigh,initialLow,count,
      prefixMessage_succ inputs index input.remaining,counts.1]
    have carry (b : Bool) : BitVec.ofNat 64 b.toNat = if b then 1 else 0 := by cases b <;> rfl
    rw [carry]
    apply count_high_add
    have bound := (ctx.inputInMemory (⟨index,input.remaining⟩ : Fin inputs.size)).2.1
    change (inputs[index]'input.remaining).address.toNat + (inputs[index]'input.remaining).bytes.size < 2^32 at bound
    omega
  have highT : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
      BitVec.ofNat 64 (((prefixMessage inputs (index+1)).size/128)/2^64) := by
    rw [loadT form.activeMemory.countHigh
      (by compressed_cases form variant { decide +kernel }) (by compressed_cases form variant { decide +kernel })
      (by compressed_cases form variant { decide +kernel }), ← memoryV]
    exact highV
  have abiRead (r : BitVec 5) (hr : r ∈ ([3,5,12,13,14,15] : List (BitVec 5))) :
      (.reg r : Operand 64).read t = (.reg r : Operand 64).read v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact abiT.1 .rbx (by simp)
    · exact abiT.1 .rbp (by simp)
    · exact abiT.1 .r12 (by simp)
    · exact abiT.1 .r13 (by simp)
    · exact abiT.1 .r14 (by simp)
    · exact abiT.1 .r15 (by simp)
  have kept (r : BitVec 5) (hr : r ∈ ([3,5,12,13,14,15] : List (BitVec 5)))
      (hs : Component.reg r ∉ (effect u).components) :
      (.reg r : Operand 64).read t = (.reg r : Operand 64).read s :=
    (abiRead r hr).trans ((setup.agrees.read hs).trans (frameU.read (by simp)))
  have sourceCarrier (restores : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset true) :
      (.reg (BitVec.ofNat 5 (variant.traversal form).lengthReg) : Operand 64).read t =
        variant.sourceValue form s := by
    have h := setup.writes.2
    have hAbi := abiRead (BitVec.ofNat 5 (variant.traversal form).lengthReg)
      (by cases variant <;> rcases restores with rfl | rfl | rfl <;> decide +kernel)
    rw [hAbi]
    apply Eq.trans _ dataU
    cases variant <;> rcases restores with rfl | rfl | rfl <;> exact h
  obtain ⟨w, preservedW, ripW, sourceW, frameW,⟨fuelW,runW⟩⟩ :
      ∃ w, Preserved variant initial w form ∧ w.RIP = tailPC variant form ∧
        variant.sourceValue form w = variant.sourceValue form s ∧
        AgreesExcept [.reg 6,.rip] t w ∧
        (∃ fuel, Advances (returnBoundary initial) fuel t w) := by
    by_cases restores : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset true
    · obtain ⟨w,pw,rw,sw,fw,run⟩ := restore_source ctx preservedT restores ripT
      refine ⟨w,pw,?_,sw.trans (sourceCarrier restores),fw,run⟩
      rw [rw]
      compressed_cases form variant { first | contradiction | rfl }
    · refine ⟨t,preservedT,?_,?_,AgreesExcept.refl _ _,⟨0,by rfl⟩⟩
      · rw [ripT]
        compressed_cases form variant { first | contradiction | rfl }
      · apply kept
        · compressed_cases form variant { first | contradiction | decide +kernel }
        · compressed_cases form variant { simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel }
  have memoryW := frameW.external (by simp [Component.Covers])
  have keptW (r : BitVec 5) (hr : r ∈ ([3,5,12,13,14,15] : List (BitVec 5)))
      (hs : Component.reg r ∉ (effect u).components) :
      (.reg r : Operand 64).read w = (.reg r : Operand 64).read s := by
    apply (frameW.read (n := 64) (r := r) ?_).trans (kept r hr hs)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have loadW (offset : Nat) (low : offset ≤ form.frameBytes) (high : 8 ≤ offset)
      (apart : form.activeMemory.hash + 8 ≤ offset ∨ offset + 64 ≤ form.activeMemory.hash)
      (apartLow : OffsetsApart (-(BitVec.ofNat 64 form.activeMemory.countLow)) 8 (-(BitVec.ofNat 64 offset)) 8)
      (apartHigh : OffsetsApart (-(BitVec.ofNat 64 form.activeMemory.countHigh)) 8 (-(BitVec.ofNat 64 offset)) 8) :
      memLoad w.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    rw [memoryW, loadT offset low high apart]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (counter_bytes frameU apartLow apartHigh (by decide) i hi)
  refine ⟨w,⟨preservedW,input.remaining,input.consumedBound,input.aligned,?_,?_,?_,
    sourceW.trans input.source,?_,?_,?_,?_,?_,?_,?_⟩,ripW,
    ⟨_,((runU.trans runV).trans runT).trans runW⟩,
    memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans stackU stackV) stackT)
      (frameW.memoryWriteFrame (by simp [WritesWithin,Component.Covers]))⟩
  · rw [prefixMessage_succ inputs index input.remaining,← hashEq]
    exact hashState_of_bytes wordsT (fun i _ => by rw [memoryW]; rfl)
  · rw [memoryW]; exact blocksT
  · rw [memoryW]; exact highT
  · apply Eq.trans _ input.length
    apply keptW
    · compressed_cases form variant { decide +kernel }
    · compressed_cases form variant { simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel }
  · apply Eq.trans _ input.indexRegister
    apply keptW
    · compressed_cases form variant { decide +kernel }
    · compressed_cases form variant { simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel }
  · apply Eq.trans _ input.countRegister
    compressed_cases form variant {
      first
      | (apply keptW <;> simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel)
      | (apply loadW <;> (try unfold OffsetsApart) <;> decide +kernel) }
  · intro h; subst form
    rw [← input.outputSaved rfl]
    apply loadW <;> cases variant <;> (try unfold OffsetsApart) <;> decide +kernel
  · intro h; subst form
    exact (keptW 3 (by simp) (by cases variant <;> simp [effect, Setup.effectAt, Setup.moveRex, Setup.moveModrm, Effect.components] <;> decide +kernel)).trans (input.bufferRegister rfl)
  · have h3 : w.regValue .rbx = s.regValue .rbx := keptW 3 (by simp)
      (by compressed_cases form variant { simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel })
    have h12 : w.regValue .r12 = s.regValue .r12 := keptW 12 (by simp)
      (by compressed_cases form variant { simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel })
    compressed_cases form variant { first | (solve | simp [h3,h12]) | simpa [h3,h12] using input.memcpyTarget }
  · intro second h; subst form
    exact (keptW 3 (by simp) (by cases variant <;> cases second <;> simp [effect,Setup.effectAt,Setup.moveRex,Setup.moveModrm,Effect.components] <;> decide +kernel)).trans
      (input.activeBufferRegister second rfl)

theorem skip [Bindings] {variant : Variant} {form : Form} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (input : Input variant initial s inputs index consumed form)
    (zero : ((inputs[index]'input.remaining).bytes.size-consumed)/128 = 0) :
    CompressedSlice variant initial s inputs index consumed form := by
  have hashEq := finish_hash variant.initialHash (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  have counts := finish_counts (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  rw [zero,Nat.mul_zero,Nat.add_zero] at hashEq
  have empty : (inputs[index]'input.remaining).bytes.extract consumed consumed = ByteArray.empty := by simp
  rw [empty,compressBlocks_short _ _ (by decide)] at hashEq
  refine ⟨input.toPreserved,input.remaining,input.consumedBound,input.aligned,?_,?_,?_,
    input.source,input.length,input.indexRegister,input.countRegister,
    input.outputSaved,input.bufferRegister,?_,input.activeBufferRegister⟩
  · rw [prefixMessage_succ inputs index input.remaining,← hashEq]
    exact input.hashWords
  · rw [prefixMessage_succ inputs index input.remaining,counts.1,zero,Nat.add_zero]
    exact input.blockCount
  · rw [prefixMessage_succ inputs index input.remaining,counts.1,zero,Nat.add_zero]
    exact input.blockCountHigh

  · cases form with
    | slices | digest => trivial
    | reset k => exact input.memcpyTarget
    | finalizeIntoReset b => cases b <;> exact input.memcpyTarget
    | traitFinalizeIntoReset b => trivial

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
