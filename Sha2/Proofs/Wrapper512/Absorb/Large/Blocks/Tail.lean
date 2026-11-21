import Sha2.Proofs.Common.Machine.MemoryFrame
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.TailRegisters
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.TailSetup
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Arithmetic
import Sha2.Proofs.Wrapper512.Absorb.Blocks.Mathematics
import Sha2.Proofs.Wrapper512.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper512.Absorb.Blocks

def tailEndPC (v : Variant) (form : Form) : BitVec 64 :=
  v.pc (Copy.Site.tail.relativeOffset form v + Copy.Site.tail.size v form) form


theorem tailEndPC_slices (v : Variant) : tailEndPC v .slices = v.pc 0x1fc := rfl


theorem tailEndPC_trait (v : Variant) (second : Bool) :
    tailEndPC v (.traitFinalizeIntoReset second) =
      v.pc ((v.traversal (.traitFinalizeIntoReset second)).exit - 24)
        (.traitFinalizeIntoReset second) := by
  cases second <;> cases v <;> decide +kernel


set_option maxHeartbeats 800000 in
theorem tail_copied [Bindings] {variant : Variant} {form : Form}
    {initial s w t : RamState} {inputs : Array Program.Input} {index consumed : Nat}
    (ctx : Context variant initial inputs form)
    (input : CompressedSlice variant initial s inputs index consumed form)
    (copied : Copy.Result variant initial w t (inputs[index]'input.remaining) .tail
      (consumed+128*(((inputs[index]'input.remaining).bytes.size-consumed)/128)) 0
      (((inputs[index]'input.remaining).bytes.size-consumed)%128) form)
    (words : HashStateAt w (hashPointer initial form form.activeMemory)
      (compressBlocks variant.initialHash (Wrapper.prefixMessage inputs (index+1))))
    (blocks : memLoad w.external (blockCountPointer initial form form.activeMemory) 64 =
      BitVec.ofNat 64 ((Wrapper.prefixMessage inputs (index+1)).size/128))
    (high : memLoad w.external (blockCountHighPointer initial form form.activeMemory) 64 =
      BitVec.ofNat 64 (((Wrapper.prefixMessage inputs (index+1)).size/128)/2^64))
    (tail : w.external[tailLengthPointer initial form form.activeMemory]? =
      some (UInt8.ofNat (((inputs[index]'input.remaining).bytes.size-consumed)%128))) :
    Buffered variant initial t (Wrapper.prefixMessage inputs (index+1)) form form.activeMemory := by
  let bytes := (inputs[index]'input.remaining).bytes
  let count := bytes.size-consumed
  have countSmall : count%128 < 128 := Nat.mod_lt _ (by decide)
  have bounds : form.activeMemory.hash ≤ form.frameBytes ∧ 64 ≤ form.activeMemory.hash ∧
      form.activeMemory.hash + 127 ≤ form.activeMemory.buffer ∧
      form.activeMemory.countLow ≤ form.frameBytes ∧ 8 ≤ form.activeMemory.countLow ∧
      form.activeMemory.countLow + 127 ≤ form.activeMemory.buffer ∧
      form.activeMemory.countHigh ≤ form.frameBytes ∧ 8 ≤ form.activeMemory.countHigh ∧
      form.activeMemory.countHigh + 127 ≤ form.activeMemory.buffer ∧
      form.activeMemory.tail ≤ form.frameBytes ∧ 1 ≤ form.activeMemory.tail ∧
      form.activeMemory.tail + 127 ≤ form.activeMemory.buffer := by
    cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes,
      ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  rcases bounds with ⟨hashLow,hashHigh,hashApart,countLow,countHigh,countApart,highLow,highHigh,highApart,tailLow,tailHigh,tailApart⟩
  have sameByte (off len : Nat) (low : off ≤ form.frameBytes) (high : len ≤ off)
      (apart : off + 127 ≤ form.activeMemory.buffer) (i : Nat) (hi : i < len) :
      t.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      w.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
    exact copied.bytes_unchanged ctx (by change 0 + count%128 ≤ 128; omega) low high
      (.inr (by change off+count%128 ≤ form.activeMemory.buffer-0; omega)) i hi
  have wordsT : HashStateAt t (hashPointer initial form form.activeMemory)
      (compressBlocks variant.initialHash (Wrapper.prefixMessage inputs (index+1))) := by
    apply hashState_of_bytes words
    intro i hi
    exact sameByte _ _ hashLow hashHigh hashApart i hi
  have blocksT : memLoad t.external (blockCountPointer initial form form.activeMemory) 64 =
      BitVec.ofNat 64 ((Wrapper.prefixMessage inputs (index+1)).size/128) := by
    rw [← blocks]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (sameByte _ _ countLow countHigh countApart i hi)
  have highT : memLoad t.external (blockCountHighPointer initial form form.activeMemory) 64 =
      BitVec.ofNat 64 (((Wrapper.prefixMessage inputs (index+1)).size/128)/2^64) := by
    rw [← high]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (sameByte _ _ highLow highHigh highApart i hi)
  have tailT : t.external[tailLengthPointer initial form form.activeMemory]? =
      some (UInt8.ofNat (count%128)) := by
    have kept := sameByte _ 1 tailLow
      tailHigh tailApart 0 (by decide)
    simp only [BitVec.add_zero] at kept
    exact kept.trans tail
  have endEq : consumed+128*(count/128)+count%128 = bytes.size := by
    have := input.consumedBound
    change consumed ≤ bytes.size at this
    dsimp only [count]
    omega
  have counts := finish_counts (Wrapper.prefixMessage inputs index) bytes input.consumedBound input.aligned
  have sizeEq : (Wrapper.prefixMessage inputs (index+1)).size%128 = count%128 := by
    rw [Wrapper.prefixMessage_succ inputs index input.remaining]
    exact counts.2
  have tailEq : (Wrapper.prefixMessage inputs (index+1)).extract
      (128*((Wrapper.prefixMessage inputs (index+1)).size/128)) (Wrapper.prefixMessage inputs (index+1)).size =
      bytes.extract (consumed+128*(count/128)) bytes.size := by
    change remainderBytes (Wrapper.prefixMessage inputs (index+1)) = _
    rw [Wrapper.prefixMessage_succ inputs index input.remaining]
    exact finish_tail (Wrapper.prefixMessage inputs index) bytes input.consumedBound input.aligned
  refine ⟨copied.preserved,wordsT,?_,?_,blocksT,highT⟩
  · dsimp only [tailRegion,tailData,bufferPointer]
    rw [sizeEq,tailEq]
    have result := copied.bytes
    change (⟨(stackPtr initial-BitVec.ofNat 64 form.activeMemory.buffer+0#64).toNat,count%128⟩ : MemoryRegion).HasBytes t.external
      (bytes.extract (consumed+128*(count/128)) (consumed+128*(count/128)+count%128)) at result
    rw [BitVec.add_zero,endEq] at result
    exact result
  · rw [sizeEq]
    exact tailT

theorem tail_control_registers (v : Variant) (form : Form) :
    let i := BitVec.ofNat 5 (v.traversal form).indexReg
    let c := BitVec.ofNat 5 ((v.traversal form).countReg.getD 0)
    i ∈ ([14,15] : List (BitVec 5)) ∧ i ≠ v.restRegister form ∧
      i ≠ BitVec.ofNat 5 (v.traversal form).dataReg ∧ i ≠ tailSetupTargetRegister form ∧
    ((v.traversal form).countReg.isSome = true →
      c ∈ ([12,15] : List (BitVec 5)) ∧ c ≠ v.restRegister form ∧
      c ≠ BitVec.ofNat 5 (v.traversal form).dataReg ∧ c ≠ tailSetupTargetRegister form) := by
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    revert second; cases v <;> decide +kernel

theorem tail_count_slot_bounds (v : Variant) (form : Form) :
    (v.traversal form).countReg.isNone = true →
    let off := (v.traversal form).countSlot.getD 0
    off ≤ form.frameBytes ∧ 8 ≤ off ∧
    (form.activeMemory.buffer + 8 ≤ off ∨ off + 127 ≤ form.activeMemory.buffer) ∧
    OffsetsApart (-BitVec.ofNat 64 form.activeMemory.tail) 1 (-BitVec.ofNat 64 off) 8 := by
  unfold OffsetsApart
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    revert second; cases v <;> decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem tail [Bindings] {variant : Variant} {form : Form} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context variant initial inputs form)
    (input : CompressedSlice variant initial s inputs index consumed form)
    (rip : s.RIP = variant.pc (tailOffset variant form) form)
    (hd : form ≠ .digest) :
    ∃ t, Absorb.Blocks.Result variant initial t inputs index form ∧
      t.RIP = tailEndPC variant form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  let bytes := (inputs[index]'input.remaining).bytes
  let count := bytes.size-consumed
  have countBound : count < 2^32 := by
    have h := ctx.inputInMemory (⟨index,input.remaining⟩ : Fin inputs.size)
    have hb := h.2.1
    change (inputs[index]'input.remaining).address.toNat + bytes.size < 2^32 at hb
    dsimp only [count]
    omega
  have lengthNat : ((.reg (variant.restRegister form) : Operand 64).read s).toNat = count := by
    rw [input.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by change count < 2^64; omega)]
  have countSmall : count%128 < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨u,preservedU,registers,⟨fuelU,runU⟩,stackU⟩ := register_block
    (pc := variant.pc (tailOffset variant form) form)
    (bytes := TailRegisters.bytesAt (tailRegisterEncoding form))
    (effect := TailRegisters.effectAt (variant.pc (tailOffset variant form) form) (tailRegisterEncoding form))
    ctx input.toPreserved
    (TailRegisters.run_at _ _ (returnBoundary initial) (by
      intro n hn
      rw [Variant.pc_add variant _ _ form]
      apply boundary_ne_program ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
      apply inProgram_of_textOffset
      have := tailRegister_bounds variant form
      omega))
    (tailRegister_code input.loaded hd) rip
    (by simp [TailRegisters.effectAt,Effect.components,Component.Covers])
    (by
      rw [tailRegister_effect variant form]
      have facts := tailRegister_keeps_rsp variant form
      simpa [Effect.components, eq_comm] using facts)
    (by simp [TailRegisters.effectAt,Effect.components])
    (by intro h; exact (hd h).elim)
    (fun h => .inr (input.outputSaved h))
  have memoryU := registers.agrees.external
    (by simp [TailRegisters.effectAt,Effect.components,Component.Covers])
  rw [tailRegister_effect variant form] at registers
  have sourceU : variant.sourceValue form u =
      (inputs[index]'input.remaining).address + BitVec.ofNat 64 (consumed+128*(count/128)) := by
    have value : variant.sourceValue form u = variant.sourceValue form s +
        (0x7fffffffffffff80 &&& (.reg (variant.restRegister form) : Operand 64).read s) := registers.writes.2.2.2
    rw [value,full_length _ (by rw [lengthNat]; omega),lengthNat,input.source,
      BitVec.ofNat_add,BitVec.add_assoc]
  have lengthU : (.reg (variant.restRegister form) : Operand 64).read u = BitVec.ofNat 64 (count%128) :=
    registers.writes.2.2.1.trans ((tail_length _).trans (by rw [lengthNat]))
  have lengthReg : lengthRegister true form = variant.restRegister form := by
    cases form with
    | slices | digest => rfl
    | reset stage =>
      have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases cases with rfl | rfl | rfl <;> rfl
    | finalizeIntoReset second => cases variant <;> rfl
    | traitFinalizeIntoReset second => rfl
  obtain ⟨v,preservedV,ripV,byteV,frameV,runV⟩ := store_length_local ctx preservedU true
    (registers.rip.trans (tail_register_end variant form hd)) hd
  have tailV : v.external[tailLengthPointer initial form form.activeMemory]? =
      some (UInt8.ofNat (count%128)) := by
    rw [lengthReg] at byteV
    change v.external[tailLengthPointer initial form form.activeMemory]? =
      some (UInt8.ofNat (((.reg (variant.restRegister form) : Operand 64).read u).setWidth 8).toNat) at byteV
    rw [lengthU] at byteV
    simpa only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : count%128 < 2^64),
      Nat.mod_eq_of_lt (by omega : count%128 < 2^8)] using byteV
  have stackV : MemoryWriteFrame u v #v[Stack.region initial (variant.routine form).minStackBytes] := by
    apply frameV.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, stackRegion_contains_sub ctx.stack.2.2.1
        (by cases variant <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
        (by cases variant <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) ha⟩
    · exact ha.elim
  have sourceV := (frameV.read (n := 64)
    (r := BitVec.ofNat 5 (variant.traversal form).dataReg) (by simp)).trans sourceU
  have lengthV := (frameV.read (n := 64)
    (r := variant.restRegister form) (by simp)).trans lengthU
  have sameByteV (off len : Nat)
      (apart : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.tail) 1 (-BitVec.ofNat 64 off) len)
      (small : 1+len < 2^64) (i : Nat) (hi : i < len) :
      v.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      s.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
    exact (bytes_of_mem_frame frameV (by simp [Component.Covers]) apart small i hi).trans
      (by rw [memoryU])
  have wordsV : HashStateAt v (hashPointer initial form form.activeMemory)
      (compressBlocks variant.initialHash (Wrapper.prefixMessage inputs (index+1))) := by
    apply hashState_of_bytes input.hashWords
    intro i hi
    exact sameByteV _ _ (by
      cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory,
        ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]
      all_goals unfold OffsetsApart; decide +kernel) (by decide) i hi
  have blocksV : memLoad v.external (blockCountPointer initial form form.activeMemory) 64 =
      BitVec.ofNat 64 ((Wrapper.prefixMessage inputs (index+1)).size/128) := by
    rw [← input.blockCount]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (sameByteV _ _ (by
        cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory,
          ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]
        all_goals unfold OffsetsApart; decide +kernel) (by decide) i hi)
  have highV : memLoad v.external (blockCountHighPointer initial form form.activeMemory) 64 =
      BitVec.ofNat 64 (((Wrapper.prefixMessage inputs (index+1)).size/128)/2^64) := by
    rw [← input.blockCountHigh]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (sameByteV _ _ (by
        cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory,
          ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]
        all_goals unfold OffsetsApart; decide +kernel) (by decide) i hi)
  have loadV (off : Nat)
      (apart : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.tail) 1 (-BitVec.ofNat 64 off) 8) :
      memLoad v.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (sameByteV off 8 apart (by decide) i hi)
  have outputSavedV : form = .traitFinalizeIntoReset false →
      memLoad v.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by
    intro h
    exact (loadV form.outputSlot (by subst form; unfold OffsetsApart; decide +kernel)).trans
      (input.outputSaved h)
  have keptV (r : BitVec 5) (h0 : r ≠ 0) (h1 : r ≠ 1)
      (hr : r ≠ variant.restRegister form)
      (hs : r ≠ BitVec.ofNat 5 (variant.traversal form).dataReg) :
      (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read s := by
    apply (frameV.read (n := 64) (r := r) (by simp)).trans
    apply registers.agrees.read
    change Component.reg r ∉ [.reg 0, .reg 1, .reg (variant.restRegister form),
      .reg (BitVec.ofNat 5 (variant.traversal form).dataReg), .flags, .rip]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
      reduceCtorEq, not_or]
    exact ⟨h0,h1,hr,hs⟩
  have bufferV : form = .reset 1 → v.regValue .rbx = bufferPointer initial form := by
    intro h
    subst form
    exact (keptV 3 (by decide) (by decide) (by cases variant <;> decide)
      (by cases variant <;> decide)).trans (input.bufferRegister rfl)
  have activeV : ∀ second, form = .traitFinalizeIntoReset second →
      v.regValue .rbx = bufferPointer initial form form.activeMemory := by
    intro second h
    subst form
    exact (keptV 3 (by decide) (by decide) (by cases second <;> cases variant <;> decide)
      (by cases second <;> cases variant <;> decide)).trans (input.activeBufferRegister second rfl)
  have targetV : ∀ r, Copy.Site.tail.register variant form = some r →
      form ≠ .traitFinalizeIntoReset false → form ≠ .traitFinalizeIntoReset true →
      (Operand.reg r : Operand 64).read v = 0x10dd60 := by
    intro r hr hf ht
    cases form with
    | slices | digest => simp [Copy.Site.register] at hr
    | traitFinalizeIntoReset second => cases second <;> contradiction
    | reset stage =>
      have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases cases with rfl | rfl | rfl
      all_goals simp only [Copy.Site.register] at hr
      all_goals first | contradiction | skip
      have eq : r = 3 := by simpa using hr.symm
      subst r
      exact (keptV 3 (by decide) (by decide) (by cases variant <;> decide)
        (by cases variant <;> decide)).trans (input.memcpyTarget rfl)
    | finalizeIntoReset second =>
      cases second
      · change (none : Option (BitVec 5)) = some r at hr
        contradiction
      · cases variant <;> simp [Copy.Site.register] at hr
        all_goals subst r
        all_goals exact (keptV _ (by decide) (by decide) (by decide) (by decide)).trans input.memcpyTarget
  obtain ⟨w,preservedW,ripW,destinationW,sourceW,lengthW,targetW,frameW,⟨fuelW,runW⟩,stackW⟩ :=
    tail_setup ctx preservedV (ripV.trans (tail_length_end variant form hd)) hd
      outputSavedV bufferV activeV targetV
  have memoryW := frameW.external (by simp [tailSetupComponents,Component.Covers])
  have endEq : consumed+128*(count/128)+count%128 = bytes.size := by
    have := input.consumedBound
    change consumed ≤ bytes.size at this
    dsimp only [count]
    omega
  obtain ⟨t,copied⟩ := Copy.copy ctx preservedW .tail ⟨index,input.remaining⟩
    (offset := consumed+128*(count/128)) (position := 0) (count := count%128)
    (by change consumed+128*(count/128)+count%128 ≤ bytes.size; omega)
    (by omega) ripW (by simpa only [bufferPointer, BitVec.add_zero] using destinationW)
    (sourceW.trans sourceV) (lengthW.trans lengthV) targetW
  have bufferedT := tail_copied ctx input copied
    (hashState_of_bytes wordsV (fun i _ => by rw [memoryW]))
    (by rw [memoryW]; exact blocksV) (by rw [memoryW]; exact highV)
    (by rw [memoryW]; exact tailV)
  have keptW (r : BitVec 5) (h2 : r ≠ 2) (h6 : r ≠ 6) (h7 : r ≠ 7)
      (ht : r ≠ tailSetupTargetRegister form) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read v := by
    apply frameW.read
    simp only [tailSetupComponents, List.mem_cons, List.not_mem_nil, or_false,
      Component.reg.injEq, reduceCtorEq, false_or, not_or]
    exact ⟨h2,h6,h7,ht⟩
  have controls := tail_control_registers variant form
  rcases controls with ⟨indexMember,indexRest,indexSource,indexTarget,countFacts⟩
  have indexKept : variant.indexValue form t = variant.indexValue form s := by
    let r := BitVec.ofNat 5 (variant.traversal form).indexReg
    have nonzero : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 6 ∧ r ≠ 7 := by
      change r ∈ ([14,15] : List (BitVec 5)) at indexMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at indexMember
      rcases indexMember with h | h <;> rw [h] <;> decide
    have abi : (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read w := by
      change r ∈ ([14,15] : List (BitVec 5)) at indexMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at indexMember
      rcases indexMember with h | h
      · rw [h]; exact copied.abi.1 .r14 (by simp)
      · rw [h]; exact copied.abi.1 .r15 (by simp)
    exact abi.trans ((keptW r nonzero.2.2.1 nonzero.2.2.2.1 nonzero.2.2.2.2 indexTarget).trans
      (keptV r nonzero.1 nonzero.2.1 indexRest indexSource))
  have sameLoadT (off : Nat) (low : off ≤ form.frameBytes) (high : 8 ≤ off)
      (apart : form.activeMemory.buffer + 8 ≤ off ∨ off + 127 ≤ form.activeMemory.buffer) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad v.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    apply (copied.bytes_unchanged ctx (by omega) low high ?_ i hi).trans
    · rw [memoryW]; rfl
    · rcases apart with h | h
      · exact .inl (by simpa only [Nat.sub_zero] using h)
      · exact .inr (by change off+count%128 ≤ form.activeMemory.buffer-0; omega)
  have countKept : variant.countValue form initial t = variant.countValue form initial s := by
    unfold Variant.countValue
    split
    · rename_i r hr
      have facts := countFacts (by rw [hr]; rfl)
      simp only [hr, Option.getD_some] at facts
      rcases facts with ⟨member,rest,source,target⟩
      have nonzero : BitVec.ofNat 5 r ≠ 0 ∧ BitVec.ofNat 5 r ≠ 1 ∧
          BitVec.ofNat 5 r ≠ 2 ∧ BitVec.ofNat 5 r ≠ 6 ∧ BitVec.ofNat 5 r ≠ 7 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with h | h <;> rw [h] <;> decide
      have abi : (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
          (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read w := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with h | h
        · rw [h]; exact copied.abi.1 .r12 (by simp)
        · rw [h]; exact copied.abi.1 .r15 (by simp)
      exact abi.trans ((keptW _ nonzero.2.2.1 nonzero.2.2.2.1 nonzero.2.2.2.2 target).trans
        (keptV _ nonzero.1 nonzero.2.1 rest source))
    · rename_i hr
      have bounds := tail_count_slot_bounds variant form (by rw [hr]; rfl)
      exact (sameLoadT _ bounds.1 bounds.2.1 bounds.2.2.1).trans (loadV _ bounds.2.2.2)
  have outputSavedT : form = .traitFinalizeIntoReset false →
      memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by
    intro h
    have bounds := Copy.metadataBounds form form.outputSlot hd (by simp)
    exact (sameLoadT _ bounds.1 bounds.2.1 (by rcases bounds.2.2 with h | h; exact .inl h; exact .inr (by omega))).trans (outputSavedV h)
  refine ⟨t, ⟨bufferedT, indexKept.trans input.indexRegister, countKept.trans input.countRegister,
    outputSavedT, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro h
    exact (copied.abi.1 .rbx (by simp)).trans
      ((keptW 3 (by decide) (by decide) (by decide)
        (by cases form <;> simp [tailSetupTargetRegister]; split <;> decide)).trans (bufferV h))
  · cases form with
    | slices | digest => trivial
    | reset stage =>
      intro h
      have hs : stage = 2 := by apply Fin.ext; exact h
      subst stage
      exact (copied.abi.1 .rbx (by simp)).trans (targetW 3 (by simp [Copy.Site.register]))
    | finalizeIntoReset second =>
      cases second
      · trivial
      · cases variant
        · exact (copied.abi.1 .rbx (by simp)).trans (targetW 3 rfl)
        · exact (copied.abi.1 .rbx (by simp)).trans (targetW 3 rfl)
        · exact (copied.abi.1 .r12 (by simp)).trans (targetW 12 rfl)
        · exact (copied.abi.1 .r12 (by simp)).trans (targetW 12 rfl)
    | traitFinalizeIntoReset second =>
      cases second
      · exact (copied.abi.1 .r13 (by simp)).trans (targetW 13 rfl)
      · exact (copied.abi.1 .rbp (by simp)).trans (targetW 5 rfl)
  · intro second h
    exact (copied.abi.1 .rbx (by simp)).trans
      ((keptW 3 (by decide) (by decide) (by decide)
        (by cases form <;> simp [tailSetupTargetRegister]; split <;> decide)).trans (activeV second h))
  · exact copied.rip.trans (by simp only [tailEndPC, Variant.pc, Copy.Site.offset, BitVec.ofNat_add, BitVec.add_assoc])

  · obtain ⟨fuelT,runT⟩ := copied.execution
    exact ⟨_,((runU.trans runV).trans runW).trans runT⟩
  · exact memoryWriteFrame_trans
      (memoryWriteFrame_trans (memoryWriteFrame_trans stackU stackV) stackW) copied.stackFrame

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
