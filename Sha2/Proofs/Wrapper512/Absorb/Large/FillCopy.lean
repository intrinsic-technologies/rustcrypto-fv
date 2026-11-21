import Sha2.Proofs.Wrapper512.Absorb.Branch
import Sha2.Proofs.Wrapper512.Absorb.Large.FillSetup
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter
import Sha2.Proofs.Wrapper512.Absorb.Copied
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Call

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large
open Sha2.Proofs.Wrapper (prefixMessage)
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
structure Filled [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Input) (index : Nat) (form : Form := .slices) : Prop
    extends Preserved v initial s form where
  remaining : index < inputs.size
  bound : 128-(prefixMessage inputs index).size%128 ≤ inputs[index].bytes.size
  hashWords : HashStateAt s (hashPointer initial form form.activeMemory)
    (compressBlocks v.initialHash (prefixMessage inputs index))
  blocks : memLoad s.external (blockCountPointer initial form form.activeMemory) 64 =
    BitVec.ofNat 64 ((prefixMessage inputs index).size/128)
  blocksHigh : memLoad s.external (blockCountHighPointer initial form form.activeMemory) 64 =
    BitVec.ofNat 64 (((prefixMessage inputs index).size/128)/2^64)
  bytes : (⟨(bufferPointer initial form form.activeMemory).toNat,128⟩ : MemoryRegion).HasBytes s.external
    (filledBlock (prefixMessage inputs index) inputs[index].bytes)
  source : (.reg (if form = .slices then 3 else BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read s =inputs[index].address+BitVec.ofNat 64 (128-(prefixMessage inputs index).size%128)
  length : (.reg (v.restRegister form) : Operand 64).read s =BitVec.ofNat 64 (inputs[index].bytes.size-(128-(prefixMessage inputs index).size%128))
  indexRegister : v.indexValue form s =BitVec.ofNat 64 index
  countRegister : v.countValue form initial s =BitVec.ofNat 64 inputs.size

  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx
  bufferRegister : form = .reset 1 →
    s.regValue .rbx = bufferPointer initial form
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
    | .finalizeIntoReset true =>
      s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
    | .traitFinalizeIntoReset second =>
      s.regValue (if second then .rbp else .r13) = 0x10dd60
    | _ => True

theorem filled_of_copy [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} {index : Nat} (ctx : Context v initial inputs form)
    (buffered : Buffered v initial s (prefixMessage inputs index) form form.activeMemory)
    (remaining : index < inputs.size)
    (enough : 128 - (prefixMessage inputs index).size % 128 ≤ inputs[index].bytes.size)
    (copy : Copy.Result v initial s t inputs[index] .fill 0
      ((prefixMessage inputs index).size % 128)
      (128 - (prefixMessage inputs index).size % 128) form)
    (source : (.reg (if form = .slices then 3 else
      BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read t =
      inputs[index].address + BitVec.ofNat 64 (128 - (prefixMessage inputs index).size % 128))
    (length : (.reg (v.restRegister form) : Operand 64).read t =
      BitVec.ofNat 64 (inputs[index].bytes.size - (128 - (prefixMessage inputs index).size % 128)))
    (indexRegister : v.indexValue form t = BitVec.ofNat 64 index)
    (countRegister : v.countValue form initial t = BitVec.ofNat 64 inputs.size)
    (outputSaved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx)
    (bufferRegister : form = .reset 1 → t.regValue .rbx = bufferPointer initial form)
    (memcpyTarget : match form with
      | .reset stage => stage.val = 2 → t.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second =>
        t.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True) :
    Filled v initial t inputs index form := by
  have extent : (prefixMessage inputs index).size % 128 +
      (128 - (prefixMessage inputs index).size % 128) ≤ 128 := by omega
  have unchanged (offset len : Nat) (low : offset ≤ form.frameBytes)
      (high : len ≤ offset) (apart : offset + 128 ≤ form.activeMemory.buffer) :=
    copy.bytes_unchanged ctx extent (offset := offset) (len := len) low high
      (.inr (by omega))
  have hash := hashState_of_bytes buffered.hashWords
    (unchanged form.activeMemory.hash 64
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide))
  have tail := copied_tail ctx buffered copy enough extent
  refine ⟨copy.preserved, remaining, enough, hash, ?_, ?_, ?_,
    source, length, indexRegister, countRegister, ?_, bufferRegister, ?_⟩
  · rw [← buffered.blockCount]
    apply memLoad_congr
    intro j hj
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (unchanged form.activeMemory.countLow 8
        (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)
        (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) j hj)
  · rw [← buffered.blockCountHigh]
    apply memLoad_congr
    intro j hj
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (unchanged form.activeMemory.countHigh 8
        (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)
        (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) j hj)
  · exact ⟨filledBlock_size _ _ enough, tail.2⟩
  · intro hf
    subst form
    rw [← outputSaved rfl]
    apply memLoad_congr
    intro j hj
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (unchanged 408 8 (by decide) (by decide) (by decide) j hj)

  · cases form with
    | finalizeIntoReset second => cases second <;> exact memcpyTarget
    | _ => exact memcpyTarget

end Sha2.Proofs.Wrapper512.Absorb.Large

namespace Sha2.Proofs.Wrapper512.Absorb.Large
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512 Sha2.Proofs.Wrapper

theorem fill_register_facts (v : Variant) (form : Form) :
    finishSourceRegister v form ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
    (∀ r ∈ [v.restRegister form, BitVec.ofNat 5 (v.traversal form).indexReg],
      r ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
      Component.reg r ∉ FillSetup.formComponents v form) ∧
    (∀ r, Copy.Site.fill.register v form = some r →
      r ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
      Component.reg r ∉ FillSetup.formComponents v form) := by
  cases v <;> cases form <;> decide +revert +kernel

theorem fill_count_facts (v : Variant) (form : Form) :
    match (v.traversal form).countReg with
    | some r => BitVec.ofNat 5 r ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
        Component.reg (BitVec.ofNat 5 r) ∉ FillSetup.formComponents v form
    | none => (v.traversal form).countSlot = some 640 ∧
        form.frameBytes = 648 ∧ form.activeMemory.buffer = 616 := by
  have options : (v.traversal form).countReg = some 12 ∨
      (v.traversal form).countReg = some 15 ∨ (v.traversal form).countReg = none := by
    cases v <;> cases form <;> decide +revert +kernel
  rcases options with h | h | h
  all_goals rw [h]
  all_goals revert h
  all_goals cases v <;> cases form <;> decide +revert +kernel

theorem fill_flow (v : Variant) (form : Form) (hd : form ≠ .digest) :
    FillSetup.startOffset v form +
      (FillSetup.bytesAt (FillSetup.formEncoding form) (FillSetup.isTruncated v)).length =
      Copy.Site.fill.relativeOffset form v ∧
    Copy.Site.fill.relativeOffset form v + Copy.Site.fill.size v form =
      Counter.addOffset false v form ∧
    (FillSetup.bytesAt (FillSetup.formEncoding form) (FillSetup.isTruncated v)).length ≤ 18 := by
  cases v <;> cases form with
  | digest => exact (hd rfl).elim
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel

set_option maxHeartbeats 1000000 in
theorem fill_copy [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {index : Nat}
    (ctx : Context v initial inputs form) (input : Prepared v initial s inputs index form)
    (rip : s.RIP = v.pc (FillSetup.startOffset v form) form)
    (enough : 128-(prefixMessage inputs index).size%128 ≤ (inputs[index]'input.remaining).bytes.size)
    (hd : form ≠ .digest := by decide)
    (bufferRegister : form = .reset 1 → s.regValue .rbx = bufferPointer initial form := input.bufferRegister)
    (memcpyTarget : match (generalizing := false) form with
      | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second =>
        s.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by
        cases form with
        | finalizeIntoReset second => cases second <;> exact input.memcpyTarget
        | _ => exact input.memcpyTarget) :
    ∃ t, Filled v initial t inputs index form ∧
      t.RIP = v.pc (Counter.addOffset false v form) form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  let i : Fin inputs.size := ⟨index,input.remaining⟩
  have extent : (prefixMessage inputs index).size%128 +
      (128-(prefixMessage inputs index).size%128) ≤ 128 := by omega
  have flow := fill_flow v form hd
  have facts := fill_register_facts v form
  have reserved : Component.reg 2 ∉ FillSetup.formComponents v form ∧
      Component.reg 4 ∉ FillSetup.formComponents v form := by
    have saved := facts.1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at saved
    rcases saved with h | h | h | h | h | h <;> simp [FillSetup.formComponents,h]
  have noMem : ∀ c ∈ FillSetup.formComponents v form, ∀ a, ¬ c.Covers a := by
    simp [FillSetup.formComponents, Component.Covers]
  obtain ⟨fuel,b,run,ready,_,setup⟩ := FillSetup.run_form v form
    (returnBoundary initial) (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 s
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded)
      (v.textOffset form + FillSetup.startOffset v form) _
      (by have h := FillSetup.start_bound v form; omega)
      (FillSetup.code_facts v form hd)) rip
  obtain ⟨savedB,destinationB,sourceB,frame⟩ := FillSetup.form_result v form hd setup
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame noMem
    reserved.2 (by simp [FillSetup.formComponents])
    (by intro h; exact (hd h).elim) (fun h => .inr (input.outputSaved h))
  have destination : b.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer +
      BitVec.ofNat 64 ((prefixMessage inputs index).size%128) := by
    rw [destinationB]
    change stackPtr s + v.tailValue form s + BitVec.ofNat 64 (form.frameBytes-form.activeMemory.buffer) = _
    rw [input.position,input.rsp]
    have fb : form.activeMemory.buffer ≤ form.frameBytes := by
      cases form <;> dsimp only [Form.activeMemory,Form.bufferedMemory,Form.frameBytes,
        ResetLayout.resetMemory,ResetLayout.cloneMemory,ResetLayout.finalizeMemory] <;> decide
    have large : form.frameBytes < 2^64 := by cases form <;> dsimp only [Form.frameBytes] <;> decide
    rw [← BitVec.ofNat_sub_ofNat_of_le form.frameBytes form.activeMemory.buffer (by omega) fb]
    calc
      _ = ((stackPtr initial - BitVec.ofNat 64 form.frameBytes) + BitVec.ofNat 64 form.frameBytes) -
          BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 ((prefixMessage inputs index).size%128) := by
        simp only [BitVec.sub_eq_add_neg]
        ac_rfl
      _ = _ := by rw [BitVec.sub_add_cancel]
  have source : b.regValue .rsi = inputs[i].address + BitVec.ofNat 64 0 := by
    change b.regValue .rsi = (inputs[index]'input.remaining).address + (0#64)
    rw [BitVec.add_zero]
    exact sourceB.trans input.source
  have count : b.regValue .rdx = BitVec.ofNat 64 (128-(prefixMessage inputs index).size%128) :=
    (frame.read (n:=64) (r:=2) reserved.1).trans input.space
  have setupRip : b.RIP = Extracted.textAddress + BitVec.ofNat 64 (Copy.Site.fill.offset v form) := by
    have h := setup.rip
    have effectRip : (FillSetup.effectAt (v.pc (FillSetup.startOffset v form) form)
        (FillSetup.formEncoding form) s (FillSetup.isTruncated v)).rip =
        v.pc (FillSetup.startOffset v form) form + BitVec.ofNat 64
          (FillSetup.bytesAt (FillSetup.formEncoding form) (FillSetup.isTruncated v)).length := by
      cases form with
      | slices | digest => cases v <;> rfl
      | reset stage =>
        have hc : stage = (0:Fin 3) ∨ stage=1 ∨ stage=2 := by omega
        rcases hc with rfl | rfl | rfl <;> cases v <;> rfl
      | finalizeIntoReset second | traitFinalizeIntoReset second =>
        cases second <;> cases v <;> rfl
    rw [effectRip,Variant.pc_add v _ _ form,flow.1] at h
    exact h
  have targetS : ∀ r, Copy.Site.fill.register v form = some r →
      (.reg r : Operand 64).read s = 0x10dd60 := by
    cases form with
    | slices | digest | traitFinalizeIntoReset _ => intro r hr; cases hr
    | reset stage =>
      intro r hr
      by_cases hs : stage.val = 2
      · simp only [Copy.Site.register, hs, ↓reduceIte, Option.some.injEq] at hr
        subst r
        exact memcpyTarget hs
      · simp only [Copy.Site.register, hs, ↓reduceIte] at hr
        cases hr
    | finalizeIntoReset second =>
      cases second
      · intro r hr; cases hr
      · cases v <;> intro r hr <;> cases hr <;> exact memcpyTarget
  obtain ⟨t,copy⟩ := Copy.copy ctx buffered.toPreserved .fill i (offset:=0)
    (by change 0 + (128-(prefixMessage inputs index).size%128) ≤ (inputs[index]'input.remaining).bytes.size; omega)
    extent setupRip destination source count
    (fun r hr => (frame.read (facts.2.2 r hr).2).trans (targetS r hr))
  have kept (r : BitVec 5) (saved : r ∈ ([3,5,12,13,14,15] : List (BitVec 5)))
      (untouched : Component.reg r ∉ FillSetup.formComponents v form) :
      (.reg r : Operand 64).read t = (.reg r : Operand 64).read s :=
    (Common.SHA256.Finalize.Compress.abi_read copy.abi saved).trans (frame.read untouched)
  have sameSlot (offset : Nat) (low : offset ≤ form.frameBytes) (high : 8 ≤ offset)
      (apart : form.activeMemory.buffer + 8 ≤ offset ∨ offset + 128 ≤ form.activeMemory.buffer) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro j hj
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      ((copy.bytes_unchanged ctx extent low high (by rcases apart with h | h <;> omega) j hj).trans
        (frame.memory _ (noMem · · _)))
  have sourceT : (.reg (finishSourceRegister v form) : Operand 64).read t =
      inputs[i].address + BitVec.ofNat 64 (128-(prefixMessage inputs index).size%128) := by
    rw [Common.SHA256.Finalize.Compress.abi_read copy.abi facts.1,savedB,input.space,input.source,BitVec.add_comm]
    rfl
  have lengthT : (.reg (v.restRegister form) : Operand 64).read t =
      BitVec.ofNat 64 (inputs[i].bytes.size-(128-(prefixMessage inputs index).size%128)) := by
    rw [kept _ (facts.2.1 _ (by simp)).1 (facts.2.1 _ (by simp)).2,input.rest]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by have h := (ctx.inputInMemory i).2.1; omega) enough
  have indexT : v.indexValue form t = BitVec.ofNat 64 index :=
    (kept _ (facts.2.1 _ (by simp)).1 (facts.2.1 _ (by simp)).2).trans input.indexRegister
  have countT : v.countValue form initial t = BitVec.ofNat 64 inputs.size := by
    have hcount := input.countRegister
    have f := fill_count_facts v form
    unfold Variant.countValue at hcount ⊢
    split
    · rename_i r hr
      rw [hr] at hcount f
      exact (kept _ f.1 f.2).trans hcount
    · rename_i hn
      rw [hn] at hcount f
      simp only [f.1,Option.getD_some] at hcount ⊢
      exact (sameSlot 640 (by omega) (by decide) (.inl (by omega))).trans hcount
  have outputB : form = .traitFinalizeIntoReset false →
      memLoad b.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by
    intro hf
    rw [frame.external noMem]
    exact input.outputSaved hf
  have bufferT : form = .reset 1 → t.regValue .rbx = bufferPointer initial form := by
    intro hf; subst form
    exact (kept 3 (by simp) (by cases v <;> decide +kernel)).trans (bufferRegister rfl)
  have targetT : match (generalizing := false) form with
      | .reset stage => stage.val = 2 → t.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second =>
        t.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by
    cases form with
    | slices | digest => trivial
    | reset stage =>
      intro h
      have hs : stage = (2 : Fin 3) := Fin.ext h
      subst stage
      exact (kept 3 (by simp) (by cases v <;> decide +kernel)).trans (memcpyTarget rfl)
    | finalizeIntoReset second =>
      cases second
      · trivial
      · cases v with
        | sha384 | sha512 => exact (kept 3 (by simp) (by decide +kernel)).trans memcpyTarget
        | sha512_224 | sha512_256 => exact (kept 12 (by simp) (by decide +kernel)).trans memcpyTarget
    | traitFinalizeIntoReset second =>
      cases second
      · exact (kept 13 (by simp) (by cases v <;> decide +kernel)).trans memcpyTarget
      · exact (kept 5 (by simp) (by cases v <;> decide +kernel)).trans memcpyTarget
  obtain ⟨copyFuel,copyRun⟩ := copy.execution
  refine ⟨t,filled_of_copy ctx buffered input.remaining enough copy sourceT lengthT indexT countT
    outputB bufferT targetT,?_,⟨_,run.trans copyRun⟩,
    memoryWriteFrame_trans (frame.memoryWriteFrame
      (fun c hc a ha => (noMem c hc a ha).elim)) copy.stackFrame⟩
  exact copy.rip.trans ((Variant.pc_add v _ _ form).trans (congrArg (fun n => v.pc n form) flow.2.1))
end Sha2.Proofs.Wrapper512.Absorb.Large
