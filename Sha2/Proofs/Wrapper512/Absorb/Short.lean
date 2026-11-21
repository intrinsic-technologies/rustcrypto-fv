import Sha2.Proofs.Wrapper512.Absorb.Next
import Sha2.Proofs.Wrapper512.Absorb.Bytes
import Sha2.Proofs.Wrapper512.Absorb.ByteAdd
import Sha2.Proofs.Wrapper512.Absorb.Copied
import Sha2.Proofs.Wrapper512.Absorb.SmallSetup
import Sha2.Proofs.Wrapper512.Absorb.TailLength

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper

theorem preservesABI_read {s t : RamState} (abi : Sha2.Proofs.Program.PreservesABI s t)
    {r : BitVec 5} (hr : r ∈ ([3,5,12,13,14,15] : List (BitVec 5))) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact abi.1 .rbx (by simp)
  · exact abi.1 .rbp (by simp)
  · exact abi.1 .r12 (by simp)
  · exact abi.1 .r13 (by simp)
  · exact abi.1 .r14 (by simp)
  · exact abi.1 .r15 (by simp)

theorem short_register_facts (v : Variant) (form : Form) :
    shortLengthRegister v form ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
    shortPositionRegister v form ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
    BitVec.ofNat 5 (v.traversal form).indexReg ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
    BitVec.ofNat 5 (v.traversal form).indexReg ≠ shortLengthRegister v form ∧
    (∀ r, (v.traversal form).countReg = some r →
      BitVec.ofNat 5 r ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
      BitVec.ofNat 5 r ≠ shortLengthRegister v form) ∧
    (∀ r, Copy.Site.short.register v form = some r →
      r ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧ r ≠ shortLengthRegister v form) := by
  cases v <;> cases form <;>
    simp [shortLengthRegister, shortPositionRegister, Variant.traversal,
      ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset,
      Copy.Site.register]
  all_goals try (split <;> simp_all)
  all_goals
    rename_i stage
    rcases stage with ⟨n, hn⟩
    have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases h with rfl | rfl | rfl <;> simp

theorem copy_target_register_iff (v : Variant) (form : Form) (s : RamState) :
    (∀ r, Copy.Site.short.register v form = some r →
      (Operand.reg r : Operand 64).read s = 0x10dd60) ↔
    (match (generalizing := false) form with
      | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second =>
        s.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True) := by
  cases v <;> cases form <;> simp [Copy.Site.register]
  all_goals first | rfl | (split <;> simp_all <;> rfl)

set_option maxHeartbeats 100000 in
theorem finish_short_copy [Bindings] {v : Variant} {form : Form} {initial b c d t : RamState}
    {inputs : Array Input} {previous : ByteArray} (ctx : Context v initial inputs form)
    (buffered : Buffered v initial b previous form form.activeMemory) (i : Fin inputs.size)
    (copy : Copy.Result v initial b c inputs[i] .short 0 (previous.size % 128) inputs[i].bytes.size form)
    (small : inputs[i].bytes.size < 128 - previous.size % 128)
    (preservedT : Preserved v initial t form)
    (lengthT : t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? =
      some (UInt8.ofNat (previous.size % 128 + inputs[i].bytes.size)))
    (noMemD : ∀ a : BitVec 64, d.external[a]? = c.external[a]?)
    (frameT : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1, .rip] d t) :
    Buffered v initial t (previous ++ inputs[i].bytes) form form.activeMemory := by
  have facts : form.activeMemory.buffer ≤ form.frameBytes ∧
      392 ≤ form.activeMemory.buffer ∧ form.activeMemory.hash + 128 = form.activeMemory.buffer ∧
      form.activeMemory.countLow + 192 = form.activeMemory.buffer ∧
      form.activeMemory.countHigh + 200 = form.activeMemory.buffer ∧
      form.activeMemory.tail + 127 = form.activeMemory.buffer := by
    cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes,
      ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have bound : previous.size % 128 + inputs[i].bytes.size < 128 := by omega
  have tailC := copied_tail ctx buffered copy (Nat.le_refl _) (Nat.le_of_lt bound)
  have hashC := hashState_of_bytes buffered.hashWords
    (copy.bytes_unchanged ctx (Nat.le_of_lt bound) (offset:=form.activeMemory.hash) (len:=64)
      (by omega) (by omega) (.inr (by omega)))
  have countersC (offset : Nat) (lower : form.activeMemory.countHigh ≤ offset) (upper : offset ≤ form.activeMemory.countLow) :
      memLoad c.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad b.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    exact copy.bytes_unchanged ctx (Nat.le_of_lt bound) (offset:=offset) (len:=8)
      (by omega) (by omega) (.inr (by omega)) j hj
  have hashD := hashState_of_bytes hashC (fun j _ => noMemD _)
  have hashT := hashState_of_bytes hashD (store_bytes (offset:=form.activeMemory.hash) (len:=64) frameT
    (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> unfold OffsetsApart <;> decide +kernel) (by omega))
  have tailSize : (remainderBytes previous ++ inputs[i].bytes).size =
      previous.size%128+inputs[i].bytes.size := by
    rw [ByteArray.size_append,remainderBytes_size]
  have tailC' : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat,
      (remainderBytes previous ++ inputs[i].bytes).size⟩ : MemoryRegion).HasBytes
      c.external (remainderBytes previous ++ inputs[i].bytes) := by
    simpa only [ByteArray.extract_zero_size] using tailC
  have sameTail : ∀ j < (remainderBytes previous ++ inputs[i].bytes).size,
      t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 j]? =
      c.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 j]? := by
    intro j hj
    rw [tailSize] at hj
    exact (store_bytes (offset:=form.activeMemory.buffer)
      (len:=previous.size%128+inputs[i].bytes.size) frameT
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> change 1 ≤ 18446744073709551489 ∧ _ ≤ 127 <;> constructor <;> omega)
      (by omega) j hj).trans (noMemD _)
  have tailT : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat,
      (remainderBytes previous ++ inputs[i].bytes).size⟩ : MemoryRegion).HasBytes
      t.external (remainderBytes previous ++ inputs[i].bytes) :=
    hasBytes_of_bytes tailC' sameTail
  have countersT (offset : Nat) (lower : form.activeMemory.countHigh ≤ offset) (upper : offset ≤ form.activeMemory.countLow)
      (apart : OffsetsApart (-(BitVec.ofNat 64 form.activeMemory.tail)) 1 (-(BitVec.ofNat 64 offset)) 8) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad b.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    rw [← countersC offset lower upper]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    exact (store_bytes (offset:=offset) (len:=8) frameT
      apart
      (by omega) j hj).trans (noMemD _)
  have result : Buffered v initial t (previous ++ inputs[i].bytes) form form.activeMemory := by
    have small' : inputs[i].bytes.size < 128-previous.size%128 := small
    have counts := append_short_counts previous inputs[i].bytes small'
    refine ⟨preservedT,?_,?_,?_,?_,?_⟩
    · rw [compressBlocks_append_short _ _ _ small']
      exact hashT
    · change (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat, _⟩ : MemoryRegion).HasBytes t.external
        (remainderBytes (previous ++ inputs[i].bytes))
      rw [remainderBytes_append_short _ _ small',counts.2]
      simpa only [tailSize] using tailT
    · rw [counts.2]
      change t.external[stackPtr initial-BitVec.ofNat 64 form.activeMemory.tail]? = some (UInt8.ofNat _)
      exact lengthT
    · rw [counts.1]
      exact (countersT form.activeMemory.countLow (by omega) (by omega) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> unfold OffsetsApart <;> decide +kernel)).trans buffered.blockCount
    · rw [counts.1]
      exact (countersT form.activeMemory.countHigh (by omega) (by omega) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> unfold OffsetsApart <;> decide +kernel)).trans buffered.blockCountHigh
  exact result

theorem short_flow (v : Variant) (form : Form) (hd : form ≠ .digest) :
    v.shortOffset form + (SmallSetup.bytes v form).length = Copy.Site.short.relativeOffset form v ∧
    shortAddOffset v form + 3 = lengthOffset v false form ∧
    lengthOffset v false form + lengthSize false form = counterOffset v false form ∧
    shortLengthRegister v form = lengthRegister false form := by
  cases v <;> cases form with
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel

theorem short_count_slot (v : Variant) (form : Form)
    (hnone : (v.traversal form).countReg = none) :
    (v.traversal form).countSlot = some 640 ∧ form.frameBytes = 648 ∧
      form.activeMemory.buffer = 616 ∧ form.activeMemory.tail = 489 := by
  cases v <;> cases form <;>
    simp_all [Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset,
      ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, ResetLayout.finalizeMemory]
  all_goals try (split at hnone <;> simp_all)
  all_goals
    rename_i stage
    rcases stage with ⟨n, hn⟩
    have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases h with rfl | rfl | rfl <;> simp_all

set_option maxHeartbeats 800000 in
theorem short [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {index : Nat}
    (ctx : Context v initial inputs form) (input : SliceState v initial s inputs index form)
    (rip : s.RIP = v.pc (v.shortOffset form) form)
    (small : (inputs[index]'input.remaining).bytes.size < 128 - (prefixMessage inputs index).size % 128)
    (hd : form ≠ .digest := by decide) :
    ∃ t, Buffered v initial t (prefixMessage inputs (index+1)) form form.activeMemory ∧
      t.RIP = counterPC v false form ∧
      v.indexValue form t = BitVec.ofNat 64 index ∧
      v.countValue form initial t = BitVec.ofNat 64 inputs.size ∧
      (form = .traitFinalizeIntoReset false →
        memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx) ∧
      (form = .reset 1 → t.regValue .rbx = bufferPointer initial form) ∧
      (match (generalizing := false) form with
      | .reset stage => stage.val = 2 → t.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second =>
        t.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have bufferRegister := input.bufferRegister
  let i : Fin inputs.size := ⟨index,input.remaining⟩
  have bound : (prefixMessage inputs index).size % 128 + inputs[i].bytes.size < 128 := by
    change (prefixMessage inputs index).size % 128 + (inputs[index]'input.remaining).bytes.size < 128
    omega
  have flow := short_flow v form hd
  have facts := short_register_facts v form
  have keptSetup (r : BitVec 5) (hr : r ∈ ([3,5,12,13,14,15] : List (BitVec 5))) :
      Component.reg r ∉ [.reg 7,.reg 6,.reg 2,.flags,.rip] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have noMemSetup : ∀ c ∈ ([.reg 7,.reg 6,.reg 2,.flags,.rip] : List Component), ∀ a, ¬ c.Covers a := by
    simp [Component.Covers]
  obtain ⟨fuel,b,run,ready,_,setup⟩ := SmallSetup.run (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 form hd s
    (supportedMachine_readyToStep input.machine) (SmallSetup.code input.loaded form hd) rip
  obtain ⟨destinationB,sourceB,countB,frameB⟩ := SmallSetup.effect_result setup
  have bufferedB := buffered_of_agrees ctx input.toBuffered run ready frameB noMemSetup
    (by simp) (by simp) (by intro h; exact (hd h).elim) (fun h => .inr (input.outputSaved h))
  have destination : b.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer +
      BitVec.ofNat 64 ((prefixMessage inputs index).size % 128) := by
    change b.regValue .rdi = rspOf s + v.tailValue form s +
      BitVec.ofNat 64 (form.frameBytes - form.activeMemory.buffer) at destinationB
    rw [destinationB]
    change stackPtr s + v.tailValue form s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.buffer) = _
    rw [input.position, input.rsp]
    have fb : form.activeMemory.buffer ≤ form.frameBytes := by
      cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes,
        ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
    have large : form.frameBytes < 2^64 := by cases form <;> dsimp only [Form.frameBytes] <;> decide
    rw [← BitVec.ofNat_sub_ofNat_of_le form.frameBytes form.activeMemory.buffer (by omega) fb]
    calc
      _ = ((stackPtr initial - BitVec.ofNat 64 form.frameBytes) + BitVec.ofNat 64 form.frameBytes) -
        BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 ((prefixMessage inputs index).size % 128) := by
          simp only [BitVec.sub_eq_add_neg]
          ac_rfl
      _ = _ := by rw [BitVec.sub_add_cancel]
  have source : b.regValue .rsi = inputs[i].address + BitVec.ofNat 64 0 := by
    change b.regValue .rsi = v.sourceValue form s at sourceB
    change b.regValue .rsi = inputs[i].address + (0#64)
    rw [BitVec.add_zero]
    exact sourceB.trans input.source
  have count : b.regValue .rdx = BitVec.ofNat 64 inputs[i].bytes.size := countB.trans input.length
  have setupRip : b.RIP = Extracted.textAddress + BitVec.ofNat 64 (Copy.Site.short.offset v form) := by
    have h := setup.rip
    change b.RIP = v.pc (v.shortOffset form) form + BitVec.ofNat 64 (SmallSetup.bytes v form).length at h
    rw [Variant.pc_add v _ _ form, flow.1] at h
    exact h
  have targetS := (copy_target_register_iff v form s).mpr (by
    cases form with
    | slices | digest => trivial
    | reset stage | traitFinalizeIntoReset flag => exact input.memcpyTarget
    | finalizeIntoReset flag => cases flag <;> exact input.memcpyTarget)
  obtain ⟨c,copy⟩ := Copy.copy ctx bufferedB.toPreserved .short i (offset:=0)
    (by omega) (Nat.le_of_lt bound) setupRip destination source count
    (fun r hr => (frameB.read (n:=64) (r:=r) (keptSetup r (facts.2.2.2.2.2 r hr).1)).trans (targetS r hr))
  have lengthC : (Operand.reg (shortLengthRegister v form) : Operand 64).read c =
      BitVec.ofNat 64 inputs[i].bytes.size :=
    (preservesABI_read copy.abi facts.1).trans
      ((frameB.read (n:=64) (r:=shortLengthRegister v form) (keptSetup _ facts.1)).trans input.length)
  have positionC : (Operand.reg (shortPositionRegister v form) : Operand 64).read c =
      BitVec.ofNat 64 ((prefixMessage inputs index).size % 128) :=
    (preservesABI_read copy.abi facts.2.1).trans
      ((frameB.read (n:=64) (r:=shortPositionRegister v form) (keptSetup _ facts.2.1)).trans input.position)
  have copyRip : c.RIP = v.pc (shortAddOffset v form) form :=
    copy.rip.trans (Variant.pc_add v _ _ form)
  obtain ⟨d,preservedD,ripD,lowD,frameD,runD⟩ := add_short_length_local ctx copy.preserved copyRip hd
  have lengthD : (Operand.reg (lengthRegister false form) : Operand 8).read d =
      BitVec.ofNat 8 ((prefixMessage inputs index).size % 128 + inputs[i].bytes.size) := by
    rw [← flow.2.2.2, lowD]
    change ((Operand.reg (shortLengthRegister v form) : Operand 64).read c).setWidth 8 +
      ((Operand.reg (shortPositionRegister v form) : Operand 64).read c).setWidth 8 = _
    rw [lengthC,positionC,BitVec.setWidth_ofNat_of_le (by decide),BitVec.setWidth_ofNat_of_le (by decide),← BitVec.ofNat_add,Nat.add_comm]
  have storeRip : d.RIP = lengthPC v false form := by rw [flow.2.1] at ripD; exact ripD
  obtain ⟨t,preservedT,ripT,lengthT,frameT,runT⟩ := store_length_local ctx preservedD false storeRip hd
  have noMemD : ∀ a : BitVec 64, d.external[a]? = c.external[a]? :=
    fun a => frameD.memory a (by simp [Component.Covers])
  have lengthT' : t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? =
      some (UInt8.ofNat ((prefixMessage inputs index).size % 128 + inputs[i].bytes.size)) := by
    rw [lengthT, lengthD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bufferedT := finish_short_copy ctx bufferedB i copy small preservedT lengthT' noMemD frameT
  have kept (r : BitVec 5) (hr : r ∈ ([3,5,12,13,14,15] : List (BitVec 5)))
      (hne : r ≠ shortLengthRegister v form) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
    (frameT.read (n:=64) (r:=r) (by simp)).trans
      ((frameD.read (n:=64) (r:=r) (by simp [hne])).trans
        ((preservesABI_read copy.abi hr).trans (frameB.read (n:=64) (r:=r) (keptSetup r hr))))
  have sameSlot (off : Nat) (lo : off ≤ form.frameBytes) (hi : 8 ≤ off)
      (apartCopy : form.activeMemory.buffer + 8 ≤ off ∨ off + 128 ≤ form.activeMemory.buffer)
      (apartStore : OffsetsApart (-(BitVec.ofNat 64 form.activeMemory.tail)) 1 (-(BitVec.ofNat 64 off)) 8) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    exact (store_bytes frameT apartStore (by decide) j hj).trans ((noMemD _).trans
      ((copy.bytes_unchanged ctx (Nat.le_of_lt bound) lo hi
        (by rcases apartCopy with h | h <;> omega) j hj).trans
        (frameB.memory _ (noMemSetup · · _))))
  have countT : v.countValue form initial t = BitVec.ofNat 64 inputs.size := by
    have hcount := input.countRegister
    unfold Variant.countValue at hcount ⊢
    split
    · rename_i r hr
      rw [hr] at hcount
      exact (kept _ (facts.2.2.2.2.1 r hr).1 (facts.2.2.2.2.1 r hr).2).trans hcount
    · rename_i hn
      rw [hn] at hcount
      have hf := short_count_slot v form hn
      simp only [hf.1, Option.getD_some] at hcount ⊢
      exact (sameSlot 640 (by omega) (by decide) (.inl (by omega))
        (by rw [hf.2.2.2]; unfold OffsetsApart; decide +kernel)).trans hcount
  refine ⟨t, ?_, ?_, (kept _ facts.2.2.1 facts.2.2.2.1).trans input.indexRegister, countT, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prefixMessage_succ inputs index input.remaining]
    exact bufferedT
  · rw [lengthPC, Variant.pc_add v _ _ form, flow.2.2.1] at ripT
    exact ripT
  · intro h
    subst form
    exact (sameSlot 408 (by decide) (by decide) (.inr (by decide))
      (by unfold OffsetsApart; decide +kernel)).trans (input.outputSaved rfl)
  · intro h
    subst form
    exact (kept 3 (by simp) (by cases v <;> decide +kernel)).trans (bufferRegister rfl)
  · apply (copy_target_register_iff v form t).mp
    intro r hr
    exact (kept r (facts.2.2.2.2.2 r hr).1 (facts.2.2.2.2.2 r hr).2).trans (targetS r hr)

  · obtain ⟨copyFuel, copyRun⟩ := copy.execution
    exact ⟨_, ((run.trans copyRun).trans runD).trans runT⟩
  · apply memoryWriteFrame_trans (frameB.memoryWriteFrame
      (fun c hc a ha => (noMemSetup c hc a ha).elim))
    apply memoryWriteFrame_trans copy.stackFrame
    refine memoryWriteFrame_trans (frameD.memoryWriteFrame ?_) ?_
    · intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> exact ha.elim
    · apply frameT.memoryWriteFrame
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · refine ⟨Stack.region initial (v.routine form).minStackBytes, by simp, ?_⟩
        apply stackRegion_contains_sub ctx.stack.2.2.1 ?_ ?_ ha
        all_goals cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory,
          Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory,
          ResetLayout.finalizeMemory] <;> decide
      · exact ha.elim

end Sha2.Proofs.Wrapper512.Absorb
