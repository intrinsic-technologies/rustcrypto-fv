import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Machine.Stages.Stack
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false
namespace Sha2.Proofs.Wrapper512.Absorb.Large
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def finishTailMode (form : Form) : AddrMode :=
  match form with
  | .reset _ => .sib 4 none 0 (.d8 127)
  | _ => .sib 4 none 0 (.d32 (BitVec.ofNat 32 (form.frameBytes-form.activeMemory.tail)))

def finishTailLength (form : Form) : Nat := 3 + (finishTailMode form).tail.length

def finishMoveOffset (v : Variant) (form : Form) : Nat :=
  (v.traversal form).fillCall + 5 + finishTailLength form

def finishSourceRegister (v : Variant) (form : Form) : BitVec 5 :=
  if form = .slices then 3 else BitVec.ofNat 5 (v.traversal form).lengthReg

def finishTargetRegister (v : Variant) (form : Form) : BitVec 5 :=
  BitVec.ofNat 5 (v.traversal form).dataReg

set_option maxRecDepth 2048 in
theorem finishTailAddress (form : Form) (s : RamState) (p : BitVec 64) :
    storeAddrAt p (finishTailMode form) (finishTailLength form) s =
      rspOf s + BitVec.ofNat 64 (form.frameBytes-form.activeMemory.tail) := by
  cases form <;> rfl

theorem finishTailCodeLength (form : Form) :
    (0xc6 :: (finishTailMode form).modrm 0 :: ((finishTailMode form).tail ++ immBytes 8 0)).length = finishTailLength form := by
  simp only [List.length_cons, List.length_append, immBytes_length, finishTailLength]
  omega

theorem finishMoveStep [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeMovR64R64 dst src))
      (movR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, bytes, hrex, hmod, hdst, hsrc⟩ := encodeMovR64R64_spec dst src
  rw [bytes, ← hdst, ← hsrc]
  exact mov_r64_r64_effect_step p rex modrm hrex hmod

theorem finishCode (v : Variant) (form : Form) (nonDigest : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + (v.traversal form).fillCall + 5)
      (finishTailLength form) =
      0xc6 :: (finishTailMode form).modrm 0 :: ((finishTailMode form).tail ++ immBytes 8 0) ∧
    Extracted.textBytes.toListFrom (v.textOffset form + finishMoveOffset v form) 3 =
      encodeMovR64R64 (BitVec.ofNat 4 (v.traversal form).dataReg)
        ((finishSourceRegister v form).setWidth 4) ∧
    v.textOffset form + finishMoveOffset v form + 3 < 71757 := by
  cases form <;> cases v <;> first | contradiction | decide +revert +kernel

theorem finishTailLocal (form : Form) {initial : RamState} :
    LocalWrites initial [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1, .rip] form := by
  have facts : form.activeMemory.tail ≤ form.stackBytes ∧ 49 ≤ form.activeMemory.tail ∧
      (match form with
      | .slices | .digest => 1+624 ≤ form.activeMemory.tail ∨ form.activeMemory.tail ≤ 600
      | _ => ∀ slot ∈ form.metadataSlots,
          OffsetsApart (-BitVec.ofNat 64 form.activeMemory.tail) 1 (-BitVec.ofNat 64 slot) 8) := by
    cases form <;> simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, OffsetsApart] <;> decide +revert +kernel
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have h := local_memory facts.1 facts.2.1 (by cases form <;> exact facts.2.2) a ha
    cases form <;> exact h
  · exact ha.elim

theorem finishRegisters (v : Variant) (form : Form) :
    (BitVec.ofNat 4 (v.traversal form).dataReg).setWidth 5 = finishTargetRegister v form ∧
    ((finishSourceRegister v form).setWidth 4).setWidth 5 = finishSourceRegister v form ∧
    Component.reg 4 ∉ [Component.reg (finishTargetRegister v form), .rip] := by
  cases form <;> cases v <;> decide +revert +kernel

theorem finish [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (rip : s.RIP = v.pc ((v.traversal form).fillCall + 5) form)
    (nonDigest : form ≠ .digest := by decide)
    (outputSaved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by simp) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (finishMoveOffset v form + 3) form ∧
      v.sourceValue form t = (.reg (finishSourceRegister v form) : Operand 64).read s ∧
      t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? = some 0 ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1,
        .reg (finishTargetRegister v form), .rip] s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have address : rspOf s + BitVec.ofNat 64 (form.frameBytes-form.activeMemory.tail) =
      stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail := by
    change stackPtr s + _ = _
    rw [input.rsp]
    have eq : BitVec.ofNat 64 (form.frameBytes-form.activeMemory.tail) =
        BitVec.ofNat 64 form.frameBytes - BitVec.ofNat 64 form.activeMemory.tail := by
      cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel
    rw [eq]
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using
      congrArg (fun x => x - BitVec.ofNat 64 form.activeMemory.tail)
        (BitVec.sub_add_cancel (stackPtr initial) (BitVec.ofNat 64 form.frameBytes))
  have writable : MemWritable s (rspOf s + BitVec.ofNat 64 (form.frameBytes-form.activeMemory.tail)) 1 := by
    rw [address]
    have read := Common.Encoding.Serialize.readable_of_grow
      (Dispatch.stack_sub_readable512 ctx (offset := form.activeMemory.tail) (len := 1)
        (by cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel) (by omega)) input.allocated
    refine MemWritable.of_not_reserved (by decide) read.low read.mem ?_
    intro i hi reserved
    exact (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes)
      (by cases form <;> simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2 _
      (stackRegion_contains_sub ctx.stack.2.2.1
        (by cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel) (by cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel) ⟨i, hi, rfl⟩)
      (.inr reserved)
  have apart : RangeApart (rspOf s + BitVec.ofNat 64 (form.frameBytes-form.activeMemory.tail)) 1
      (v.pc ((v.traversal form).fillCall + 5) form) (finishTailLength form) := by
    rw [address]
    exact Machine.Stages.stack_slot_codeApart ctx
      (by cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel) (by cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel)
      (by have h := (finishCode v form nonDigest).2.2; simp only [finishMoveOffset] at h; omega)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (mov_m8_imm8_effect_step (v.pc ((v.traversal form).fillCall+5) form) (finishTailMode form)
      (by cases form <;> dsimp only [finishTailMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel) (by cases form <;> rfl) (by cases form <;> rfl) 0).advances
      (supportedMachine_readyToStep input.machine)
      (programText_slice (programLoaded_codeIn input.loaded)
        (v.textOffset form + ((v.traversal form).fillCall + 5)) _
        (by have h := (finishCode v form nonDigest).2.2; simp only [finishMoveOffset] at h
            rw [finishTailCodeLength]; omega)
        (by simpa only [finishTailCodeLength, Nat.add_assoc] using (finishCode v form nonDigest).1))
      (by change StorePre _ (finishTailLength form) (storeAddrAt _ _ (finishTailLength form)) 1 s
          exact ⟨rip, by simpa only [finishTailAddress] using writable, by simpa only [finishTailAddress] using apart⟩)
      (by
        change v.pc ((v.traversal form).fillCall+5) form + BitVec.ofNat 64 (finishTailLength form) ≠ _
        rw [Variant.pc_add (form := form)]
        exact boundary_ne_program ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
          (inProgram_of_textOffset (v.textOffset form + finishMoveOffset v form)
            (by have h := (finishCode v form nonDigest).2.2; omega)))
  have frameU : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1, .rip] s u := by
    have h := effectU.agrees
    simp only [movM8Imm8Effect, storeEffect_components] at h
    change AgreesExcept [.mem (storeAddrAt _ _ (finishTailLength form) s) 1, .rip] s u at h
    rwa [finishTailAddress, address] at h
  have preservedU := preserved_of_agrees ctx input runU readyU frameU (finishTailLocal form)
    (by simp) (by simp) (by simp) (by intro _; left; simp)
  have byte : u.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? = some 0 := by
    have value := effectU.writes
    change memLoad u.external (storeAddrAt _ _ (finishTailLength form) s) 8 = 0 at value
    rw [finishTailAddress, address] at value
    have allocated : ∀ i < 1, (u.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      exact frameU.grow _ (by simpa only [address] using writable.mem i hi)
    have stored := Bytes.of_memLoad (n := 8) allocated 0 (by decide)
    rw [value] at stored
    simpa [storedByte] using stored
  have targetEq : (BitVec.ofNat 4 (v.traversal form).dataReg).setWidth 5 = finishTargetRegister v form := by
    exact (finishRegisters v form).1
  have sourceEq : ((finishSourceRegister v form).setWidth 4).setWidth 5 = finishSourceRegister v form := by
    exact (finishRegisters v form).2.1
  have moveLength : (encodeMovR64R64 (BitVec.ofNat 4 (v.traversal form).dataReg)
      ((finishSourceRegister v form).setWidth 4)).length = 3 := rfl
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (finishMoveStep (v.pc (finishMoveOffset v form) form)
      (BitVec.ofNat 4 (v.traversal form).dataReg) ((finishSourceRegister v form).setWidth 4)).advances
      (supportedMachine_readyToStep preservedU.machine)
      (programText_slice (programLoaded_codeIn preservedU.loaded) (v.textOffset form + finishMoveOffset v form) _
        (by have h := (finishCode v form nonDigest).2.2
            simpa only [moveLength] using Nat.le_of_lt h)
        (by simpa only [moveLength] using (finishCode v form nonDigest).2.1))
      (effectU.rip.trans (Variant.pc_add v _ _ form))
      (by change v.pc (finishMoveOffset v form) form + BitVec.ofNat 64 3 ≠ _
          rw [Variant.pc_add (form := form)]
          exact boundary_ne_program ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
            (inProgram_of_textOffset (v.textOffset form + (finishMoveOffset v form+3))
              (by simpa only [finishTailCodeLength, Nat.add_assoc] using (finishCode v form nonDigest).2.2)))
  have frameT : AgreesExcept [.reg (finishTargetRegister v form), .rip] u t := by
    simpa only [movR64R64Effect_components, targetEq] using effectT.agrees
  have kept : Component.reg 4 ∉ [Component.reg (finishTargetRegister v form), .rip] := by
    exact (finishRegisters v form).2.2
  have preservedT := preserved_of_agrees ctx preservedU runT readyT frameT
    (by intro c hc a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact ha.elim) kept (by simp)
    (by intro hd; exact (nonDigest hd).elim)
    (by intro hf; right; subst form
        rw [← outputSaved rfl]
        apply memLoad_congr
        intro i hi
        exact congrArg (fun x : Option UInt8 => x.getD 0)
          ((finishTailLocal (.traitFinalizeIntoReset false)).memory frameU
            ⟨Form.outputSlot (.traitFinalizeIntoReset false), by simp [Form.metadataSlots], i, hi, rfl⟩))
  refine ⟨t, preservedT, effectT.rip.trans (Variant.pc_add v _ 3 form), ?_, ?_, ?_,
    ⟨_, runU.trans runT⟩, memoryWriteFrame_trans
      (frameU.memoryWriteFrame ((finishTailLocal form).stack ctx))
      (frameT.memoryWriteFrame (by simp [WritesWithin, Component.Covers]))⟩
  · have h := effectT.writes
    change (.reg _ : Operand 64).read t = (.reg _ : Operand 64).read u at h
    rw [targetEq, sourceEq] at h
    exact h.trans (frameU.read (n := 64) (r := finishSourceRegister v form) (by simp))
  · exact (frameT.byte (by simp [Component.Covers])).trans byte
  · exact (frameU.trans frameT).mono (by simp)

end Sha2.Proofs.Wrapper512.Absorb.Large
