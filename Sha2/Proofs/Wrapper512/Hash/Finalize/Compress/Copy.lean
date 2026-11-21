import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Hash.Finalize.Compress.Call
import Sha2.Proofs.Wrapper512.Finish.Copy

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Machine

def copyRegister (v : Variant) : Form → Syntax.Reg
  | .slices | .reset _ | .finalizeIntoReset false => .rbx
  | .digest => .r15
  | .traitFinalizeIntoReset false => if v = .sha512 then .rbx else .r14
  | _ => .r14

theorem copySetupEffect_eq (v : Variant) (form : Form) (p : BitVec 64) (s : RamState) :
    copySetupEffect p s form v =
      { rip := p + BitVec.ofNat 64 (copySetupLength form v)
        writes := [⟨(.reg (BitVec.ofNat 5 (copyRegister v form).fin.val) : Operand 64),
          rspOf s + BitVec.ofNat 64 (form.frameBytes - copyOutputOffset form)⟩,
          ⟨(.reg 6 : Operand 64), rspOf s + BitVec.ofNat 64
            (form.frameBytes - form.finalMemory.buffer)⟩,
          ⟨(.reg 2 : Operand 64), 128⟩,
          ⟨(.reg 7 : Operand 64), rspOf s + BitVec.ofNat 64
            (form.frameBytes - copyOutputOffset form)⟩] } := by
  cases form with
  | slices | digest | reset stage =>
    cases v <;> simp [Syntax.Reg.fin, copySetupEffect, copySetupLength, copySetupBytes, copyRegister,
      copyOutputOffset, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory] <;> rfl
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> simp [Syntax.Reg.fin, copySetupEffect, copySetupLength, copySetupBytes, copyRegister,
      copyOutputOffset, Form.frameBytes, Form.finalMemory, ResetLayout.finalizeMemory] <;> rfl

theorem copy_setup_offsets (v : Variant) (form : Form) (last : Bool) :
    copySetupOffset v form last + copySetupLength form v + 6 = setupOffset v form last ∧
    setupOffset v form last + setupLength form last v = callOffset v form last := by
  cases form <;> cases v <;> cases last <;> decide +revert +kernel

theorem copy_register_safe (v : Variant) (form : Form) :
    BitVec.ofNat 5 (copyRegister v form).fin.val ≠ 4 ∧
    (form = .digest → BitVec.ofNat 5 (copyRegister v form).fin.val ≠ 3) ∧
    (form = .traitFinalizeIntoReset false →
      BitVec.ofNat 5 (copyRegister v form).fin.val ≠ (if v = .sha512 then 13 else 5)) := by
  cases form <;> cases v <;> decide +revert +kernel

def copyLayout (form : Form) : Wrapper.StackCallLayout form.stackBytes 128 128 0 :=
  ⟨form.frameBytes + 8, form.finalMemory.buffer, copyOutputOffset form,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel⟩

theorem copy_bounds (form : Form) :
    copyOutputOffset form ≤ form.frameBytes ∧ 176 ≤ copyOutputOffset form ∧
    form.finalMemory.buffer ≤ form.frameBytes ∧
    (copyOutputOffset form + 64 ≤ form.finalMemory.hash ∨
      form.finalMemory.hash + 128 ≤ copyOutputOffset form) := by
  cases form <;> decide +revert +kernel

theorem copy_slots_bounds (form : Form) (reset : form.twoOutputs = true) :
    ∀ offset ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot],
      offset ≤ form.frameBytes ∧ 8 ≤ offset ∧
      (copyOutputOffset form + 8 ≤ offset ∨ offset + 128 ≤ copyOutputOffset form) := by
  cases form <;> first | contradiction | decide +revert +kernel

theorem copy_source_apart (form : Form) :
    OffsetsApart (-BitVec.ofNat 64 (form.frameBytes + 8)) 8
      (-BitVec.ofNat 64 form.finalMemory.buffer) 128 := by
  cases form <;> unfold OffsetsApart <;> decide +revert +kernel

def copyDisplacement (v : Variant) (form : Form) (last : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (0x200280 -
    (0x100000 + v.textOffset form + (setupOffset v form last - 6) + 6))

theorem copy_site (v : Variant) (form : Form) (last : Bool) :
    v.textOffset form + (setupOffset v form last - 6) + 6 ≤ 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset form + (setupOffset v form last - 6)) 6 =
      encodeCallM64 (.rip (copyDisplacement v form last)) ∧
    Extracted.textAddress + BitVec.ofNat 64
      (v.textOffset form + (setupOffset v form last - 6)) + 6 +
      (copyDisplacement v form last).signExtend 64 = 0x200280 := by
  cases form <;> cases v <;> cases last <;> decide +revert +kernel

theorem read_namedRegister (s : RamState) (r : Syntax.Reg) :
    (.reg (BitVec.ofNat 5 r.fin.val) : Operand 64).read s = s.regValue r := by
  cases r <;> rfl

theorem copy_register_kept (v : Variant) (form : Form) (r : Syntax.Reg)
    (saved : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15])
    (different : r ≠ copyRegister v form) :
    Component.reg (BitVec.ofNat 5 r.fin.val) ∉
      [Component.reg (BitVec.ofNat 5 (copyRegister v form).fin.val), .reg 6, .reg 2, .reg 7, .rip] := by
  revert saved different
  cases r <;> cases form <;> cases v <;> decide +revert +kernel

theorem hashPointerState_of_copy_saved {v : Variant} {form : Form} {initial s t : RamState}
    (pointer : hashPointerState v form initial s)
    (kept : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      r ≠ copyRegister v form → t.regValue r = s.regValue r) :
    hashPointerState v form initial t := by
  cases form with
  | slices | digest => exact (kept .r14 (by simp) (by simp [copyRegister])).trans pointer
  | reset stage => trivial
  | finalizeIntoReset second =>
    cases second with
    | false => trivial
    | true => exact (kept .rbx (by simp) (by simp [copyRegister])).trans pointer
  | traitFinalizeIntoReset second =>
    cases second with
    | true => exact (kept .rbx (by simp) (by simp [copyRegister])).trans pointer
    | false =>
      cases v <;> exact ⟨(kept _ (by simp) (by simp [copyRegister])).trans pointer.1,
        (kept _ (by simp) (by simp [copyRegister])).trans pointer.2⟩

theorem copy_register_saved (v : Variant) (form : Form) :
    copyRegister v form ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15] := by
  cases form <;> cases v <;> decide +revert +kernel

set_option maxHeartbeats 800000 in
theorem copy_local [Bindings] (last : Bool)
    {form : Form} {v : Variant} {initial s : RamState} {inputs : Array Input}
    {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form) (input : HashAt v initial s hash form)
    (rip : s.RIP = v.pc (copySetupOffset v form last) form)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat,
      128⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      HashAt v initial t hash form ∧ t.RIP = v.pc (setupOffset v form last) form ∧
      t.regValue (copyRegister v form) = stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form) ∧
      (⟨(stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat,
        128⟩ : MemoryRegion).HasBytes t.external chunk ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        r ≠ copyRegister v form → t.regValue r = s.regValue r) ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat, 128⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
  have offsets := copy_setup_offsets v form last
  have site := call_site v form last
  have copySite := copy_site v form last
  have bounds := copy_bounds form
  have frameBounds := frame_bounds form
  have safe := copy_register_safe v form
  have nextState (i : Nat) (hi : i ≤ copySetupLength form v) :
      v.pc (copySetupOffset v form last) form + BitVec.ofNat 64 i ≠
        (returnBoundary initial).rip := by
    rw [Variant.pc_add v _ _ form]
    apply boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    exact inProgram_of_textOffset (v.textOffset form + (copySetupOffset v form last + i)) (by omega)
  obtain ⟨n, u, runU, readyU, _, effectU⟩ := copySetup (form := form)
    (v.pc (copySetupOffset v form last) form) (returnBoundary initial) v nextState s
    (supportedMachine_readyToStep input.machine) (copySetupCode last input.loaded) rip
  change (copySetupEffect (v.pc (copySetupOffset v form last) form) s form v).Holds s u at effectU
  rw [copySetupEffect_eq] at effectU
  have frameU : AgreesExcept [.reg (BitVec.ofNat 5 (copyRegister v form).fin.val),
      .reg 6, .reg 2, .reg 7, .rip] s u := effectU.agrees
  have keptU (r : Syntax.Reg) (saved : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15])
      (different : r ≠ copyRegister v form) : u.regValue r = s.regValue r := by
    simpa only [read_namedRegister] using
      frameU.read (n := 64) (r := BitVec.ofNat 5 r.fin.val)
        (copy_register_kept v form r saved different)
  have preservedU := Absorb.preserved_of_agrees ctx input.toPreserved runU readyU frameU
    (by simp [Absorb.LocalWrites, Component.Covers])
    (by simpa using Ne.symm safe.1) (by simp)
    (by intro h; simpa using Ne.symm (safe.2.1 h))
    (by intro h; left; have hs := safe.2.2 h; cases v <;> simpa using Ne.symm hs)
  have memoryU : u.external = s.external := frameU.external (by simp [Component.Covers])
  have hashU : HashAt v initial u hash form :=
    ⟨preservedU, Absorb.hashState_of_bytes input.hashWords (fun _ _ => by rw [memoryU]),
      hashPointerState_of_copy_saved input.hashPointer keptU⟩
  have pointerArithmetic (offset : Nat) (ho : offset ≤ form.frameBytes) :
      rspOf s + BitVec.ofNat 64 (form.frameBytes - offset) =
        stackPtr initial - BitVec.ofNat 64 offset := by
    have small : form.frameBytes < 2^64 := by cases form <;> simp [Form.frameBytes]
    change stackPtr s + _ = _
    rw [input.rsp, ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) ho]
    calc
      _ = (stackPtr initial - BitVec.ofNat 64 form.frameBytes +
          BitVec.ofNat 64 form.frameBytes) - BitVec.ofNat 64 offset := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      _ = _ := by rw [BitVec.sub_add_cancel]
  have pointerU : u.regValue (copyRegister v form) =
      stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form) := by
    have h := effectU.writes.1
    rw [read_namedRegister] at h
    exact h.trans (pointerArithmetic _ bounds.1)
  have rdiU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form) :=
    effectU.writes.2.2.2.trans (pointerArithmetic _ bounds.1)
  have rsiU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer :=
    effectU.writes.2.1.trans (pointerArithmetic _ bounds.2.2.1)
  have rdxU : u.regValue .rdx = 128 := effectU.writes.2.2.1
  have ripU : u.RIP = v.pc (setupOffset v form last - 6) form := by
    calc
      u.RIP = v.pc (copySetupOffset v form last) form + BitVec.ofNat 64 (copySetupLength form v) := effectU.rip
      _ = v.pc (copySetupOffset v form last + copySetupLength form v) form := Variant.pc_add v _ _ form
      _ = _ := congrArg (fun off => v.pc off form) (by omega)
  obtain ⟨t, result⟩ := Finish.Copy.copy_m64_at ctx hashU.toState (copyLayout form) rfl
    bounds.2.1 bounds.1 (by decide) (copy_source_apart form)
    (setupOffset v form last - 6) (copyDisplacement v form last)
    copySite.1 copySite.2.1 copySite.2.2
    (inProgram_of_textOffset (v.textOffset form + (setupOffset v form last - 6 + 6)) (by omega))
    ripU rdiU rsiU rdxU
  have frame : MemoryWriteFrame u t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat, 128⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
    simpa only [copyLayout] using result.frame
  have outHigh : 128 ≤ copyOutputOffset form := by omega
  have reserveLow : form.frameBytes ≤ form.frameBytes + 8 := by omega
  have unchanged {offset len : Nat} (low : offset ≤ form.frameBytes) (high : len ≤ offset)
      (apart : copyOutputOffset form + len ≤ offset ∨ offset + 128 ≤ copyOutputOffset form) :=
    Absorb.frame_bytes (reserve := form.frameBytes + 8) ctx
      (by simpa only [Nat.add_sub_cancel_left] using frame)
      bounds.1 outHigh reserveLow frameBounds.1 low high apart
  have preservedT := Absorb.preserved_of_bytes hashU.toPreserved result.state (by
    cases form with
    | slices =>
      intro a ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact unchanged (by decide) (by decide) (.inl (by decide)) i hi
    | digest => trivial
    | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
      intro offset member a ha
      obtain ⟨i, hi, rfl⟩ := ha
      have bound := copy_slots_bounds _ rfl offset member
      exact unchanged bound.1 bound.2.1 bound.2.2 i hi)
    (by intro _; exact result.abi.1 .rbx (by simp))
    (by intro h; subst form; left; exact result.abi.1 _ (by cases v <;> simp))
  have wordsT : HashStateAt t (stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash) hash :=
    Absorb.hashState_of_bytes hashU.hashWords
      (unchanged frameBounds.2.2.2.2 (by have h := frameBounds.2.2.2.1; omega) bounds.2.2.2)
  obtain ⟨m, runT⟩ := result.execution
  have frameST : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat, 128⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
    intro address outside
    rw [result.frame address outside, memoryU]
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
    intro address outside
    rw [result.stackFrame address outside, memoryU]
  refine ⟨n + m, t, runU.trans runT, ⟨preservedT, wordsT,
    hashPointerState_of_abi hashU.hashPointer result.abi⟩, ?_, ?_, ⟨bytes.1, ?_⟩,
    ?_, stackFrame, frameST⟩
  · rw [result.rip]
    congr 1
    omega
  · exact (result.abi.1 _ (copy_register_saved v form)).trans pointerU
  · intro i
    have hi : i.val < 128 := by have hs : chunk.size = 128 := bytes.1; omega
    have h := result.bytes i.val hi
    simp only [copyLayout] at h
    change t.external[BitVec.ofNat 64
      ((stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, h, memoryU]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes.2 i
  · intro r saved different
    exact (result.abi.1 r saved).trans (keptU r saved different)

theorem copy [Bindings] (last : Bool)
    {form : Form} {v : Variant} {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form) (input : HashAt v initial s hash form)
    (rip : s.RIP = v.pc (if form = .slices then (if last then 0x353 else 0x27b) else (if last then 0x266 else 0x19d)) form)
    (bytes : (⟨(stackPtr initial - 600).toNat, 128⟩ : MemoryRegion).HasBytes s.external chunk)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, HashAt v initial t hash form ∧ t.RIP = v.pc (if form = .slices then (if last then 0x36e else 0x296) else (if last then 0x27f else 0x1b6)) form ∧
      t.regValue (if form = .slices then .rbx else .r15) = stackPtr initial - 176 ∧
      (⟨(stackPtr initial - 176).toNat, 128⟩ : MemoryRegion).HasBytes t.external chunk ∧
      t.regValue .r12 = s.regValue .r12 ∧
      t.regValue .r13 = s.regValue .r13 ∧
      t.regValue (if form = .slices then .r15 else .rbp) = s.regValue (if form = .slices then .r15 else .rbp) := by
  obtain ⟨_, t, _, output, ripT, pointer, bytesT, kept, _, _⟩ := copy_local last ctx input
    (by rcases eligible with rfl | rfl <;> cases last <;> exact rip)
    (by rcases eligible with rfl | rfl <;> exact bytes)
  refine ⟨t, output, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases eligible with rfl | rfl <;> cases last <;> exact ripT
  · rcases eligible with rfl | rfl <;> exact pointer
  · rcases eligible with rfl | rfl <;> exact bytesT
  · exact kept .r12 (by simp) (by rcases eligible with rfl | rfl <;> simp [copyRegister])
  · exact kept .r13 (by simp) (by rcases eligible with rfl | rfl <;> simp [copyRegister])
  · rcases eligible with rfl | rfl
    · exact kept .r15 (by simp) (by simp [copyRegister])
    · exact kept .rbp (by simp) (by simp [copyRegister])

end Sha2.Proofs.Wrapper512.Hash.Finalize.Compress
