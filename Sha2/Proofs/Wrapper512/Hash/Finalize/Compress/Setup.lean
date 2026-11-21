import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Hash.Finalize.Compress.Call
import Sha2.Proofs.Wrapper512.Hash.Finalize.Compress.Copy

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Machine

theorem setup_effect_frame {v : Variant} {form : Form} {last : Bool} {p : BitVec 64}
    {s t : RamState} (effect : (setupEffect p s form last v).Holds s t) :
    AgreesExcept [.reg 2, .reg 7, .reg 6, .reg 14, .rip] s t := by
  apply effect.agrees.mono
  cases form with
  | slices | digest => simp [setupEffect, Effect.components]
  | reset stage =>
    by_cases hs : stage.val ≠ 2 ∧ last = true <;> simp [setupEffect, hs, Effect.components]
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases last <;> cases v <;> simp [setupEffect, Effect.components]

theorem setup_effect_frame_first {v : Variant} {form : Form} {p : BitVec 64}
    {s t : RamState} (effect : (setupEffect p s form false v).Holds s t) :
    AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t := by
  apply effect.agrees.mono
  cases form with
  | slices | digest | reset stage => simp [setupEffect, Effect.components]
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> simp [setupEffect, Effect.components]

theorem setup_effect_rip (v : Variant) (form : Form) (last : Bool) (p : BitVec 64)
    (s : RamState) : (setupEffect p s form last v).rip = p + BitVec.ofNat 64 (setupLength form last v) := by
  cases form with
  | slices | digest => rfl
  | reset stage =>
    by_cases hs : stage.val ≠ 2 ∧ last = true <;> simp [setupEffect, setupLength, setupBytes, hs]
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases last <;> cases v <;> rfl

theorem setup_effect_rdx {v : Variant} {form : Form} {last : Bool} {p : BitVec 64}
    {s t : RamState} (effect : (setupEffect p s form last v).Holds s t) : t.regValue .rdx = 1 := by
  cases form with
  | slices | digest => exact effect.writes.1
  | reset stage =>
    by_cases hs : stage.val ≠ 2 ∧ last = true
    · simp only [setupEffect, ite_eq_left hs] at effect
      exact effect.writes.1
    · simp only [setupEffect, ite_eq_right hs] at effect
      exact effect.writes.1
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases last <;> cases v <;> exact effect.writes.1

theorem setup_effect_rsi {v : Variant} {form : Form} {last : Bool} {p : BitVec 64}
    {s t : RamState} (effect : (setupEffect p s form last v).Holds s t) :
    t.regValue .rsi = s.regValue (copyRegister v form) := by
  cases form with
  | slices | digest => exact effect.writes.2.2
  | reset stage =>
    by_cases hs : stage.val ≠ 2 ∧ last = true
    · simp only [setupEffect, ite_eq_left hs] at effect
      exact effect.writes.2.2.2
    · simp only [setupEffect, ite_eq_right hs] at effect
      exact effect.writes.2.2
  | finalizeIntoReset second =>
    cases second with
    | false =>
      cases last with
      | false => exact effect.writes.2.2
      | true => exact effect.writes.2.2.2
    | true => exact effect.writes.2.2
  | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> exact effect.writes.2.2

theorem setup_effect_pointer {v : Variant} {form : Form} {last : Bool} {p : BitVec 64}
    {initial s t : RamState} (effect : (setupEffect p s form last v).Holds s t)
    (pointer : hashPointerState v form initial s) : hashPointerState v form initial t := by
  cases form with
  | slices | digest =>
    exact (effect.agrees.read (n := 64) (r := 14) (by simp [setupEffect, Effect.components])).trans pointer
  | reset stage => trivial
  | finalizeIntoReset second =>
    cases second with
    | false => trivial
    | true => exact (effect.agrees.read (n := 64) (r := 3) (by simp [setupEffect, Effect.components])).trans pointer
  | traitFinalizeIntoReset second =>
    cases second with
    | true => exact (effect.agrees.read (n := 64) (r := 3) (by simp [setupEffect, Effect.components])).trans pointer
    | false =>
      cases v <;> constructor
      all_goals first
        | exact (effect.agrees.read (n := 64) (r := 3) (by simp [setupEffect, Effect.components])).trans pointer.1
        | exact (effect.agrees.read (n := 64) (r := 5) (by simp [setupEffect, Effect.components])).trans pointer.1
        | exact (effect.agrees.read (n := 64) (r := 5) (by simp [setupEffect, Effect.components])).trans pointer.2
        | exact (effect.agrees.read (n := 64) (r := 13) (by simp [setupEffect, Effect.components])).trans pointer.2

theorem setup_effect_rdi {v : Variant} {form : Form} {last : Bool} {p : BitVec 64}
    {initial s t : RamState} (effect : (setupEffect p s form last v).Holds s t)
    (pointer : hashPointerState v form initial s)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash := by
  cases form with
  | slices | digest => exact effect.writes.2.1.trans pointer
  | reset stage =>
    have address : rspOf s + 128 = stackPtr initial - BitVec.ofNat 64 (Form.reset stage).finalMemory.hash := by
      change stackPtr s + 128 = _
      rw [rsp]
      simp only [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory,
        BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    by_cases hs : stage.val ≠ 2 ∧ last = true
    · simp only [setupEffect, ite_eq_left hs] at effect
      exact effect.writes.2.2.1.trans address
    · simp only [setupEffect, ite_eq_right hs] at effect
      exact effect.writes.2.1.trans address
  | finalizeIntoReset second =>
    cases second with
    | false =>
      have address : rspOf s + 144 = stackPtr initial - BitVec.ofNat 64 (Form.finalizeIntoReset false).finalMemory.hash := by
        change stackPtr s + 144 = _
        rw [rsp]
        simp only [Form.frameBytes, Form.finalMemory, ResetLayout.finalizeMemory,
          BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      cases last with
      | false => exact effect.writes.2.1.trans address
      | true => exact effect.writes.2.2.1.trans address
    | true => exact effect.writes.2.1.trans pointer
  | traitFinalizeIntoReset second =>
    cases second with
    | false => cases v <;> exact effect.writes.2.1.trans pointer.1
    | true => exact effect.writes.2.1.trans pointer

theorem setup_effect_reset_pointer {v : Variant} {p : BitVec 64}
    {initial s t : RamState} (effect : (setupEffect p s (.reset 1) true v).Holds s t)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (Form.reset 1).frameBytes) :
    t.regValue .r14 = stackPtr initial - 296 := by
  have value : t.regValue .r14 = rspOf s + 128 := effect.writes.2.1
  apply value.trans
  change stackPtr s + 128 = _
  rw [rsp]
  simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem working_registers (v : Variant) (form : Form) :
    ∀ r ∈ [lowCountRegister v form, highCountRegister v form, tailRegister v form],
      r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15] ∧ r ≠ copyRegister v form := by
  cases form <;> cases v <;> decide +revert +kernel

theorem first_setup_kept {s t : RamState}
    (frame : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t)
    (r : Syntax.Reg) (saved : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
    t.regValue r = s.regValue r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact frame.read (n := 64) (r := 3) (by simp)
    | exact frame.read (n := 64) (r := 5) (by simp)
    | exact frame.read (n := 64) (r := 12) (by simp)
    | exact frame.read (n := 64) (r := 13) (by simp)
    | exact frame.read (n := 64) (r := 14) (by simp)
    | exact frame.read (n := 64) (r := 15) (by simp)

theorem setup_kept_saved {s t : RamState}
    (frame : AgreesExcept [.reg 2, .reg 7, .reg 6, .reg 14, .rip] s t)
    (r : Syntax.Reg) (saved : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15])
    (different : r ≠ .r14) : t.regValue r = s.regValue r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (different rfl).elim
    | exact frame.read (n := 64) (r := 3) (by simp)
    | exact frame.read (n := 64) (r := 5) (by simp)
    | exact frame.read (n := 64) (r := 12) (by simp)
    | exact frame.read (n := 64) (r := 13) (by simp)
    | exact frame.read (n := 64) (r := 15) (by simp)

theorem reset_countValue (v : Variant) (stage : Fin 3) (initial s : RamState) :
    v.countValue (.reset stage) initial s = s.regValue .r12 := by
  have stages : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
  rcases stages with rfl | rfl | rfl <;> cases v <;> rfl

theorem trait_first_countValue (v : Variant) (initial s : RamState) :
    v.countValue (.traitFinalizeIntoReset false) initial s =
      memLoad s.external (stackPtr initial - 640) 64 := by
  cases v <;> rfl

theorem finalize_first_countValue (v : Variant) (initial s : RamState) :
    v.countValue (.finalizeIntoReset false) initial s =
      s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) := by
  cases v <;> rfl

set_option maxHeartbeats 800000 in
theorem setup_call_with_registers [Bindings] (body : Compression.BlockCorrect) (last : Bool)
    {form : Form} {v : Variant} {initial s : RamState} {inputs : Array Input}
    {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form) (input : HashAt v initial s hash form)
    (rip : s.RIP = v.pc (copySetupOffset v form last) form)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat,
      128⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ fuel t,
      Advances (returnBoundary initial) fuel s t ∧
      HashAt v initial t (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits chunk)) form ∧
      t.RIP = v.pc (callOffset v form last + 5) form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (last = false →
        t.regValue (lowCountRegister v form) = s.regValue (lowCountRegister v form) ∧
        t.regValue (highCountRegister v form) = s.regValue (highCountRegister v form) ∧
        t.regValue (tailRegister v form) = s.regValue (tailRegister v form)) ∧
      (form = .reset 1 → last = true →
        t.regValue .r14 = stackPtr initial - 296) ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        r ≠ copyRegister v form → r ≠ .r14 → t.regValue r = s.regValue r) ∧
      (form = .finalizeIntoReset false → last = true →
        t.regValue .r14 = stackPtr initial - 488) := by
  obtain ⟨n, u, runU, inputU, ripU, pointerU, bytesU, keptU, stackU, frameU⟩ :=
    copy_local last ctx input rip bytes
  have offsets := copy_setup_offsets v form last
  have site := call_site v form last
  have nextState (i : Nat) (hi : i ≤ setupLength form last v) :
      v.pc (setupOffset v form last) form + BitVec.ofNat 64 i ≠ (returnBoundary initial).rip := by
    rw [Variant.pc_add v _ _ form]
    apply boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    exact inProgram_of_textOffset (v.textOffset form + (setupOffset v form last + i)) (by omega)
  obtain ⟨k, w, runW, readyW, _, effectW⟩ := setup (form := form)
    (v.pc (setupOffset v form last) form) (returnBoundary initial) last v nextState u
    (supportedMachine_readyToStep inputU.machine) (setupCode last inputU.loaded) ripU
  change (setupEffect (v.pc (setupOffset v form last) form) u form last v).Holds u w at effectW
  have frameW := setup_effect_frame effectW
  have preservedW := Absorb.preserved_of_agrees ctx inputU.toPreserved runW readyW frameW
    (by simp [Absorb.LocalWrites, Component.Covers]) (by simp) (by simp) (by simp)
    (by intro h; left; cases v <;> simp)
  have memoryW : w.external = u.external := frameW.external (by simp [Component.Covers])
  have inputW : HashAt v initial w hash form :=
    ⟨preservedW, Absorb.hashState_of_bytes inputU.hashWords (fun _ _ => by rw [memoryW]),
      setup_effect_pointer effectW inputU.hashPointer⟩
  have ripW : w.RIP = v.pc (callOffset v form last) form := by
    calc
      w.RIP = (setupEffect (v.pc (setupOffset v form last) form) u form last v).rip := effectW.rip
      _ = v.pc (setupOffset v form last) form + BitVec.ofNat 64 (setupLength form last v) := setup_effect_rip _ _ _ _ _
      _ = v.pc (setupOffset v form last + setupLength form last v) form := Variant.pc_add v _ _ form
      _ = _ := congrArg (fun off => v.pc off form) offsets.2
  obtain ⟨m, t, output, ripT, abi, runT, stackT, frameT⟩ := call body last ctx inputW ripW
    (setup_effect_rdi effectW inputU.hashPointer inputU.rsp)
    ((setup_effect_rsi effectW).trans pointerU) (setup_effect_rdx effectW)
    (by simpa only [memoryW] using bytesU)
  have kept (r : Syntax.Reg) (saved : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15])
      (notCopy : r ≠ copyRegister v form) (not14 : r ≠ .r14) : t.regValue r = s.regValue r :=
    (abi.1 r saved).trans ((setup_kept_saved frameW r saved not14).trans (keptU r saved notCopy))
  have localFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
    apply memoryWriteFrame_trans stackU
    intro address outside
    rw [stackT address outside, memoryW]
  have finalizePointer : form = .finalizeIntoReset false → last = true →
      t.regValue .r14 = stackPtr initial - 488 := by
    intro hf hl
    subst form
    subst last
    have value : w.regValue .r14 = rspOf u + 144 := effectW.writes.2.1
    apply (abi.1 .r14 (by simp)).trans
    apply value.trans
    change stackPtr u + 144 = _
    rw [inputU.rsp]
    simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  refine ⟨n + k + m, t, (runU.trans runW).trans runT, output, ?_, localFrame, ?_, ?_, ?_, kept, finalizePointer⟩
  · rw [ripT, ripW]
    exact Variant.pc_add v _ 5 form
  · intro hlast
    subst last
    have firstFrame := setup_effect_frame_first effectW
    have preserved (r : Syntax.Reg)
        (member : r ∈ [lowCountRegister v form, highCountRegister v form, tailRegister v form]) :
        t.regValue r = s.regValue r := by
      have hs := working_registers v form r member
      exact (abi.1 r hs.1).trans ((first_setup_kept firstFrame r hs.1).trans (keptU r hs.1 hs.2))
    exact ⟨preserved _ (by simp), preserved _ (by simp), preserved _ (by simp)⟩
  · intro hform hlast
    subst form
    subst last
    exact (abi.1 .r14 (by simp)).trans (setup_effect_reset_pointer effectW inputU.rsp)
  · intro nonterminal
    cases form with
    | slices | digest => exact (nonterminal trivial).elim
    | reset stage =>
      rw [reset_countValue, reset_countValue]
      exact kept .r12 (by simp) (by simp [copyRegister]) (by decide)
    | finalizeIntoReset second =>
      cases second with
      | true => exact (nonterminal rfl).elim
      | false =>
        rw [finalize_first_countValue, finalize_first_countValue]
        cases v <;> exact kept _ (by simp) (by simp [copyRegister]) (by decide)
    | traitFinalizeIntoReset second =>
      cases second with
      | true => exact (nonterminal rfl).elim
      | false =>
        rw [trait_first_countValue, trait_first_countValue]
        have bytesCopy := Absorb.frame_bytes (output := 616) (count := 128) (reserve := 656)
          (offset := 640) (len := 8) ctx frameU
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
        have bytesCall := Absorb.frame_bytes (output := 264) (count := 64) (reserve := 1072)
          (offset := 640) (len := 8) ctx frameT
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
        apply memLoad_congr
        intro i hi
        change (t.external[stackPtr initial - 640 + BitVec.ofNat 64 i]?).getD 0 =
          (s.external[stackPtr initial - 640 + BitVec.ofNat 64 i]?).getD 0
        have hb := bytesCall i hi
        rw [memoryW] at hb
        simpa only [BitVec.ofNat_eq_ofNat] using
          congrArg (fun value : Option UInt8 => value.getD 0) (hb.trans (bytesCopy i hi))

theorem setup_call_local [Bindings] (body : Compression.BlockCorrect) (last : Bool)
    {form : Form} {v : Variant} {initial s : RamState} {inputs : Array Input}
    {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form) (input : HashAt v initial s hash form)
    (rip : s.RIP = v.pc (copySetupOffset v form last) form)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat,
      128⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ fuel t,
      Advances (returnBoundary initial) fuel s t ∧
      HashAt v initial t (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits chunk)) form ∧
      t.RIP = v.pc (callOffset v form last + 5) form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (last = false →
        t.regValue (lowCountRegister v form) = s.regValue (lowCountRegister v form) ∧
        t.regValue (highCountRegister v form) = s.regValue (highCountRegister v form) ∧
        t.regValue (tailRegister v form) = s.regValue (tailRegister v form)) ∧
      (form = .reset 1 → last = true →
        t.regValue .r14 = stackPtr initial - 296) ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) ∧
      (form = .finalizeIntoReset false → last = true →
        t.regValue .r14 = stackPtr initial - 488) := by
  obtain ⟨fuel, t, run, output, ripT, frame, working, pointer, count, _, finalizePointer⟩ :=
    setup_call_with_registers body last ctx input rip bytes
  exact ⟨fuel, t, run, output, ripT, frame, working, pointer, count, finalizePointer⟩

theorem setup_call [Bindings] (body : Compression.BlockCorrect) (last : Bool)
    {form : Form} {v : Variant} {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form) (input : HashAt v initial s hash form)
    (rip : s.RIP = v.pc (if form = .slices then (if last then 0x353 else 0x27b) else (if last then 0x266 else 0x19d)) form)
    (bytes : (⟨(stackPtr initial - 600).toNat, 128⟩ : MemoryRegion).HasBytes s.external chunk)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, HashAt v initial t (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits chunk)) form ∧
      t.RIP = v.pc (if form = .slices then (if last then 0x37e else 0x2a6) else (if last then 0x28f else 0x1c6)) form ∧
      t.regValue .r12 = s.regValue .r12 ∧
      t.regValue .r13 = s.regValue .r13 ∧
      t.regValue (if form = .slices then .r15 else .rbp) = s.regValue (if form = .slices then .r15 else .rbp) := by
  obtain ⟨_, t, _, output, ripT, _, _, _, _, kept, _⟩ := setup_call_with_registers body last ctx input
    (by rcases eligible with rfl | rfl <;> cases last <;> exact rip)
    (by rcases eligible with rfl | rfl <;> exact bytes)
  refine ⟨t, output, ?_, ?_, ?_, ?_⟩
  · rcases eligible with rfl | rfl <;> cases last <;> exact ripT
  · exact kept .r12 (by simp) (by rcases eligible with rfl | rfl <;> simp [copyRegister]) (by decide)
  · exact kept .r13 (by simp) (by rcases eligible with rfl | rfl <;> simp [copyRegister]) (by decide)
  · rcases eligible with rfl | rfl
    · exact kept .r15 (by simp) (by simp [copyRegister]) (by decide)
    · exact kept .rbp (by simp) (by simp [copyRegister]) (by decide)

end Sha2.Proofs.Wrapper512.Hash.Finalize.Compress
