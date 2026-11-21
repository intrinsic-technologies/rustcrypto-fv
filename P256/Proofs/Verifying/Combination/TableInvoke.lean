import P256.Proofs.Verifying.Combination.TableResult
import P256.Proofs.Program.ScalarFrame.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure TableCallSite where
  codeOffset : Nat
  displacement : BitVec 32
  bound : codeOffset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 displacement
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5
    (displacement.signExtend 64) = 0x10aff0

theorem table_call_of_correct (correct : Table.Correct) [Bindings] {s t : RamState} {boundary : ReturnBoundary} {po : Nat}
    {value : Projective} (pre : Pre s boundary) (state : State s t)
    (site : TableCallSite) (pointLow : 4752 ≤ po) (pointHigh : po ≤ 6240)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - 6520)
    (output : t.regValue .rdi = stackPtr s - 4656)
    (cursor : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6496)
    (point : memLoad t.external (stackPtr s - 6496) 64 = stackPtr s - BitVec.ofNat 64 po)
    (valueAt : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 po) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ State s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + 5#64 ∧
      Table.TableAt u (stackPtr s - 4656) (Table.oddTable value) ∧
      memLoad u.external (stackPtr s - 6496) 64 = stackPtr s - BitVec.ofNat 64 po + 128 ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 6552 → len ≤ offset + 8 →
        (offset + 768 ≤ 4656 ∨ 4656 + len ≤ offset) →
        (offset + 8 ≤ 6496 ∨ 6496 + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  obtain ⟨v, run, ready, effect⟩ := call_step (frameOffset := 6552) pre (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp
    site.codeOffset site.displacement
    (Nat.le_of_lt site.bound) site.bytes (by rw [site.target]; decide)
    (by rw [site.target]; exact inProgram_of_textOffset 0xaff0 (by decide)) rip
  have frame := FrameState.after_call pre (by decide) (by decide) state ready effect
  have vin : v.regValue .rsi = stackPtr s - 6520 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - 4656 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + 5#64 :=
    (callEffect_stack effect).1
  have cursor' : memLoad v.external (stackPtr s - 6520) 64 = stackPtr s - 6496 :=
    (scalar_call_read (frameOffset := 6552) (by decide) state effect (offset := 6520) (n := 64) (by decide) (by decide)).trans cursor
  have point' : memLoad v.external (stackPtr s - 6496) 64 = stackPtr s - BitVec.ofNat 64 po :=
    (scalar_call_read (frameOffset := 6552) (by decide) state effect (offset := 6496) (n := 64) (by decide) (by decide)).trans point
  have value' := valueAt.of_bytes_eq (fun _ hi => scalar_call_byte (frameOffset := 6552) (by decide) state effect (by omega) (by omega) hi)
  have cp := table_pre pre frame pointLow pointHigh (effect.rip.trans site.target) vin vout cursor' point'
    (by rw [ret]; simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      inProgram_of_textOffset (site.codeOffset + 5) site.bound)
  obtain ⟨u, result, table⟩ := correct _ _ _ _ _ cp value'
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_table pre frame result vout,
    result.rip.trans ret, ?_, result.cursorValue, ?_, ?_⟩
  · rwa [vout] at table
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · intro offset len ho hl apartOut apartCur i hi
    exact (table_result_byte pre frame result vout ho hl apartOut apartCur hi).trans
      (scalar_call_byte (frameOffset := 6552) (by decide) state effect ho hl hi)

end P256.Proofs.Verifying.Combination
