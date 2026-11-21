import P256.Proofs.Projective.Double.Memory
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

theorem calleePre_of_point [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {reserve inputOffset outputOffset : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 736)
    (capacity : 736 + reserve ≤ 1016) (inputBound : inputOffset + 32 ≤ 96)
    (outputAbove : outputOffset ≤ 728) (outputEnd : 32 ≤ outputOffset + 8)
    (rip : t.RIP = entry) (input : t.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (ret : InProgram (returnBoundary t).rip) : CalleePre t boundary entry 32 32 reserve := by
  have hb : (s.regValue .rdi).toNat + 96 < 2^32 := pre.outputBounded
  have addr : (t.regValue .rsi).toNat = (s.regValue .rdi).toNat + inputOffset := by
    rw [input, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : inputOffset < 2^64), Nat.mod_eq_of_lt (by omega)]
  have sub : ∀ a, (registerRegion t .rsi 32).Contains a →
      (registerRegion s .rdi 96).Contains a := by
    intro a ha
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 32 at ha
    rw [addr] at ha
    change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 96
    constructor <;> omega
  apply CalleePre.of_disjoint_input_and_stack
    (initial := s) ⟨736, outputOffset, by decide, capacity, by omega, outputEnd⟩ pre.stack
    (pre.avoids _ (by simp)) state.bindingsSupported state.machine state.directionFlag
    state.loaded rip state.rsp
  · change (t.regValue .rsi).toNat + 32 < 2^32
    rw [addr]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.outputAllocated a (sub a.toNat ha))))
  · intro a ha hs
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) a (sub a ha) hs
  · exact output
  · exact state.allocated
  · exact pre.outerBoundary
  · exact ret

theorem point_unary_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {reserve inputOffset outputOffset x : Nat} {op : Nat → Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (capacity : 736 + reserve ≤ 1016) (inputBound : inputOffset + 32 ≤ 96)
    (outputAbove : outputOffset ≤ 728) (outputSaved : 80 ≤ outputOffset)
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = entry)
    (entryLow : entry.toNat < 2^32) (entryProgram : InProgram entry)
    (routine : ∀ (v : RamState), CalleePre v boundary entry 32 32 reserve →
      MontgomeryAt v (v.regValue .rsi) x →
      ∃ u, CalleeResult v u boundary 32 reserve ∧ MontgomeryAt u (v.regValue .rdi) (op x))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (input : t.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hx : MontgomeryAt t (s.regValue .rdi + BitVec.ofNat 64 inputOffset) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 outputOffset) (op x) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 728 → len ≤ offset + 8 →
        (offset + 32 ≤ outputOffset ∨ outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 1016] := by
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre (by decide) (by decide) state codeOffset disp
    (Nat.le_of_lt codeBound) bytes (by rw [target]; exact entryLow)
    (by rw [target]; exact entryProgram) rip
  have frame := state.after_call pre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) :=
    (callEffect_stack effect).1
  have cp : CalleePre v boundary entry 32 32 reserve := by
    apply calleePre_of_point pre frame capacity inputBound outputAbove (by omega)
      (effect.rip.trans target) vin vout
    rw [ret, show Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) =
      Extracted.textAddress + BitVec.ofNat 64 (codeOffset+5) by
        rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    exact inProgram_of_textOffset _ codeBound
  have vx : MontgomeryAt v (v.regValue .rsi) x := by
    rw [vin]
    apply hx.of_bytes_eq
    intro i hi
    have he : s.regValue .rdi + BitVec.ofNat 64 inputOffset + BitVec.ofNat 64 i =
        s.regValue .rdi + BitVec.ofNat 64 (inputOffset + i) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [he]
    apply effect.agrees.memoryWriteFrame (scalar_call_writes pre (by decide) state)
    intro region member hin
    have same : region = Stack.region s 1016 := by simpa using member
    subst region
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
        (show inputOffset + i < 96 by omega)) hin
  obtain ⟨u, result, value⟩ := routine v cp vx
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_result (frameOffset := 728) pre frame result (by decide)
    (stack_result_work_frame (frameOffset := 728) pre frame result vout (by omega) outputSaved (by omega) (by decide)), result.rip.trans ret, vout ▸ value, ?_, ?_, ?_⟩
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
  · intro offset len ho hl apart i hi
    exact (stack_result_byte (frameOffset := 728) pre frame result vout (by decide) (by omega) ho hl apart hi).trans
      (scalar_call_byte (frameOffset := 728) (by decide) state effect ho hl hi)
  · exact memoryWriteFrame_trans (field_call_work_frame pre state (by decide) (by decide) effect)
      (stack_result_work_frame (frameOffset := 728) pre frame result vout (by omega) outputSaved (by omega) (by decide))

end P256.Proofs.Projective.Double
