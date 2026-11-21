import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.Instructions.ByteStore
import Sha2.Proofs.Common.Instructions.ByteStore.Legacy
import Sha2.Proofs.Wrapper.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

def lengthPC (large : Bool) (v : Variant := .sha256) : BitVec 64 := if large then (v.pc 0x183) else (v.pc 0xba)
def lengthSize (large : Bool) : Nat := if large then 8 else 7
def lengthRegister (large : Bool) : BitVec 5 := if large then 5 else 3
def lengthCode (large : Bool) : List UInt8 :=
  if large then [0x40,0x88,0xac,0x24,0xff,0,0,0] else [0x88,0x9c,0x24,0xff,0,0,0]

theorem store_length_step [Bindings] {v : Variant} (large : Bool) :
    StepEffect (StorePre (lengthPC large v) (lengthSize large) (fun s => rspOf s + 255) 1)
      (codeRange (lengthPC large v) (lengthCode large))
      (storeEffect (lengthPC large v) (lengthSize large) (fun s => rspOf s + 255)
        (fun s => (Operand.reg (lengthRegister large) : Operand 8).read s)) := by
  cases large
  · exact mov_m8_r8_legacy_effect_step (v.pc 0xba) 3 (by decide)
      (.sib 4 none 0 (.d32 255)) (by cases v <;> decide +kernel) rfl rfl
  · exact mov_m8_r8_effect_step (v.pc 0x183) 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d32 255)) (by cases v <;> decide +kernel) rfl rfl

theorem store_length [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v)
    (input : Preserved initial s v) (large : Bool)
    (rip : s.RIP = lengthPC large v) :
    ∃ t, Preserved initial t v ∧
      t.RIP = lengthPC large v + BitVec.ofNat 64 (lengthSize large) ∧
      t.external[stackPtr initial - 89]? =
        some (UInt8.ofNat ((Operand.reg (lengthRegister large) : Operand 8).read s).toNat) ∧
      AgreesExcept [.mem (stackPtr initial - 89) 1, .rip] s t := by
  have addr : rspOf s + 255 = stackPtr initial - 89 := by
    change stackPtr s + 255 = _
    rw [input.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have writable : MemWritable s (rspOf s + 255) 1 := by
    rw [addr]
    exact stack_writable1 ctx input.toState (by decide)
  have apart : RangeApart (rspOf s + 255) 1 (lengthPC large v) (lengthSize large) := by
    rw [addr]
    cases large
    · exact stack_codeApart ctx (offset := 89) (len := 1) (codeOffset := (v.textOffset + 0xba)) (codeLen := 7)
        (by decide) (by decide) (by cases v <;> decide)
    · exact stack_codeApart ctx (offset := 89) (len := 1) (codeOffset := (v.textOffset + 0x183)) (codeLen := 8)
        (by decide) (by decide) (by cases v <;> decide)
  have code : CodeIn (codeRange (lengthPC large v) (lengthCode large)) s := by
    cases large
    · exact programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0xba) _ (by cases v <;> decide) (by cases v <;> decide +kernel)
    · exact programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x183) _ (by cases v <;> decide) (by cases v <;> decide +kernel)
  have next : lengthPC large v + BitVec.ofNat 64 (lengthSize large) ≠ (returnBoundary initial).rip := by
    cases large
    · change v.pc 0xba + BitVec.ofNat 64 7 ≠ _
      rw [Variant.pc_add]
      exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
        (Variant.pc_inProgram v (by decide : 0xc1 < 1024))
    · change v.pc 0x183 + BitVec.ofNat 64 8 ≠ _
      rw [Variant.pc_add]
      exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
        (Variant.pc_inProgram v (by decide : 0x18b < 1024))
  obtain ⟨t, run, ready, effect⟩ := (store_length_step large).advances
    (supportedMachine_readyToStep input.machine) code ⟨rip, writable, apart⟩ next
  have frame := effect.agrees
  simp only [storeEffect_components] at frame
  rw [addr] at frame
  refine ⟨t, preserved_of_agrees ctx input run ready frame ?_ (by simp),
    effect.rip, ?_, frame⟩
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact local_memory (by decide) (by decide) (.inr (by decide)) a ha
    · exact ha.elim
  · have value := effect.writes
    change memLoad t.external (rspOf s + 255) 8 = _ at value
    have allocated : ∀ i < 1, (t.external[rspOf s + 255 + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      exact effect.agrees.grow _ (writable.mem i hi)
    have byte := Bytes.of_memLoad (n := 8) allocated 0 (by decide)
    rw [value] at byte
    simpa only [BitVec.add_zero, addr, storedByte, Nat.mul_zero, Nat.shiftRight_zero] using byte

end Sha2.Proofs.Wrapper.Absorb
