import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Lower
import Sha2.Proofs.Wrapper.Hash.LengthEncoding

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Compress

variable {v : Variant}

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem first [Bindings]
    {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context initial inputs v)
    (input : HashAt initial s hash v) (rip : s.RIP = (v.pc 0x206))
    (bytes : (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, HashAt initial t hash v ∧ t.RIP = (v.pc 0x213) ∧
      (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes t.external chunk ∧
      memLoad t.external (stackPtr initial - 184) 64 =
        memLoad t.external (stackPtr initial - 288) 64 ∧
      AgreesExcept [.reg 0,.mem (stackPtr initial - 184) 8,.rip] s t := by
  have pre : FirstPre (v.pc 0x206) s := by
    refine ⟨rip, ?_, ?_, ?_⟩
    · rw [stack_address input.rsp]
      exact stack_readable ctx input.toState (offset := 288) (by decide) (by decide)
    · rw [stack_address input.rsp]
      exact stack_writable8 ctx input.toState (offset := 184) (by decide) (by decide)
    · rw [stack_address input.rsp]
      exact stack_codeApart ctx (offset := 184) (codeOffset := (v.textOffset + 0x206)) (by decide) (by decide) (by cases v <;> decide)
  obtain ⟨_, t, run, ready, _, effect⟩ := first_head (v.pc 0x206) (returnBoundary initial)
    (by
      intro i hi
      apply boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
      rw [Variant.pc_add]
      exact v.pc_inProgram (by omega)) s
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x206) firstBytes
      (by cases v <;> decide) (by cases v <;> decide +kernel)) pre
  have rsp : rspOf s = stackPtr initial - 344 := input.rsp
  have frame : AgreesExcept [.reg 0,.mem (stackPtr initial - 184) 8,.rip] s t := by
    simpa only [firstEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Nat.reduceDiv,
      Write.component, Operand.component, rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using effect.agrees
  have writes : Writes initial [.reg 0,.mem (stackPtr initial - 184) 8,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    have w := writes_mem input.rsp (offset := 160) (len := 8) (.inr ⟨by decide, by decide⟩) a
    rw [stack_address input.rsp] at w
    exact w ha
  have state := preserve ctx input run ready frame writes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp)
  have kept : ∀ i < 64,
      t.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨j, hj, he⟩ := ha
    apply OffsetsApart.ne (c₁ := -184) (len₁ := 8) (c₂ := -344) (len₂ := 64)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg] using he.symm
  refine ⟨t, state, (effect.rip.trans (v.pc_add 0x206 13)), ⟨bytes.1, ?_⟩, ?_, frame⟩
  · intro i
    have h := kept i.val (by have size : chunk.size = 64 := bytes.1; omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
      using h.trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
          using bytes.2 i)
  · have word := effect.writes.2
    change memLoad t.external (rspOf s+160) 64 = memLoad s.external (rspOf s+56) 64 at word
    have normalized : memLoad t.external (stackPtr initial-184) 64 =
        memLoad s.external (stackPtr initial-288) 64 := by
      simpa only [rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word
    apply normalized.trans
    symm
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    have address : stackPtr initial - 344 + BitVec.ofNat 64 (56+i) =
        stackPtr initial - 288 + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      rw [← BitVec.add_assoc (-344#64) (56#64)]
      rfl
    have h := kept (56+i) (by omega)
    rw [address] at h
    simpa only [PhysicalMemory.read, BitVec.ofNat_eq_ofNat] using h

end Sha2.Proofs.Wrapper.Hash.Finalize.Compress
