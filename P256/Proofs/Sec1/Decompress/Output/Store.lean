import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem store_validity [Bindings] {s t : RamState} {boundary : ReturnBoundary} {valid : Bool}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x1100b6) (rbx : t.regValue .rbx = s.regValue .rdi)
    (value : (Operand.reg 0 : Operand 8).read t = BitVec.ofNat 8 valid.toNat) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧ u.RIP = 0x1100b9 ∧
      u.external[s.regValue .rdi + 72]? = some (UInt8.ofNat valid.toNat) ∧
      AgreesExcept [.mem (s.regValue .rdi + 72) 1, .rip] t u := by
  have write := (ScalarFrame.output_writable pre (by decide) state.allocated).add 72 (len := 1) (by decide)
  have writable : MemWritable t (s.regValue .rdi + 72) 1 :=
    ⟨write.low, write.mem, write.tables⟩
  have apart := P256.Proofs.Common.Instructions.RangeApart.add_left
    (ScalarFrame.output_code pre (offset := 0x100b6) (len := 3) (by decide))
    72 (len := 1) (by decide)
  have address (u : RamState) : storeAddrAt 0x1100b6 (.base 3 (.d8 72)) 3 u =
      u.regValue .rbx + 72 := rfl
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m8_r8_legacy_effect_step 0x1100b6 0 (by decide) (.base 3 (.d8 72))
      (by decide) rfl rfl).advances (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x100b6 [0x88,0x43,0x48]
        (by decide) (by decide +kernel))
      ⟨rip, by change MemWritable t (storeAddrAt _ _ 3 t) 1; rw [address, rbx]; exact writable,
        by change RangeApart (storeAddrAt _ _ 3 t) 1 0x1100b6 3
           rw [address, rbx]; exact apart⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100b9 (by decide)))
  change (storeEffect (n := 8) 0x1100b6 3 (storeAddrAt 0x1100b6 (.base 3 (.d8 72)) 3)
    (fun t => (Operand.reg 0 : Operand 8).read t) t).Holds t u at effect
  have agrees : AgreesExcept [.mem (s.regValue .rdi + 72) 1, .rip] t u := by
    have h : AgreesExcept [.mem (storeAddrAt 0x1100b6 (.base 3 (.d8 72)) 3 t) 1, .rip] t u :=
      by simpa only [storeEffect_components, Nat.reduceDiv] using effect.agrees
    simpa only [address, rbx] using h
  have writes : WritesWithin [.mem (s.regValue .rdi + 72) 1, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, ScalarFrame.output_contains pre (by decide) ha⟩
    · exact ha.elim
  have finalState := state.after_effect pre (by decide) ready agrees writes (by simp)
  refine ⟨u, run, finalState, effect.rip, ?_, agrees⟩
  have word : memLoad u.external (s.regValue .rdi + 72) 8 = BitVec.ofNat 8 valid.toNat := by
    have h := effect.writes
    change memLoad u.external (storeAddrAt 0x1100b6 (.base 3 (.d8 72)) 3 t) 8 =
      (Operand.reg 0 : Operand 8).read t at h
    simpa only [address, rbx, value] using h
  have present := (ScalarFrame.output_writable pre (by decide) finalState.allocated).add 72 (len := 1) (by decide)
  have bytes : Bytes u.external (s.regValue .rdi + 72) 1
      (storedByte (memLoad u.external (s.regValue .rdi + 72) 8)) := Bytes.of_memLoad (n := 8) present.mem
  rw [word] at bytes
  have hb := bytes 0 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hb
  exact hb.trans (congrArg some (by cases valid <;> decide +kernel))


theorem store_keeps_byte {s t u : RamState}
    (agrees : AgreesExcept [.mem (s.regValue .rdi + 72) 1, .rip] t u)
    {i : Nat} (hi : i < 65) :
    u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    apply RangeApart.offsets (s.regValue .rdi) (a := 72) (b := 0)
      (len := 1) (count := 65) (by decide) (by decide) (.inr (by decide)) j hj i hi
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm
  · exact hv.elim

end P256.Proofs.Sec1.Decompress.Output
