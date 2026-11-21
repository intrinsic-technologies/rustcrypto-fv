import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.Copy.Memory
import P256.Proofs.Common.Instructions.CrossPageStore.Mov
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentMultiply.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem load_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (pc : Nat) (rex : UInt8) (reg : BitVec 3) (am : AddrMode) (offset : Nat)
    (hr : RexWPrefix rex.toBitVec) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (ha : ∀ u : RamState, am.addr u (Extracted.textAddress + BitVec.ofNat 64 pc +
      BitVec.ofNat 64 (movLoadLen am)) = u.regValue .rsp + BitVec.ofNat 64 offset)
    (hreg : gprNumber 0 (rexR rex.toBitVec) reg ≠ 4)
    (hoff : offset + 8 ≤ 1416)
    (hpc : pc + movLoadLen am < 118431)
    (hbytes : Extracted.textBytes.toListFrom pc (rex :: 0x8b :: am.modrm reg :: am.tail).length =
      rex :: 0x8b :: am.modrm reg :: am.tail)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Advances boundary 1 t u ∧ ExponentFrame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (movLoadLen am) ∧
      (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 offset) : Operand 64).read t ∧
      AgreesExcept [.reg (gprNumber 0 (rexR rex.toBitVec) reg), .rip] t u := by
  have hc := programText_slice (programLoaded_codeIn hf.loaded) pc _ (by
    have := am.tail_length_le
    simp only [List.length_cons]
    unfold movLoadLen at hpc
    omega) hbytes
  have haddr := (ha t).trans (congrArg (· + BitVec.ofNat 64 offset) hf.rsp)
  obtain ⟨u, he, hrdy, heff⟩ :=
    (mov_r64_m64_effect_step _ rex hr reg am hv hx hb).advances
      (readyToStep hf.machine hf.bindingsSupported) hc
      ⟨hip, haddr ▸ hf.stack_readable h hoff⟩ (by
        change Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (movLoadLen am) ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program h.outerBoundary (inProgram_of_textOffset _ hpc))
  refine ⟨u, he, hf.of_registers hrdy heff.agrees (by
      simpa only [movR64M64Effect_components, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, Component.reg.injEq, reduceCtorEq, or_false] using Ne.symm hreg)
    (by simp [Component.Covers]), heff.rip, ?_, heff.agrees⟩
  have hw := heff.writes
  change (Operand.reg _ : Operand 64).read u =
    (Operand.mem (am.addr t _) : Operand 64).read t at hw
  rwa [haddr] at hw

theorem store_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (pc : Nat) (rex : UInt8) (reg : BitVec 3) (am : AddrMode) (offset : Nat)
    (hr : RexWPrefix rex.toBitVec) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (ha : ∀ u : RamState, am.addr u (Extracted.textAddress + BitVec.ofNat 64 pc +
      BitVec.ofNat 64 (3 + am.tail.length)) = u.regValue .rsp + BitVec.ofNat 64 offset)
    (hoff : offset + 8 ≤ 1416)
    (hscratch : offset + 8 ≤ 80)
    (hpc : pc + (3 + am.tail.length) < 118431)
    (hbytes : Extracted.textBytes.toListFrom pc (rex :: 0x89 :: am.modrm reg :: am.tail).length =
      rex :: 0x89 :: am.modrm reg :: am.tail)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Advances boundary 1 t u ∧ ExponentFrame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (3 + am.tail.length) ∧
      (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 offset) : Operand 64).read u =
        (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read t ∧
      AgreesExcept [.mem (exponentFrameBase s + BitVec.ofNat 64 offset) 8, .rip] t u := by
  have hc := programText_slice (programLoaded_codeIn hf.loaded) pc _
    (by simp only [List.length_cons]; omega) hbytes
  have haddr := (ha t).trans (congrArg (· + BitVec.ofNat 64 offset) hf.rsp)
  obtain ⟨u, he, hrdy, heff⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any _ rex hr reg am hv hx hb).advances
      (readyToStep hf.machine hf.bindingsSupported) hc
      ⟨hip, by
        have hw := ScalarFrame.stack_writable h.toCalleePre hf.scalarFrame
          (offset := offset) (len := 8) (by decide) hoff (by decide)
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t
          (t.regValue .rsp + BitVec.ofNat 64 offset) 8 at hw
        rw [hf.rsp] at hw
        simpa only [storeAddrAt, haddr] using hw,
        by
          have hc := ScalarFrame.stack_code h.toCalleePre hf.scalarFrame
            (offset := offset) (len := 8) (codeOffset := pc) (codeLen := 3 + am.tail.length)
            (by decide) hoff (by omega)
          change RangeApart (t.regValue .rsp + BitVec.ofNat 64 offset) 8
            (Extracted.textAddress + BitVec.ofNat 64 pc) (3 + am.tail.length) at hc
          rw [hf.rsp] at hc
          simpa only [storeAddrAt, haddr] using hc⟩ (by
        change Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (3 + am.tail.length) ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program h.outerBoundary (inProgram_of_textOffset _ hpc))
  have heq : (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 pc)
      (gprNumber 0 (rexR rex.toBitVec) reg) am t).components =
      [.mem (exponentFrameBase s + BitVec.ofNat 64 offset) 8, .rip] := by
    rw [movM64R64Effect_components]
    change ([.mem (am.addr t _) 8, .rip] : List Component) = _
    rw [haddr]
  have hagree := heq ▸ heff.agrees
  refine ⟨u, he, frame_of_store h hf hrdy hagree hscratch, heff.rip, ?_, hagree⟩
  have hw := heff.writes
  change (Operand.mem (am.addr t _) : Operand 64).read u =
    (Operand.reg _ : Operand 64).read t at hw
  rwa [haddr] at hw


end P256.Proofs.Sec1.SquareRoot.ExponentMultiply.Copy
