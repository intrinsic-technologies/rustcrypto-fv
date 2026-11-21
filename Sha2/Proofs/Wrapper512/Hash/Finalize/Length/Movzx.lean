import Sha2.Proofs.Common.Memory.Fill.Prologue.ZeroProduct.Movzx
import Sha2.Proofs.Wrapper512.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Movzx

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Sha2.Proofs.Common.Memory.Fill

set_option maxRecDepth 2048 in
theorem movzx_eax_r13b_step [Bindings] {form : Form} (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [(if form = .slices then 0x41 else 0x40), 0x0f, 0xb6, 0xc5])
    (hlow : s.RIP.toNat + 4 ≤ 2^32)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg 0 : Operand 32)
        (movzxSpec 32 (((Operand.reg (if form = .slices then 13 else 5) : Operand 64).read t).setWidth 8))
        (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [(if form = .slices then 0x41 else 0x40), 0x0f, 0xb6, 0xc5] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok 0xc5, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_opcodeB6 _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS (if form = .slices then 0x41 else 0x40)) (by rcases eligible with rfl | rfl <;> rfl) (hmode 4) f1
  rw [decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ rfl (hmode 5) hf f2,
    movzx_r32_r8_form _ _ _ _ _ (hmode 5) (by rcases eligible with rfl | rfl <;> rfl) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  rcases eligible with rfl | rfl <;> exact step_rex_legacy1 s _ h _ 0xb6 [0xc5] (by simp [RexPrefix])
    (by decide) hcode hlow hd ((hmode 5).of_cs_lma_eq rfl rfl)

def movzxEaxR13bEffect (p : BitVec 64) (form : Form := .slices) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      ((Operand.reg (if form = .slices then 13 else 5) : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

theorem movzx_eax_r13b_effect_step [Bindings] {form : Form} (p : BitVec 64)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    StepEffect (fun s => s.RIP = p) (codeRange p [(if form = .slices then 0x41 else 0x40), 0x0f, 0xb6, 0xc5])
      (movzxEaxR13bEffect p form) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_eax_r13b_step s h hcode.bytesAt (hcode.low (by simp) (by simp)) eligible,
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)


end Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Movzx
