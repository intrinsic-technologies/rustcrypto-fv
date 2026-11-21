import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LoadStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.InputMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem signExtend8_offset {offset : Nat} (h : offset < 128) :
    (BitVec.ofNat 8 offset).signExtend 64 = BitVec.ofNat 64 offset := by
  have hm : (BitVec.ofNat 8 offset).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm,
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]

theorem signExtend32_offset {offset : Nat} (h : offset < 2^31) :
    (BitVec.ofNat 32 offset).signExtend 64 = BitVec.ofNat 64 offset := by
  have hm : (BitVec.ofNat 32 offset).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm,
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]

theorem copy_parameter_pair [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t)
    (codeOffset source target : Nat)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (h15 : t.regValue .r15 = s.regValue .rsi + 32)
    (hsource : source + 40 ≤ 144) (htarget : target + 8 ≤ 1368)
    (hbound : codeOffset + 12 < 118431)
    (hload : Extracted.textBytes.toListFrom codeOffset 4 =
      0x49 :: 0x8b :: (AddrMode.base 15 (.d8 (BitVec.ofNat 8 source))).modrm 1 ::
        (AddrMode.base 15 (.d8 (BitVec.ofNat 8 source))).tail)
    (hstore : Extracted.textBytes.toListFrom (codeOffset + 4) 8 =
      0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).modrm 1 ::
        (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).tail) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 12) ∧
      AgreesExcept [.reg 1, .mem (exponentFrameBase s + BitVec.ofNat 64 target) 8, .rip] t u ∧
      u.external = memStore t.external (exponentFrameBase s + BitVec.ofNat 64 target)
        (memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (32 + source)) 64) := by
  have sourceAddr (next : BitVec 64) : (AddrMode.base 15 (.d8 (BitVec.ofNat 8 source))).addr t
      next =
      s.regValue .rsi + BitVec.ofNat 64 (32 + source) := by
    change t.regValue .r15 + (BitVec.ofNat 8 source).signExtend 64 = _
    rw [h15, signExtend8_offset (by omega), BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have lenLoad : (AddrMode.base 15 (.d8 (BitVec.ofNat 8 source))).tail.length = 1 := rfl
  have lenStore : (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).tail.length = 5 := rfl
  obtain ⟨v, run1, frame1, rip1, value1, agrees1, memory1⟩ :=
    frame_load_r64 ctx.outerBoundary hf codeOffset 0x49 1
      (.base 15 (.d8 (BitVec.ofNat 8 source))) (by simp [RexWPrefix]) (by simp [AddrMode.Valid, regLow]) rfl rfl
      (by decide) hip (by rw [lenLoad]; omega)
      (by simpa only [lenLoad] using hload)
      (by simpa only [sourceAddr] using input_readable ctx hf (offset := 32 + source) (by omega))
  have value : (Operand.reg 1 : Operand 64).read v =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (32 + source)) 64 := by
    change (Operand.reg 1 : Operand 64).read v = _ at value1
    rw [sourceAddr] at value1
    exact value1.trans (input_memLoad_of_frame ctx hf (by omega))
  obtain ⟨u, run2, frame2, rip2, _, agrees2, memory2⟩ :=
    frame_store_r64 ctx.toCalleePre frame1 (codeOffset + 4) target
      (.d32 (BitVec.ofNat 32 target)) 0x48 1 (by simp [RexWPrefix]) rfl rfl
      (signExtend32_offset (by omega)) htarget
      (by simpa only [lenLoad, Nat.add_assoc] using rip1)
      (by rw [lenStore]; omega)
      (by simpa only [lenStore] using hstore)
  change AgreesExcept [.reg 1, .rip] t v at agrees1
  refine ⟨u, run1.trans run2, frame2, ?_, ?_, ?_⟩
  · simpa only [lenStore, Nat.add_assoc] using rip2
  · apply (agrees1.trans agrees2).mono
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    grind only
  · change u.external = memStore t.external _ _
    rw [memory2, memory1]
    exact congrArg (memStore t.external _) value

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
