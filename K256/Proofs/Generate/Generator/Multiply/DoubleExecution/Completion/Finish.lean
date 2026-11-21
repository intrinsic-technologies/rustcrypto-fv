import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Memory
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Registers
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Induction

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open Common.Point Common.Field Common.Point.DoubleWords.Replay

theorem finishReplay {seed : Registers} {scope : Values Value 3583} {m : Ram}
    {sp : Word} {p : PointWords} {yy zz : Limbs} {n : Nat}
    (rsp : seed[4] = ⟨64, sp⟩)
    (regs : ValuesMatch (values seed p yy zz sp) scope)
    (mem : memory p yy zz sp (BitVec.ofNat 32 (n + 1)) 3583 m) (hn : n < 4) :
    ∃ (b : Registers) (out : Ram), b_l11d880_83.eval (dialect Extracted.programImage) scope m =
      .jump ⟨doublesLabel n, b, out⟩ ∧
      b[1].get 64 = BitVec.ofNat 64 n ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = seed[i]) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
      b[5].get 64 = 0x1000003d10 ∧ b[12].get 64 = sp + 0x490 ∧
      WordsAt out (sp + 0x128) 64 (output p yy zz sp).x ∧
      WordsAt out (sp + 0x150) 64 (output p yy zz sp).y ∧
      WordsAt out (sp + 0x178) 64 (output p yy zz sp).z ∧ RamWriteFrame m out (writes sp) := by
  have spEq : scope[4] = ⟨64, sp⟩ := (show scope[4] = seed[4] from regs (4 : Fin 3583)).trans rsp
  have spBits : scope[4].get 64 = sp := by rw [spEq]; rfl
  have inputs : Writable Extracted.programImage m sp 0x878 ∧
      memLoad m (sp + 0x1bc) 32 = BitVec.ofNat 32 (n + 1) := by
    obtain ⟨win, _, _, _, _, _, _, _, _, _, _, _, _, _, counter, _⟩ := mem
    exact ⟨win, counter⟩
  have stack : Writable Extracted.programImage m sp 0x1c0 :=
    inputs.1.sub (Nat.le_refl _) (by omega)
  obtain ⟨b, out, run, r1, r8, keep, stores, frame⟩ := doubleTail spBits stack inputs.2 hn
  obtain ⟨count, saved, widths, savedWidths, mask, tmp⟩ := finishRegisters regs r1 r8 keep
  have slot {i : Nat} (hi : i < 3583) : scope[i] = values seed p yy zz sp i := regs ⟨i, hi⟩
  have lowInput : scope[3568] = ⟨64, w1529 p yy zz sp⟩ := slot (by decide)
  have highInput : scope[3581] = ⟨64, w1529 p yy zz sp⟩ := slot (by decide)
  have lowMask : scope[3474] = ⟨64, w59 p yy zz sp⟩ := slot (by decide)
  have previous : scope[3576] = ⟨64, w1533 p yy zz sp⟩ := slot (by decide)
  have yLow : scope[3568].get 64 &&& scope[3474].get 64 = w1538 p yy zz sp := by
    rw [lowInput, lowMask, Value.get_mk, Value.get_mk] <;> rfl
  have yHigh : (scope[3581].get 64 >>> 52) + scope[3576].get 64 = w1536 p yy zz sp := by
    rw [highInput, previous, Value.get_mk, Value.get_mk] <;> rfl
  rw [yLow, yHigh] at stores
  have words : WordsAt out (sp + 0x128) 64 (output p yy zz sp).x ∧
      WordsAt out (sp + 0x150) 64 (output p yy zz sp).y ∧
      WordsAt out (sp + 0x178) 64 (output p yy zz sp).z := by
    rw [stores]
    exact finishMemory mem
  obtain ⟨x, y, z⟩ := words
  exact ⟨b, out, run, count, saved, widths, savedWidths, mask, tmp, x, y, z, frame⟩

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
