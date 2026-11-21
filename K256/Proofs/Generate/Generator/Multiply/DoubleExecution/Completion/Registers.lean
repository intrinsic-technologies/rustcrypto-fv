import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Tail
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Layout

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open Common.Point Common.Field

theorem finishRegisters {seed b : Registers} {scope : Values Value 3583}
    {sp : Word} {p : PointWords} {yy zz : Limbs} {n : Nat}
    (regs : ValuesMatch (values seed p yy zz sp) scope)
    (r1 : b[1] = ⟨64, BitVec.ofNat 64 n⟩)
    (r8 : b[8] = ⟨64, scope[3568].get 64 &&& scope[3474].get 64⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ tailRegisters →
      b[i] = (scope[(tailMap[i]).val]?).getD ⟨1, 0⟩) :
    b[1].get 64 = BitVec.ofNat 64 n ∧
    (∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = seed[i]) ∧
    ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
    b[5].get 64 = 0x1000003d10 ∧ b[12].get 64 = sp + 0x490 := by
  have fromScope (i : Fin Reg.count) (hi : i.val ∈ tailRegisters) :
      b[i] = values seed p yy zz sp (tailMap[i]).val := by
    have h := tailIndexBound i hi
    rw [keep i hi, getElem?_pos scope (tailMap[i]).val h, Option.getD_some]
    exact regs ⟨(tailMap[i]).val, h⟩
  refine ⟨by rw [r1]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact (fromScope 4 (by decide)).trans rfl
    · exact (fromScope 22 (by decide)).trans rfl
    · exact (fromScope 39 (by decide)).trans rfl
    · exact (fromScope 50 (by decide)).trans rfl
    · exact (fromScope 51 (by decide)).trans rfl
  · intro i hi
    rcases i with ⟨i, hi'⟩
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width (fromScope 7 (by decide))
    · exact congrArg Value.width (fromScope 6 (by decide))
    · exact congrArg Value.width (fromScope 2 (by decide))
    · exact congrArg Value.width r1
    · exact congrArg Value.width r8
    · exact congrArg Value.width (fromScope 9 (by decide))
  · intro i hi
    rcases i with ⟨i, hi'⟩
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width (fromScope 3 (by decide))
    · exact congrArg Value.width (fromScope 5 (by decide))
    · exact congrArg Value.width (fromScope 12 (by decide))
    · exact congrArg Value.width (fromScope 13 (by decide))
    · exact congrArg Value.width (fromScope 14 (by decide))
    · exact congrArg Value.width (fromScope 15 (by decide))
  · exact congrArg (Value.get 64) (fromScope 5 (by decide))
  · have slot : b[12] = (⟨64, sp + 0x490⟩ : Value) := fromScope 12 (by decide)
    rw [slot]
    exact Value.get_mk _ _

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
