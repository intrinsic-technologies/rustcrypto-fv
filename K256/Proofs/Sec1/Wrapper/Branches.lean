import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Sec1.LIR.Generated.Values

set_option autoImplicit false

namespace K256.Proofs.Sec1.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift LIR

theorem parserDispatch {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {rsp : BitVec 64} (hRsp : Value.get 64 args[4] = rsp)
    (hRead : LoadOk mem (rsp + 0x88) 8) :
    let tag := memLoad mem (rsp + 0x88) 64
    program.runBlock (dialect code) ⟨.l101dea, args, mem⟩ =
      .jump ⟨if tag = 1 then .l101e62 else .l101df8,
        (args.set 3 ⟨64, tag⟩).set 19 (.ofBool (tag == 1)), mem⟩ := by
  dsimp only
  cfg_eval [hRsp, hRead, cmpSpec_ZF, beq_iff_eq]
  split <;> rename_i hTag
  all_goals
    first | rw [ite_eq_left hTag] | rw [ite_eq_right hTag]
    congr 2
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro i
    finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem serializerDispatch {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {rsp : BitVec 64} (hRsp : Value.get 64 args[4] = rsp)
    (hRead : LoadOk mem (rsp + 0x0f) 1) (hTag : memLoad mem (rsp + 0x0f) 8 = 4) :
    program.runBlock (dialect code) ⟨.l101e0c, args, mem⟩ =
      .jump ⟨.l101e4c,
        (((args.set 0 ⟨64, mergeGPR 8 1 (Value.get 64 args[0])⟩).set 1 ⟨64, 4⟩).set 2
          ⟨64, mergeGPR 8 3 (Value.get 64 args[2])⟩).set 19 (.ofBool false), mem⟩ := by
  cfg_eval [hRsp, hRead, hTag]
  have hCarry : (cmpSpec (4 : BitVec 64) 6).CF = true := by decide +kernel
  have hShift : ((61 : BitVec 8) >>> shiftCount 8 4) = 3 := by decide +kernel
  have hTest : (testFlags ((1 : BitVec 8) &&& 3)).ZF.getD false = false := by decide +kernel
  simp only [hCarry, ↓reduceIte, setWidth_mergeGPR8]
  simp only [hShift, hTest, mergeGPR_mergeGPR 8 (Or.inl rfl), Bool.not_false, ↓reduceIte]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

end K256.Proofs.Sec1.Wrapper
