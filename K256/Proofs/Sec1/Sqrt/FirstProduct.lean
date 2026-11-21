import K256.Proofs.Sec1.Sqrt.WordEquality
import K256.Proofs.Sec1.Sqrt.FirstCall
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem firstMultiply {code : CodeMap} {a b : Limbs} {args : Values Value Reg.count}
    {mem : Ram} {sp input : Word}
    (hsp : args[4].get 64 = sp) (hrbx : args[3].get 64 = input)
    (hs : Writable code mem (sp - 8) 440) (hread : Readable mem input 40)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (hsep : sp.toNat + 432 ≤ input.toNat ∨ input.toNat + 40 + 8 ≤ sp.toNat)
    (hcode : sp.toNat + 432 ≤ 0x1159a4 ∨ 0x115e4d + 8 ≤ sp.toNat)
    (ha : WordsAt mem input 64 a) (hb : WordsAt mem (sp + 40) 64 b) :
    Ahead lifted code (fun l => CallTo (lifted := lifted) (FirstCall mem args sp a b)
        (lifted.program.runBlock (dialect code) l)) ⟨.l1159a4, args, mem⟩ := by
  have haddr : (sp - (8 : BitVec 64)).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by change (8 : BitVec 64).toNat ≤ sp.toNat; exact hbase)]
    rfl
  have data : WordsAt mem input 64 a ∧ WordsAt mem (sp + 40) 64 b := ⟨ha, hb⟩
  lifted_registers [hsp, hrbx]
  subst sp input
  run_tac Lean.Elab.Tactic.withMainContext do
    let d ← Lean.Meta.getLocalDeclFromUserName `data
    let _ ← Refine.Tactic.introAtoms d.fvarId "inWord"
  refine_lifted []
  refine FirstCall.mk rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩ ?_ ?_ ?original ?product ?_ ?_ ?_ ?writes
  case' original => refine ⟨?_, ?_, ?_, ?_, ?_⟩
  case' product => refine ⟨?_, ?_, ?_, ?_, ?_⟩
  case writes =>
    unfold firstFrame
    run_tac Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← Lean.instantiateMVars (← g.getType)
      let mem := t.getArg! 1
      let mem := if mem.isAppOf ``CFG.Location.store && mem.appArg!.isAppOf ``CFG.Location.mk then
        mem.appArg!.appArg! else mem
      let shared ← Refine.Tactic.Shared.new #[]
      let some h ← Refine.Tactic.frameProof? shared (t.getArg! 0) mem (t.getArg! 2)
        | throwError "could not verify the multiplication writes"
      g.assign h
      Lean.Elab.Tactic.replaceMainGoal []
  all_goals lifted_word_reads [word0, word1, word2, word3, word4, word5, word6, word7, word8, word9]
  all_goals lifted_word_eq []

end K256.Proofs.Sec1.Sqrt
