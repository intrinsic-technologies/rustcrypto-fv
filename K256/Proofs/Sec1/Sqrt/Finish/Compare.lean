import K256.Proofs.Sec1.Sqrt.Finish.Barrier
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Call

namespace K256.Proofs.Sec1.Sqrt.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field
open K256.Proofs.Sec1.LIR (lifted)
open K256.Proofs.Sec1.SqrtLaterProducts.Final (ScratchWrites)

def compareWriteOffsets : List Word := [0xa0, 0x68, 0x90, 0x100, 0xb0, 0xa8, 0x50, 0xf8, 0xf0, 0x20, 0x18]

structure BarrierArgs (initial args : Values Value Reg.count) (sp : Word) (a : Limbs) : Prop where
  rsp : args[4] = ⟨64, sp - 8⟩
  rdiWidth : args[7].width = 64
  rbxWidth : args[3].width = 64
  r14Width : args[14].width = 64
  limb3 : args[14].get 64 = a[3]
  limb4 : args[3].get 64 = a[4]
  df : args[22] = initial[22]
  mxcsr : args[39] = initial[39]
  ftw : args[50] = initial[50]
  fcw : args[51] = initial[51]

def CallsBarrier (initial : Values Value Reg.count) (mem : Ram) (sp : Word) (a : Limbs)
    (next : lifted.Location) (frame : lifted.StackFrame) : Prop :=
  ∃ (args : Values Value Reg.count) (scratch : Ram),
    next = ⟨.l127d50, args, memStore scratch (sp - 8) (0x11a51c : Word)⟩ ∧
    frame = barrierContinuation ∧ BarrierArgs initial args sp a ∧
    memLoad scratch (sp + 0xb0) 64 = a[0] ∧ memLoad scratch (sp + 0xa8) 64 = a[1] ∧
    memLoad scratch (sp + 0x100) 64 = a[2] ∧
    ScratchWrites mem scratch sp compareWriteOffsets

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem compareBlock {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} {sp : Word}
    (a : Limbs) (hsp : args[4].get 64 = sp) (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2 ^ 32)
    (hcode : sp.toNat + 432 ≤ 0x11a14c ∨ 0x11a51c + 8 ≤ sp.toNat)
    (ha : WordsAt mem (sp + 40) 64 a) :
    CallTo (lifted := lifted) (CallsBarrier args mem sp a)
      (lifted.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩) := by
  have haddr : (sp - (8 : Word)).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase)
  lifted_registers [hsp]
  subst sp
  run_tac Lean.Elab.Tactic.withMainContext do
    let d ← Lean.Meta.getLocalDeclFromUserName `ha
    let _ ← Refine.Tactic.introAtoms d.fvarId "limb"
  final_product_block
  refine ⟨_, _, rfl, rfl, ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (lifted_word_reads [word0, word1, word2, word3, word4]; rfl)
    | final_product_frame

end K256.Proofs.Sec1.Sqrt.Finish
