import K256.Proofs.Ecdh.Decode.Packing.Guards
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Ecdh.Decode.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR

def pushedMemory (sp : BitVec 64) (regs : Values Value Reg.count) (m : Ram) : Ram :=
  memStore (memStore (memStore m (sp + 256) (regs[15].get 64))
    (sp + 248) (regs[14].get 64)) (sp + 240) (regs[3].get 64)

theorem pushedMemory_frame {code : CodeMap} {m : Ram} {sp : BitVec 64}
    (regs : Values Value Reg.count) (win : Writable code m (sp - 8) 272) :
    RamWriteFrame m (pushedMemory sp regs m) [window sp] := by
  unfold pushedMemory
  apply RamWriteFrame.memStore
  · apply RamWriteFrame.memStore
    · apply (RamWriteFrame.refl _ _).memStore
      exact stackRange win rfl (by decide)
    · exact stackRange win rfl (by decide)
  · exact stackRange win rfl (by decide)

set_option maxRecDepth 4096 in
theorem entryBlock {code : CodeMap} {regs : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {tag : BitVec 8}
    (hsp : regs[4].get 64 = sp + 264) (hsrc : regs[6].get 64 = src)
    (read : Readable m src 33) (win : Writable code m (sp - 8) 272)
    (apart : Outside [window sp] src 33)
    (head : memLoad m src 8 = tag)
    (valid : tag = 0 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (hc : ∀ x ∈ fnCode, x ∈ code) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l120f30, regs, m⟩ =
        .jump ⟨.l120f4b, args, pushedMemory sp regs m⟩ ∧
      args[0].get 64 = tag.zeroExtend 64 ∧
      args[3] = ⟨64, regs[7].get 64⟩ ∧ args[4].get 64 = sp ∧ args[6] = regs[6] ∧
      (∀ r ∈ [5, 8, 9, 12, 13, 15, 22, 39, 50, 51], ∀ hr : r < Reg.count, args[r] = regs[r]) := by
  have cover := fun x hx => hc x (code_l120f30 x hx)
  have frame := pushedMemory_frame regs win
  have lp : LoadOk (pushedMemory sp regs m) src 1 :=
    inputLoadBase (read.of_frame frame) (by decide)
  have value : memLoad (pushedMemory sp regs m) src 8 = tag :=
    (frame.memLoad_eq (show Outside [window sp] src (8 / 8) from
      ⟨by have := apart.1; omega, fun r hr => by rcases apart.2 r hr with l | r <;> omega⟩)).trans head
  have branch : (!( (cmpSpec (tag.zeroExtend 32) 5).CF ||
      (cmpSpec (tag.zeroExtend 32) 5).ZF)) = false := by
    rcases valid with rfl | rfl | rfl | rfl <;> decide +kernel
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, hsrc]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      refine stackStore (sp := sp) ?_ rfl (by decide) cover (by decide +kernel)
      repeat' apply Writable.memStore
      exact win)
    simp only [pushedMemory] at lp value
    rw [ite_eq_left lp, value, branch]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro r hr _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
theorem dispatchBlock {code : CodeMap} {regs : Values Value Reg.count} {m : Ram}
    {tag : BitVec 8} (rtag : regs[0].get 64 = tag.zeroExtend 64)
    (valid : tag = 0 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l120f4b, regs, m⟩ =
        .jump ⟨if tag = 0 then .l12105b else .l120f59, args, m⟩ ∧
      (∀ r ∈ [3, 4, 5, 6, 8, 9, 12, 13, 15, 22, 39, 50, 51],
        ∀ hr : r < Reg.count, args[r] = regs[r]) := by
  rcases valid with rfl | rfl | rfl | rfl <;>
    (refine ⟨?_, by cfg_eval [rtag]; rfl, ?_⟩
     intro r hr _
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

end K256.Proofs.Ecdh.Decode.Packing
