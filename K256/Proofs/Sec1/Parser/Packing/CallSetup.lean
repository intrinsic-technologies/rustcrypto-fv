import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def memsetResume : StackFrame Value Label signature Reg.count :=
  { target := .l106409, kept := #v[], arity := rfl, guard := some ⟨64, 0x106409⟩ }

def memcpyResume : StackFrame Value Label signature Reg.count :=
  { target := .l10641d, kept := #v[], arity := rfl, guard := some ⟨64, 0x10641d⟩ }

variable {code : CodeMap} {regs : Values Value Reg.count} {m : Ram}

theorem memsetCallStoreOk {sp : BitVec 64} (slot : Writable code m (sp - 8) 8)
    (hc : ∀ x ∈ fnCode, x ∈ code) : StoreOk code m (sp - 8) 8 0x106403 6 :=
  ParseSignature.storeOk_of_codeRange (off := 49) slot
    (fun x hx => hc x (code_l1063d2 x hx)) (by decide)

theorem memcpyCallStoreOk {sp : BitVec 64} (slot : Writable code m (sp - 8) 8)
    (hc : ∀ x ∈ fnCode, x ∈ code) : StoreOk code m (sp - 8) 8 0x106417 6 :=
  ParseSignature.storeOk_of_codeRange (off := 14) slot
    (fun x hx => hc x (code_l106409 x hx)) (by decide)

theorem callReturnStoreFrame {slot pc ret : BitVec 64} {len : Nat}
    (hw : StoreOk code m slot 8 pc len) :
    RamWriteFrame m (memStore m slot ret) [⟨slot.toNat, 8⟩] := by
  apply (RamWriteFrame.refl _ _).memStore
  exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by have := hw.low; omega⟩

set_option maxRecDepth 4096 in
theorem memsetCall (sp src dst n : BitVec 64)
    (hsp : regs[4].get 64 = sp) (hsrc : regs[6].get 64 = src)
    (hdst : regs[7].get 64 = dst) (hlen : regs[2].get 64 = n)
    (hsizes : n = 1 ∨ n = 33 ∨ n = 65)
    (hstore : StoreOk code m (sp - 8) 8 0x106403 6)
    (hgot : LoadOk m 0x203e10 8) (htarget : memLoad m 0x203e10 64 = 0x12a700) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l1063d2, regs, m⟩ =
        .call ⟨.l12a700, args, memStore m (sp - 8) (0x106409 : BitVec 64)⟩ memsetResume ∧
      args[2] = ⟨64, 65 - n⟩ ∧ args[3] = ⟨64, src⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧
      args[6] = ⟨64, 0⟩ ∧ args[7] = ⟨64, sp + 160 + n⟩ ∧ args[12] = ⟨64, 0⟩ ∧
      args[14] = ⟨64, n⟩ ∧ args[15] = ⟨64, dst⟩ ∧
      (∀ r ∈ [5, 9, 10, 11, 13, 22, 39, 50, 51], ∀ hr : r < Reg.count, args[r] = regs[r]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, hsrc, hdst, hlen, hstore, hgot, htarget]
    rfl
  case post =>
    refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
    · change (⟨64, if (cmpSpec n 65).CF = true then 65 - n else 0⟩ : Value) = ⟨64, 65 - n⟩
      congr 1
      rcases hsizes with rfl | rfl | rfl <;> decide +kernel
    · change (⟨64, sp + n + 160⟩ : Value) = ⟨64, sp + 160 + n⟩
      congr 1
      bv_omega
    · intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem memcpyCall (sp src n : BitVec 64)
    (hsp : regs[4].get 64 = sp) (hsrc : regs[3].get 64 = src) (hlen : regs[14].get 64 = n)
    (hstore : StoreOk code m (sp - 8) 8 0x106417 6)
    (hgot : LoadOk m 0x203dd0 8) (htarget : memLoad m 0x203dd0 64 = 0x12a820) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l106409, regs, m⟩ =
        .call ⟨.l12a820, args, memStore m (sp - 8) (0x10641d : BitVec 64)⟩ memcpyResume ∧
      args[2] = ⟨64, n⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧ args[6] = ⟨64, src⟩ ∧
      args[7] = ⟨64, sp + 160⟩ ∧
      (∀ r ∈ [3, 5, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51], ∀ hr : r < Reg.count,
        args[r] = regs[r]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, hsrc, hlen, hstore, hgot, htarget]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro r hr _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Parser.Packing
