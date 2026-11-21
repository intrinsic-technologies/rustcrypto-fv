import K256.Proofs.Sec1.Parser.Packing.Rearrange
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.ParseSignature.Fill.Blocks

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

def affineResume : StackFrame Value Label signature Reg.count :=
  { target := .l1064f4, kept := #v[], arity := rfl, guard := some ⟨64, 0x1064f4⟩ }

private theorem loadGuard {sp off : BitVec 64} {code : CodeMap} {m : Ram} {n : Nat}
    (win : Writable code m (sp - 8) 233) (h : (off - (-8)).toNat + n ≤ 233) :
    LoadOk m (sp + off) n :=
  LoadOk.of_offsets win.readable rfl (addr_sub _ _) h

private theorem storeGuard {sp addr off : BitVec 64} {code : CodeMap} {m : Ram}
    {pc : BitVec 64} {n ins : Nat}
    (win : Writable code m (sp - 8) 233)
    (ha : addr = sp + off) (h : (off - (-8)).toNat + n ≤ 233)
    (hc : ∀ x ∈ codeRange 0x10641d bytes_l10641d, x ∈ code)
    (within : (pc - 0x10641d).toNat + ins ≤ bytes_l10641d.length) :
    StoreOk code m addr n pc ins := by
  have hw := win.of_offsets ha (addr_sub _ _) h
  have hg := K256.Proofs.ParseSignature.storeOk_of_codeRange hw hc within
  have e : (0x10641d : BitVec 64) + BitVec.ofNat 64 (pc - 0x10641d).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [e] at hg

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem affineCall {code : CodeMap} (regs : Values Value Reg.count) (m : Ram) (sp : BitVec 64)
    (hsp : regs[4].get 64 = sp) (win : Writable code m (sp - 8) 233)
    (hc : ∀ x ∈ fnCode, x ∈ code) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l10641d, regs, m⟩ =
        .call ⟨.l121480, args, affineMemory sp m⟩ affineResume ∧
      args[3] = ⟨64, sp + 160⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧
      args[6] = ⟨64, sp + 4⟩ ∧ args[7] = ⟨64, sp + 160⟩ ∧
      (∀ r ∈ [5, 12, 13, 14, 15, 22, 39, 50, 51], ∀ hr : r < Reg.count,
        args[r] = regs[r]) := by
  have cover := fun x hx => hc x (code_l10641d x hx)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | apply loadGuard (code := code) (sp := sp)
          · repeat' apply Writable.memStore
            exact win
          · decide
        | refine storeGuard (sp := sp) ?_ rfl ?_ cover ?_
          · repeat' apply Writable.memStore
            exact win
          · decide
          · decide +kernel
        | refine storeGuard (sp := sp) (off := 0 - 8) ?_ (addr_sub _ _) ?_ cover ?_
          · repeat' apply Writable.memStore
            exact win
          · decide
          · decide +kernel)
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro r hr _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Parser.Packing
