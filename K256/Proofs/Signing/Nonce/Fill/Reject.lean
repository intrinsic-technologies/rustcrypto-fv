import K256.Proofs.Signing.Nonce.Fill.Memory
import K256.Proofs.Verify.LIR.Fn100a40

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers Reaches)
open Initialize (State)

theorem reject {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (tested : Tested fr state a m) :
    ∃ b n, Reaches .l100dd3 a m .l100ab0 b n ∧ Head fr (retry state) b n := by
  obtain ⟨atoms, widths, bits, statePtr, valuePtr, writes⟩ := tested.toFrame
  have rsp : a[4] = ⟨64, sp fr⟩ := atoms.1
  have rspBits : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have count : a[13].get 64 = 32 := congrArg (Value.get 64) tested.r13
  have readSlot (off : Nat) (inside : off + 8 ≤ 232) :
      LoadOk m (sp fr + BitVec.ofNat 64 off) 8 := by
    have bottom : (fr.rsp - 2160).toNat = fr.rsp.toNat - 2160 := env.subNat 2160 (by decide)
    have localSp : (sp fr).toNat = fr.rsp.toNat - 232 := env.subNat 232 (by decide)
    have depth := env.depth
    have limit := env.limit
    have address : (sp fr + BitVec.ofNat 64 off).toNat = (sp fr).toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64),
        Nat.mod_eq_of_lt (by omega)]
    apply LoadOk.of_region tested.toFrame.stack.readable <;> omega
  have readState : LoadOk m (sp fr + 64) 8 := readSlot 64 (by decide)
  have readValue : LoadOk m (sp fr + 136) 8 := readSlot 136 (by decide)
  suffices ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l100dd3, a, m⟩ =
      .jump ⟨.l100ab0, b, m⟩ ∧ Head fr (retry state) b m by
    obtain ⟨b, run, head⟩ := this
    exact ⟨b, m, Semantics.Reaches.single (congrArg (Transfer.next _ []) run), head⟩
  refine ⟨?_, ?run, ?head⟩
  case run =>
    cfg_eval [rspBits, count, readState, readValue, statePtr, valuePtr]
    rfl
  case head =>
    refine ⟨⟨?_, ?_, bits, statePtr, valuePtr, writes⟩, tested.stateAt, rfl, rfl, rfl⟩
    · change Atom.All Extracted.programImage _ m (Fn100a40.frameAt .l100ac0 fr)
      simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at atoms ⊢
      exact atoms
    · rintro ⟨i, hi⟩ member
      have width := widths ⟨i, hi⟩ member
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact width
end K256.Proofs.Signing.Nonce.Fill
