import K256.Proofs.Verify.Core.State
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

abbrev writes (fr : Activation) : List MemoryRegion :=
  [fr.region, ⟨fr.rdi.toNat, 16⟩]

theorem epilogue {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Saved fr b m)
    (wf : RamWriteFrame fr.original m (writes fr)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10537f, b, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = m ∧
      Atom.All Extracted.programImage out.values m (Fn104f20.doneAt fr) := by
  have entry := e.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at entry
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, retRead, ret, retLow, win, _⟩ := entry
  have area := win.of_frame wf
  have readable := retRead.of_frame wf
  have range := e.low
  have depth := e.stackRoom
  have bot : fr.low.toNat = fr.rsp.toNat - 12456 := by
    rw [e.stackBase, BitVec.toNat_sub_of_le (show (12456 : BitVec 64) ≤ fr.rsp from BitVec.le_def.mpr depth)]
    rfl
  have dst : fr.rdi.toNat = fr.rsp.toNat + 168 := by
    rw [e.dst, BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rsp.toNat + 168 < 2^64; omega)]
    rfl
  have ret' : memLoad m fr.rsp 64 = fr.ret := by
    rw [wf.memLoad_eq, ret]
    refine ⟨by change fr.rsp.toNat + 8 ≤ 2^64; omega, ?_⟩
    intro reg hm
    rcases List.mem_cons.mp hm with h | h
    · subst reg
      right
      change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
      omega
    · obtain rfl := List.mem_singleton.mp h
      left
      change fr.rsp.toNat + 8 ≤ fr.rdi.toNat
      omega
  have sp : b[4].get 64 = fr.rsp - 488 := congrArg (Value.get 64) h.sp
  obtain ⟨_, _, bp, df, mx, ft, fc, bx, r12, r13, r14, r15⟩ := h
  refine ⟨?_, .done ?run, ?tag, ?store, ?regs⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [sp, Lift.reduceAddOffset, BitVec.sub_add_cancel, bx, r12, r13, r14, r15, ret', retLow,
      and_true]
    simp (disch := slot_guard using code_l10537f) only [ite_eq_left]
    rfl
  case tag => rfl
  case store => rfl
  case regs => exact ⟨rfl, df, rfl, bp, rfl, rfl, rfl, rfl, mx, ft, fc, trivial⟩

end K256.Proofs.Verify.Core
