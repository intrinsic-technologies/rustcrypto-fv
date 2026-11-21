import K256.Proofs.ParseSignature.Pair.Frame
import K256.Proofs.ParseSignature.Compare
import K256.Proofs.ParseSignature.BlackBox

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

abbrev zeroChild (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (ret : BitVec 64) :=
  withArguments { fr with
    original := mem, rsp := sp fr - 8, low := sp fr - 9,
    ret := ret, rbx := fr.rdi, r14 := fr.rsi } args

abbrev pairLimbs (fr : Activation) (mem : Ram) :=
  scalarLimbsAt mem (sp fr + 104) fr.original fr.rsi ∧
  scalarLimbsAt mem (sp fr + 136) fr.original (fr.rsi + 32)

theorem activeOfZeroReturn {code : CodeMap} {fr : Activation} {ret : BitVec 64}
    {args regs next : Values Value Reg.count} {pushed after : Ram}
    (active : Active code fr false args after)
    (done : Atom.All code next after (Fn127f50.frameInfo.doneAtoms (zeroChild fr regs pushed ret)))
    (widths : ArgumentWidths next) : Active code fr false next after := by
  have h := active.atoms
  change Atom.All code args after (Fn103ac0.frameAt .l103b80 fr) at h
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, savedBx, saved14, readRet,
    loadRet, lowRet, stack, room, align, _⟩
  change next[4] = ⟨64, sp fr - 8 + 8⟩ ∧ next[22] = ⟨1, 0⟩ ∧ next[3] = ⟨64, fr.rdi⟩ ∧
    next[5] = ⟨64, fr.rbp⟩ ∧ next[12] = ⟨64, fr.r12⟩ ∧ next[13] = ⟨64, fr.r13⟩ ∧
    next[14] = ⟨64, fr.rsi⟩ ∧ next[15] = ⟨64, fr.r15⟩ ∧ next[39] = ⟨32, fr.mxcsr⟩ ∧
    next[50] = ⟨16, fr.ftw⟩ ∧ next[51] = ⟨16, fr.fcw⟩ ∧ True at done
  rw [BitVec.sub_add_cancel] at done
  rcases done with ⟨rsp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, _⟩
  exact ⟨⟨rsp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, savedBx, saved14,
    readRet, loadRet, lowRet, stack, room, align, trivial⟩, active.writes, widths⟩

theorem Active.ofScratchFrame {code : CodeMap} {fr : Activation} {args : Values Value Reg.count}
    {mem after : Ram} {regions : List MemoryRegion} (active : Active code fr false args mem)
    (writes : RamWriteFrame mem after regions)
    (bounds : ∀ r ∈ regions, fr.low.toNat ≤ r.start ∧ r.start + r.size ≤ (fr.rsp - 16).toNat) :
    Active code fr false args after := by
  have h := active.atoms
  change Atom.All code args mem (Fn103ac0.frameAt .l103b80 fr) at h
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at h
  rcases h with ⟨rsp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, savedBx, saved14,
    readRet, loadRet, lowRet, stack, room, align, _⟩
  have low := readRet.low
  have saved (addr : BitVec 64) (start : (fr.rsp - 16).toNat ≤ addr.toNat)
      (endBound : addr.toNat ≤ fr.rsp.toNat) : memLoad after addr 64 = memLoad mem addr 64 := by
    apply writes.memLoad_eq
    exact ⟨by change addr.toNat + 8 ≤ 2^64; omega,
      fun r hr => Or.inr (Nat.le_trans (bounds r hr).2 start)⟩
  have last16 := stackSub_toNat room 16 (by decide)
  have last8 := stackSub_toNat room 8 (by decide)
  change (fr.rsp - 16).toNat = _ at last16
  change (fr.rsp - 8).toNat = _ at last8
  refine ⟨⟨rsp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw,
    (saved _ (by omega) (by omega)).trans savedBx,
    (saved _ (by omega) (by omega)).trans saved14, readRet.of_frame writes,
    (saved _ (by omega) (by omega)).trans loadRet, lowRet, stack.of_frame writes,
    room, align, trivial⟩, active.writes.trans writes ?_, active.widths⟩
  intro r hr
  obtain ⟨lo, hi⟩ := bounds r hr
  exact ⟨fr.region, by simp, lo, by change r.start + r.size ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat); omega⟩

theorem pairLimbs_of_frame {code : CodeMap} {fr : Activation} {args : Values Value Reg.count}
    {mem after : Ram} {regions : List MemoryRegion} (active : Active code fr false args mem)
    (limbs : pairLimbs fr mem) (writes : RamWriteFrame mem after regions)
    (below : ∀ r ∈ regions, r.start + r.size ≤ (sp fr + 104).toNat) : pairLimbs fr after := by
  have h := active.atoms
  change Atom.All code args mem (Fn103ac0.frameAt .l103b80 fr) at h
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, room, _, _⟩ := h
  have unchanged (offset : BitVec 64) (off : offset = 104 ∨ offset = 136) (i : Nat) (hi : i < 4) :
      memLoad after (wordAddr (sp fr + offset) 64 i) 64 =
        memLoad mem (wordAddr (sp fr + offset) 64 i) 64 := by
    apply writes.memLoad_eq
    have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have addr : (sp fr + 104).toNat ≤ (wordAddr (sp fr + offset) 64 i).toNat ∧
        (wordAddr (sp fr + offset) 64 i).toNat + 8 ≤ 2^64 := by
      rcases off with rfl | rfl <;> rcases index with rfl | rfl | rfl | rfl <;>
        unfold wordAddr sp <;> bv_omega
    exact ⟨addr.2, fun r hr => Or.inr (Nat.le_trans (below r hr) addr.1)⟩
  exact ⟨fun i hi => (unchanged 104 (.inl rfl) i hi).trans (limbs.1 i hi),
    fun i hi => (unchanged 136 (.inr rfl) i hi).trans (limbs.2 i hi)⟩

end K256.Proofs.ParseSignature.Pair
