import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def windowLabel (count : BitVec 64) : Label :=
  if count = 0 then .l11f6c4 else .l11d7ef

theorem windowCountdown {fr : Activation} {a : Registers} {m : Ram} {count pointer : BitVec 64}
    (atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d7d0 fr))
    (countSlot : memLoad m (fr.rsp - 0xa68) 64 = count + 1)
    (digitSlot : memLoad m (fr.rsp - 0xbc8) 64 = pointer + 1)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a) :
    ∃ b, Reaches .l11d7d0 a m (windowLabel count) b m ∧
      Atom.All Extracted.programImage b m (Fn11c880.frameAt (windowLabel count) fr) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
      b[1] = ⟨64, count⟩ ∧ b[2] = ⟨64, pointer⟩ ∧ b[12] = a[12] := by
  have branch (l r : Label) (v : Registers) (h : Prop) [Decidable h] :
      (if h then Transfer.jump (signature := signature) (results := Reg.count) ⟨l, v, m⟩ else .jump ⟨r, v, m⟩) =
        .jump ⟨if h then l else r, v, m⟩ := by
      let jump (k : Label) : Transfer Value Ram Label signature Reg.count := .jump ⟨k,v,m⟩
      change (if h then jump l else jump r) = jump (if h then l else r)
      split <;> simp_all
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  have rsp : a[4].get 64 = fr.rsp - 0xcb8 := congrArg (Value.get 64) atoms.1
  have stack := atoms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have countOk : LoadOk m (fr.rsp - 0xa68) 8 := by slot_guard using code_l11d7d0
  have digitOk : LoadOk m (fr.rsp - 0xbc8) 8 := by slot_guard using code_l11d7d0
  refine ⟨?b, ?path, ?atoms, ?arg, ?saved, ?cx, ?dx, ?r12⟩
  case path =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11d7d0, a, m⟩ =
        .jump ⟨windowLabel count, ?b, m⟩ := by
      generate_block [rsp, countOk, digitOk, countSlot, digitSlot, BitVec.add_sub_cancel, BitVec.and_self, show (testFlags count).ZF.getD false = (count == 0) from rfl, beq_iff_eq]
      exact branch _ _ _ (count = 0)
    apply Semantics.Reaches.single
    change program.step _ _ = _
    simp only [Program.step, run, Transfer.next]
  case atoms =>
    by_cases h : count = 0 <;>
      simp only [windowLabel, h, ↓reduceIte, Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All,
        Atom.Holds]
    · obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,_⟩ := atoms
      exact ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,trivial⟩
    · exact atoms
  case arg =>
    rintro ⟨i, hi⟩ hm
    have w := widths ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact w
  case saved =>
    rintro ⟨i, hi⟩ hm
    have w := saved ⟨i, hi⟩ hm
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact w
  all_goals rfl

end K256.Proofs.Generate.Generator.Multiply
