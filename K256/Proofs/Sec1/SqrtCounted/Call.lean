import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Square
import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Widths
import K256.Proofs.Sec1.SqrtCounted.Types
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall

namespace K256.Proofs.Sec1.SqrtCounted

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open CFG Lift Refine Common.Field LIR Sqrt
open Serialize.Coordinates (callFrame reaches_call)

private def squareArgs (a : Vector Value Reg.count) (base : Word) : Vector Value Reg.count :=
  ((a.set 4 ⟨64, base - 8⟩).set 6 ⟨64, base⟩).set 7 ⟨64, base + 40⟩

private theorem enter (site : SquareLoop) {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {a : Values Value Reg.count} {m : Ram} {base : Word}
    (rsp : a[4].get 64 = base) (src : a[site.srcReg].get 64 = base)
    (dst : a[site.dstReg].get 64 = base + 40) (slot : Writable code m (base - 8) 8) :
    program.runBlock (dialect code) ⟨site.head, a, m⟩ =
      .call ⟨.l1145f0, squareArgs a base, memStore m (base - 8) (address site.resume)⟩
        (callFrame site.resume (address site.resume)) := by
  have hs : StoreOk code m (base - 8) 8 ((address site.head) + 6) 5 := by
    cases site
    · exact ParseSignature.storeOk_of_codeRange (off := 6) slot
        (fun e he => cover e (code_l118040 e he)) (by decide)
    · exact ParseSignature.storeOk_of_codeRange (off := 6) slot
        (fun e he => cover e (code_l1184d0 e he)) (by decide)
    · exact ParseSignature.storeOk_of_codeRange (off := 6) slot
        (fun e he => cover e (code_l118950 e he)) (by decide)
  cases site
  case' first44 =>
    change StoreOk code m (base - 8) 8 0x118046 5 at hs
    change a[15].get 64 = base at src
    change a[14].get 64 = base + 40 at dst
    change program.runBlock _ ⟨.l118040, _, _⟩ = _
  case' middle88 =>
    change StoreOk code m (base - 8) 8 0x1184d6 5 at hs
    change a[14].get 64 = base at src
    change a[3].get 64 = base + 40 at dst
    change program.runBlock _ ⟨.l1184d0, _, _⟩ = _
  case' last44 =>
    change StoreOk code m (base - 8) 8 0x118956 5 at hs
    change a[14].get 64 = base at src
    change a[3].get 64 = base + 40 at dst
    change program.runBlock _ ⟨.l118950, _, _⟩ = _
  all_goals
    cfg_eval [rsp, src, dst, hs]
    congr 2
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro i
    finite_cases i <;> simp only [squareArgs, Vector.getElem_set] <;> rfl

theorem call (site : SquareLoop) {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {a : Values Value Reg.count} {m : Ram} {base : Word} {w : Limbs}
    (rsp : a[4] = ⟨64, base⟩) (src : a[site.srcReg].get 64 = base)
    (dst : a[site.dstReg].get 64 = base + 40) (df : a[22] = ⟨1,0⟩)
    (widths : ∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15] → a[r].width = 64)
    (mxcsr : a[39].width = 32) (ftw : a[50].width = 16) (fcw : a[51].width = 16)
    (workspace : Writable code m (base - 112) 192) (room : 112 ≤ base.toNat)
    (align : base.toNat % 16 = 0)
    (apart : base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112)
    (input : WordsAt m base 64 w)
    (volatile : ∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → a[i].width = 64) :
    ∃ b m', Parser.Reaches code site.head a m site.resume b m' ∧
      b[4] = a[4] ∧ (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      WordsAt m' (base+40) 64 (squareWords w) ∧ RamWriteFrame m m' [roundStack base] ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → b[i].width = 64) := by
  let ret := address site.resume
  let child := squareArgs a base
  let cm := memStore m (base - 8) ret
  have unchanged (i : Fin Reg.count) (hi : i.val ∉ [4,6,7]) : child[i] = a[i] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [child, squareArgs, Ne.symm hi.1, Ne.symm hi.2.1, Ne.symm hi.2.2]
  have childWidths (i : Fin Reg.count)
      (hi : i.val ∈ ([1,2,8,9,3,5,12,13,14,15,39,50,51] : List Nat)) :
      child[i.val].width = (Reg.ofIndex i.val).width := by
    change (child[i]).width = _
    rw [unchanged i (by
      simp only [List.mem_cons,
        List.not_mem_nil, or_false] at hi ⊢
      omega)]
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact volatile 1 (by decide)
    · exact volatile 2 (by decide)
    · exact volatile 8 (by decide)
    · exact volatile 9 (by decide)
    · exact widths 3 (by decide)
    · exact widths 5 (by decide)
    · exact widths 12 (by decide)
    · exact widths 13 (by decide)
    · exact widths 14 (by decide)
    · exact widths 15 (by decide)
    · exact mxcsr
    · exact ftw
    · exact fcw
  have slot : Writable code m (base - 8) 8 :=
    workspace.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have input' : WordsAt cm base 64 w :=
    input.write_apart _ ret (RangeApart.of_offsets (addr_sub _ _) (addr_self base) (by decide))
  have hcall := enter site cover (congrArg (Value.get 64) rsp) src dst slot
  have argsOK : child[4] = ⟨64, base-8⟩ ∧ child[6] = ⟨64, base⟩ ∧ child[7] = ⟨64, base+40⟩ := by
    simp [child, squareArgs]
  let loc : LIR.lifted.Location := ⟨.l1145f0, child, cm⟩
  have entry : LiftedSquare.Entry code loc base ret w := {
    label := rfl, rsp := argsOK.1, rsi := argsOK.2.1, rdi := argsOK.2.2
    df := (unchanged 22 (by decide)).trans df
    widths := childWidths, workspace := workspace.memStore _ ret
    slot := memLoad_memStore_same _ _ _ (by decide) (by decide)
    retLow := by cases site <;> decide
    room := room, align := align, apart := apart, input := input' }
  obtain ⟨o, run, result⟩ := LiftedSquare.execute code entry
  have pushFrame : RamWriteFrame m cm [roundStack base] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have hs := toNat_of_offsets (addr_sub base 8) (addr_sub base 112) workspace.readable.low
      (n := 8) (by decide)
    rw [show ((0-8 : Word)-(0-112)).toNat = 104 by decide] at hs
    have bound := workspace.readable.low
    change (base-112).toNat ≤ (base-8).toNat ∧ (base-8).toNat+8 ≤ (base-112).toNat+192 ∧ _
    omega
  refine ⟨o.values, o.store, reaches_call hcall run result.tag, result.rsp.trans rsp.symm, ?_, result.output,
    pushFrame.trans result.frame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
    LiftedSquare.volatileWidths code loc rfl o run⟩
  intro i hi
  apply Eq.trans (result.saved i hi) (unchanged i ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
  omega

end K256.Proofs.Sec1.SqrtCounted
