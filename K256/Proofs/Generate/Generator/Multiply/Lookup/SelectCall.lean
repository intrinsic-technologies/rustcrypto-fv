import K256.Proofs.Generate.Generator.Multiply.Lookup.Select
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field

theorem resumeSelect {l next : Label} {a b : Registers} {initial m : Ram}
    {sp ret left right dst : Word} {p q : Projective} (choose : Bool)
    (call : program.runBlock (dialect Extracted.programImage) ⟨l, a, initial⟩ =
      .call ⟨.l10fcc0, b, memStore m (sp - 8) ret⟩ (callFrame next ret))
    (rsp : b[4].get 64 = sp - 8) (rsi : b[6].get 64 = left) (rdx : b[2].get 64 = right)
    (rdi : b[7].get 64 = dst) (width : b[7].width = 64)
    (flag : (b[1].get 64).setWidth 8 = if choose then 1 else 0)
    (stack : Writable Extracted.programImage m (sp - 88) 88) (room : 88 ≤ sp.toNat)
    (retLow : ret.toNat < 2^32) (srcL : Readable m left 120) (srcR : Readable m right 120)
    (target : Writable Extracted.programImage m dst 120)
    (aboveL : sp.toNat ≤ left.toNat) (aboveR : sp.toNat ≤ right.toNat) (aboveD : sp.toNat ≤ dst.toNat)
    (pointL : p.Stored m left) (pointR : q.Stored m right) :
    ∃ c n, Reaches l a initial next c n ∧ c[4] = ⟨64,sp⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i] = ⟨64, b[i].get 64⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      ParseSignature.ArgumentWidths c ∧ (if choose then q else p).Stored n dst ∧
      RamWriteFrame m n [⟨(sp - 88).toNat,88⟩, ⟨dst.toNat,120⟩] := by
  let pushed := memStore m (sp - 8) ret
  have sub (k : Word) (hk : k.toNat ≤ 88) :
      (sp - k).toNat = sp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans hk room))
  have childBase : sp - 8 - 80 = sp - 88 := by bv_omega
  have pushAddr : (sp - 8).toNat = sp.toNat - 8 := sub 8 (by decide)
  have baseAddr : (sp - 88).toNat = sp.toNat - 88 := sub 88 (by decide)
  have win : Writable Extracted.programImage pushed (sp - 8 - 80) 80 := by
    rw [childBase]
    exact (stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)).memStore _ ret
  have retRead : Readable pushed (sp - 8) 8 :=
    (stack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)).memStore _ ret
  have tag := memLoad_memStore_same m (sp - 8) ret (by decide) (by decide)
  let sl : MemoryRegion := ⟨(sp - 8).toNat,8⟩
  have pushFrame : RamWriteFrame m pushed [sl] := by
    have high := stack.readable.low
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, ?_⟩
    change (sp - 8).toNat + 8 ≤ 2^64
    omega
  have outside {v : Word} (rv : Readable m v 120) (above : sp.toNat ≤ v.toNat) :
      Outside [sl] v 120 := by
    obtain ⟨low, _⟩ := rv
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [sl]
    omega
  obtain ⟨out, block, outTag, back, saved, kept, widths, frame, words⟩ :=
    selectBlock choose flag width rsp rsi rdx rdi win (srcL.of_frame pushFrame)
      (srcR.of_frame pushFrame) (target.of_frame pushFrame) (by omega) (by omega)
      (by omega) (by omega) retRead tag retLow
  have run : program.Exec (dialect Extracted.programImage) ⟨⟨.l10fcc0,b,pushed⟩,[]⟩ out :=
    .done (by simp only [Program.step, block, Transfer.next, pushed])
  refine ⟨_, _, Sample.reachesAfterSampleCall call run outTag [], ?_, saved, kept, widths, ?_, ?_⟩
  · simpa only [BitVec.sub_add_cancel] using back
  · have s : (if choose then q else p).Stored pushed (if choose then right else left) := by
      cases choose
      · exact pointL.of_frame pushFrame (outside srcL aboveL)
      · exact pointR.of_frame pushFrame (outside srcR aboveR)
    apply s.of_word_copy
    intro i
    simpa only [sourceWords, Vector.getElem_ofFn] using words i.val i.isLt
  · let areas : List MemoryRegion := [⟨(sp - 88).toNat,88⟩,⟨dst.toNat,120⟩]
    have f : RamWriteFrame m pushed areas :=
      (RamWriteFrame.refl _ _).trans pushFrame (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> dsimp only [sl] <;> omega)
    apply f.trans frame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, childBase] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, by dsimp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply.Lookup
