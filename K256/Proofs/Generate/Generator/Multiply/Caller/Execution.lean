import K256.Proofs.Generate.Generator.Multiply.Core
import K256.Proofs.Generate.Generator.Multiply.Caller.CopyMemory
import K256.Proofs.Generate.Generator.Multiply.Caller.ReturnFrame

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters

open Caller

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
theorem caller (core : type_of% @coreExecution) {fr : Activation} {a : Values Value Reg.count} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32)
    (src : fr.rsi = fr.rsp + 8) (dst : fr.rdi = fr.rsp + 232)
    (source : Readable fr.original fr.rsi 32)
    (destination : Writable Extracted.programImage fr.original fr.rdi 120)
    (words : WordsAt fr.original fr.rsi 64
      (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))))
    (pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ b m, Reaches .l10ee80 a fr.original .l10f12f b m ∧
      Atom.All Extracted.programImage b m (Fn10ee80.frameAt .l10f12f fr) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → b[i].width = 64) ∧
      RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat, 120⟩] ∧
      Affine.ProjectiveAt m fr.rdi (Curve.generatorWindow d) := by
  let sp := localSp fr
  let m₁ := firstCopyMemory fr
  let m₂ := secondCopyMemory m₁ sp
  let m₃ := tableCopyMemory m₂ sp
  let m₄ := coreCallMemory m₃ sp
  have initial := atoms
  simp only [Fn10ee80.frameAt,Fn10ee80.frameAtG1,Atom.All,Atom.Holds] at initial
  obtain ⟨_,df,_,_,_,bp,_,_,_,_,_,_,_,_,mx,ft,fc,_,_,_,stack,_⟩ := initial
  have window : Writable Extracted.programImage fr.original (sp - 8) 5928 :=
    stack.of_offsets (x := fr.rsp) (c := 0 - 5968) (by unfold sp localSp; bv_omega)
      (addr_sub fr.rsp 9768) (by decide)
  obtain ⟨b,p,bsp,b3,b13,b14,bkeep⟩ := firstCopy atoms image src source
  have w₁ : RamWriteFrame fr.original m₁ [fr.region] := firstCopyFrame room low
  have w₂ : RamWriteFrame fr.original m₂ [fr.region] := secondCopyFrame room low w₁
  have w₄ : RamWriteFrame fr.original m₄ [fr.region] := tableCoreFrame room low w₂
  have bdf := (bkeep 22 (by decide)).trans df
  obtain ⟨c,q,csp,c12,c15,ckeep⟩ := secondCopy
    ((window.of_frame w₁).sub (Nat.le_refl _) (by omega))
    (callerImage room low stack w₁ image) (congrArg (Value.get 64) bsp)
    (congrArg (Value.get 64) b13) (congrArg (Value.get 1) bdf)
  have c13 := (ckeep 13 (by decide) (by decide) (by decide)).trans b13
  have cdf := (ckeep 22 (by decide) (by decide) (by decide)).trans bdf
  obtain ⟨e,r,esp,e15,ekeep⟩ := tableCopies (window.of_frame w₂) (congrArg (Value.get 64) csp)
    (congrArg (Value.get 64) c13) (congrArg (Value.get 64) c15) (congrArg (Value.get 64) c12)
    (congrArg (Value.get 1) cdf)
  have window₃ : Writable Extracted.programImage m₃ (sp - 8) 82 := by
    have w := (window.of_frame w₂).sub (Nat.le_refl _) (show (sp-8).toNat + 82 ≤ (sp-8).toNat + 5928 by omega)
    unfold m₃ tableCopyMemory memCopy
    iterate 4 apply Writable.memStore
    exact w
  obtain ⟨u,call,usp,u1,u2,u6,u7,u8,u9,uk⟩ := coreCall (congrArg (Value.get 64) esp) window₃
  have saved (i : Fin Reg.count) (hi : i.val ∈ [3,5,13,14,22,39,50,51]) : e[i] = b[i] := by
    apply (ekeep i ?_ ?_).trans (ckeep i ?_ ?_ ?_)
    all_goals simp only [memcpyPreserved,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢ <;> omega
  have e3 := (saved 3 (by decide)).trans b3
  have e14 := (saved 14 (by decide)).trans b14
  obtain ⟨generator,scalar,s3,s12,s13,s14,s15⟩ := callerMemoryFacts (d := d) atoms image room low words
  have slots := coreCallSlots m₃ sp
  have entry : CoreEntry (coreActivation fr m₄) u d := by
    apply makeCoreEntry atoms image room low high dst destination w₄ ?_ slots.1 slots.2 generator scalar
    simp only [Atom.All,Atom.Holds]
    refine ⟨usp,?_,?_,u2,?_,?_,?_,?_,u8,u9,?_,?_,?_,?_,?_,?_,?_,trivial⟩
    · exact (uk 22 (by decide)).trans ((saved 22 (by decide)).trans bdf)
    · exact u1.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) e15)
    · exact (uk 3 (by decide)).trans e3
    · exact (uk 5 (by decide)).trans ((saved 5 (by decide)).trans ((bkeep 5 (by decide)).trans bp))
    · exact u6.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) e14)
    · exact u7.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) e3)
    · exact (uk 12 (by decide)).trans ((ekeep 12 (by decide) (by decide)).trans c12)
    · exact (uk 13 (by decide)).trans ((saved 13 (by decide)).trans b13)
    · exact (uk 14 (by decide)).trans e14
    · exact (uk 15 (by decide)).trans e15
    · exact (uk 39 (by decide)).trans ((saved 39 (by decide)).trans ((bkeep 39 (by decide)).trans mx))
    · exact (uk 50 (by decide)).trans ((saved 50 (by decide)).trans ((bkeep 50 (by decide)).trans ft))
    · exact (uk 51 (by decide)).trans ((saved 51 (by decide)).trans ((bkeep 51 (by decide)).trans fc))
  obtain ⟨out,exec,result⟩ := core entry pos bound
  have finish := Sample.reachesAfterSampleCall call exec result.1 []
  exact ⟨out.values,out.store,((p.trans q).trans r).trans finish,
    afterCore atoms room low high dst w₄ s3 s12 s13 s14 s15 result⟩

end K256.Proofs.Generate.Generator.Multiply
