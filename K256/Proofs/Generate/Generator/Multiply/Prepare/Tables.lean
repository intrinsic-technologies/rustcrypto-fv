import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Signed
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Second
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Ready

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Prepare

open Table

set_option linter.unusedVariables false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem prepareTables (add : type_of% @addCall) {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr initial d) (pos : 0 < d) (bound : d < domain.n)
    (s : BasesReady fr a m d) :
    ∃ b n, Reaches .l11cf0d a m .l11d546 b n ∧ TablesReady fr b n d := by
  obtain ⟨p,v,base,pv⟩ := s.firstBaseStored
  obtain ⟨t,valid,endo,tv⟩ := s.endomorphismStored
  obtain ⟨rsp,df,_⟩ := Accumulator.currentStack s.toState rfl
  have args : Inputs true 0 (sp fr) a := ⟨congrArg (Value.get 64) rsp,congrArg (Value.get 1) df,
    congrArg (Value.get 64) s.basePtr,congrArg (Value.get 64) s.workPtr,by simp,by omega⟩
  obtain ⟨b,n,r,sb,inputs,tab,f,save⟩ := buildTable add true entry s.toState args v base 7 (by decide)
  have wide : RamWriteFrame m n (Bases.writes fr scratchSpans) :=
    (RamWriteFrame.refl _ _).trans f (inductionWithin true fr)
  obtain ⟨c,o,r',sc,first,point,c3,c12,c14,c15,delta⟩ :=
    selectSecondBase entry sb tab (endo.of_frame wide (Bases.outside entry scratchSpans (i := 688) (by decide) (by decide)))
      (congrArg (Value.get 64) ((save 3 (by decide)).trans s.mask4)) (congrArg (Value.get 64) ((save 12 (by decide)).trans s.mask52))
      (congrArg (Value.get 64) ((save 14 (by decide)).trans s.mask48)) inputs.base inputs.work (inputs.temp (by decide))
      ((wide.memLoad_eq (Bases.outside entry scratchSpans (i := 8) (by decide) (by decide))).trans (s.extra (8,0) (by simp)))
      ((wide.memLoad_eq (Bases.outside entry scratchSpans (i := 72) (by decide) (by decide))).trans s.sign)
  have full := wide.trans delta (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  let signed := if secondComponent d < 0 then t.neg else t
  have sv : signed.valid := by unfold signed; split <;> first | exact Projective.neg_valid valid | exact valid
  have value : signed.value = secondBase d := by
    unfold signed secondBase Curve.signedBase
    split <;> simp only [tv,Projective.neg_value]
  have lim := (full.memLoad_eq (Bases.outside entry scratchSpans (i := 104) (by decide) (by decide))).trans
    (s.extra (104,152) (by simp))
  obtain ⟨b',n',r'',sb',ft,st,b12,b13,b14,b15,finish⟩ :=
    buildSecond add entry sc sv point (pv ▸ first) c3 c12 c14 c15 lim
  have final := full.trans finish (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have mag : Magnitudes fr n' d := ⟨WordsAt.of_frame s.first final (by decide)
    (Bases.outside entry scratchSpans (i := 624) (by decide) (by decide)),
    WordsAt.of_frame s.second final (by decide) (Bases.outside entry scratchSpans (i := 656) (by decide) (by decide))⟩
  have ptr := (final.memLoad_eq (Bases.outside entry scratchSpans (i := 216) (by decide) (by decide))).trans
    (s.extra (216,fr.rcx) (by simp))
  have extra : Locals fr n' [(0x60,66),(0x88,152),(0xc0,0)] := by
    intro kv h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl
    · exact (final.memLoad_eq (Bases.outside entry scratchSpans (i := 96) (n := 8) (by decide) (by decide))).trans (s.extra _ (by simp))
    · exact (final.memLoad_eq (Bases.outside entry scratchSpans (i := 136) (n := 8) (by decide) (by decide))).trans (s.extra _ (by simp))
    · exact (final.memLoad_eq (Bases.outside entry scratchSpans (i := 192) (n := 8) (by decide) (by decide))).trans (s.extra _ (by simp))
  obtain ⟨c',o',endRun,post⟩ := exportTables entry sb' ft (value ▸ st) ptr mag extra b12 b13 b14 b15
  exact ⟨c',o',r.trans (r'.trans (r''.trans endRun)),post⟩

end Prepare

end K256.Proofs.Generate.Generator.Multiply
