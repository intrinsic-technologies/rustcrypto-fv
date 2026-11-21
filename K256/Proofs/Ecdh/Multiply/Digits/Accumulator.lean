import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
import K256.Proofs.Ecdh.Multiply.Digits.CopyTables

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Prepare

open Accumulator

local macro "generator_accumulator%" name:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
    (`K256.Proofs.Generate.Generator.Multiply.Prepare ++ name.getId)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 380000 in
theorem peerPrepareAccumulator (select : type_of% @lookup) (add : type_of% @addCall) {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (_pos : 0 < d) (bound : d < domain.n)
    (s : PeerDigitsReady fr a m d peer) :
    ∃ b n, Reaches .l11d620 a m .l11d748 b n ∧ PeerPrepared fr b n d peer := by
  have addr : sp fr + 0x128 = fr.rsp - 0xb90 := by
    unfold sp
    bv_omega
  obtain ⟨b,n,init,st,left,right,ident,limit,frame,b5,b12,b14,b15⟩ := peerCopyTables entry s
  let x := (firstComponent d).natAbs
  let y := (secondComponent d).natAbs
  obtain ⟨bx,hx⟩ := (generator_accumulator% topDigit) (Curve.split_correct d bound).2.1
  obtain ⟨by',hy⟩ := (generator_accumulator% topDigit) (Curve.split_correct d bound).2.2
  have firstByte := (generator_accumulator% lastByte) s.firstDigits
  have secondByte := (generator_accumulator% lastByte) s.secondDigits
  rw [show fr.r9 + 33 + 32 = fr.r9 + 65 by rw [BitVec.add_assoc]; rfl] at secondByte
  have access {l : Label} {v : Registers} {mem : Ram} (st : State l fr v mem)
      (layout : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr) :
      v[4].get 64 = sp fr ∧ Writable Extracted.programImage mem (sp fr - 8) 8 ∧
      Readable mem (sp fr + 0xf0) 8 := by
    obtain ⟨top,_,win⟩ := currentStack st layout
    exact ⟨congrArg (Value.get 64) top,win.sub (by peer_acc_bounds using entry) (by peer_acc_bounds using entry),
      win.readable.sub (by peer_acc_bounds using entry) (by peer_acc_bounds using entry)⟩
  obtain ⟨top₁,slot₁,ptrRead⟩ := access st rfl
  obtain ⟨c,c₁,ptr,di,si,idx,kc⟩ := firstLookupBlock top₁ slot₁ st.widths st.savedWidths b5 b12 b14
    (st.locals (0xf0,fr.r9) (by simp)) ptrRead
    ((frame.memLoad_eq (by peer_acc_bounds using entry)).trans firstByte)
    ((entry.digitWrite.of_frame st.frame).readable.sub (by peer_acc_bounds using entry) (by peer_acc_bounds using entry))
  have index₁ : (c[2].get 64).setWidth 8 = BitVec.ofInt 8 (Curve.radixRemaining x 32) := by
    rw [idx,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq]; exact bx
  obtain ⟨v,o,t,path₁,st₁,tv,ts,te,f₁,kv⟩ := peerPointLookup (r := .l11d6eb) select true entry st rfl rfl c₁
    (by decide) di si index₁ hx left
  have id₁ := ident.of_frame f₁ (by peer_acc_call_bounds using entry)
  obtain ⟨top₂,slot₂,_⟩ := access st₁ rfl
  have gp₁ (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,14,15]) : v[i].get 64 = b[i].get 64 :=
    congrArg (Value.get 64) ((kv i (by simp only [Sample.nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (kc i hi))
  obtain ⟨e,c₂,accPtr,di₂,si₂,ke⟩ := firstAddBlock top₂ slot₂ st₁.widths st₁.savedWidths
    ((gp₁ 12 (by decide)).trans b12)
  obtain ⟨u,z,path₂,st₂,sum₁,f₂,ku⟩ := peerPointAdd (r := .l11d6fe) add entry st₁ rfl rfl c₂ (by decide) di₂ si₂ id₁ ts
  have gp₂ (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,15]) : u[i].get 64 = v[i].get 64 :=
    congrArg (Value.get 64) ((ku i (by simp only [Sample.nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (ke i hi))
  have f' := (frame.trans f₁ (by peer_acc_call_bounds using entry)).trans f₂ (by peer_acc_call_bounds using entry)
  obtain ⟨top₃,slot₃,_⟩ := access st₂ rfl
  obtain ⟨g,c₃,di₃,si₃,idx₃,kg⟩ := secondLookupBlock top₃ slot₃ st₂.widths st₂.savedWidths
    ((gp₂ 5 (by decide)).trans ((gp₁ 5 (by decide)).trans b5))
    ((gp₂ 12 (by decide)).trans ((gp₁ 12 (by decide)).trans b12))
    ((gp₂ 15 (by decide)).trans ((gp₁ 15 (by decide)).trans b15))
    ((gp₂ 3 (by decide)).trans ((congrArg (Value.get 64) (kv 3 (by decide))).trans ptr))
    ((f'.memLoad_eq (by peer_acc_bounds using entry)).trans secondByte)
    ((entry.digitWrite.of_frame st₂.frame).readable.sub (by peer_acc_bounds using entry) (by peer_acc_bounds using entry))
  have index₂ : (g[2].get 64).setWidth 8 = BitVec.ofInt 8 (Curve.radixRemaining y 32) := by
    rw [idx₃,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq]; exact by'
  have right₂ := (right.of_frame f₁ (by peer_acc_call_bounds using entry)).of_frame f₂ (by peer_acc_call_bounds using entry)
  obtain ⟨w,h,r,path₃,st₃,rv,rs,re,f₃,kw⟩ := peerPointLookup (r := .l11d70e) select false entry st₂ rfl rfl c₃
    (by decide) di₃ si₃ index₂ hy right₂
  obtain ⟨top₄,slot₄,_⟩ := access st₃ rfl
  have gp₃ (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) : w[i].get 64 = u[i].get 64 :=
    congrArg (Value.get 64) ((kw i (by simp only [Activation.calleeSavedNumbers,Sample.nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (kg i hi))
  obtain ⟨j,c₄,di₄,si₄,kj⟩ := secondAddBlock top₄ slot₄ st₃.widths st₃.savedWidths
    ((gp₃ 12 (by decide)).trans ((gp₂ 12 (by decide)).trans ((gp₁ 12 (by decide)).trans b12)))
    ((gp₃ 14 (by decide)).trans ((congrArg (Value.get 64) (ku 14 (by decide))).trans accPtr))
  obtain ⟨v',m',path₄,st₄,sum₂,f₄,kv'⟩ := peerPointAdd (r := .l11d719) add entry st₃ rfl rfl c₄ (by decide) di₄ si₄
    (sum₁.of_frame f₃ (by peer_acc_call_bounds using entry)) rs
  have zero := (congrArg (Value.get 64) ((kv' 5 (by decide)).trans (kj 5 (by decide)))).trans
    ((gp₃ 5 (by decide)).trans ((gp₂ 5 (by decide)).trans ((gp₁ 5 (by decide)).trans b5)))
  have lim : memLoad m' (sp fr + 56) 64 = 66 :=
    (f₄.memLoad_eq (by peer_acc_call_bounds using entry)).trans ((f₃.memLoad_eq (by peer_acc_call_bounds using entry)).trans
      ((f₂.memLoad_eq (by peer_acc_call_bounds using entry)).trans ((f₁.memLoad_eq (by peer_acc_call_bounds using entry)).trans limit)))
  obtain ⟨result,last,fin⟩ := Accumulator.peerExit entry st₄ zero lim
  have full := (f'.trans f₃ (by peer_acc_call_bounds using entry)).trans f₄ (by peer_acc_call_bounds using entry)
  obtain ⟨sv,ve⟩ := Projective.add_correct _ _ identity_valid tv
  obtain ⟨valid,value⟩ := Projective.add_correct _ _ sv rv
  refine ⟨result,m',(((((init.trans path₁).trans path₂).trans path₃).trans path₄).trans last),
    fin.atoms,fin.widths,fin.savedWidths,fin.frame,s.firstTable.of_frame full (by peer_acc_bounds using entry),
    s.secondTable.of_frame full (by peer_acc_bounds using entry),?_,?_,⟨(identity.add t).add r,valid,?_,?_⟩,fin.locals⟩
  · apply WordsAt.of_frame s.firstDigits full (by decide); peer_acc_bounds using entry
  · apply WordsAt.of_frame s.secondDigits full (by decide); peer_acc_bounds using entry
  · exact Eq.mp (congrArg (fun k => ((identity.add t).add r).Stored m' k) addr) sum₂
  · have first : (identity.add t).value = Curve.selectDigit (peerFirstBase d peer) (Curve.radixRemaining x 32) :=
      ve.trans ((congrArg (fun p => Standards.SECG.ECC.Curve.add domain p t.value) identity_value).trans te)
    exact value.trans ((congrArg (fun p => Standards.SECG.ECC.Curve.add domain p r.value) first).trans
      (congrArg (Standards.SECG.ECC.Curve.add domain _) re))

end Prepare

end K256.Proofs.Generate.Generator.Multiply
