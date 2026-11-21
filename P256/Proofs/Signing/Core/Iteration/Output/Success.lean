import P256.Proofs.Signing.Core.Iteration.Output.Arguments
import P256.Proofs.Signing.Core.Iteration.Output.Compare
import P256.Proofs.Signing.Core.Iteration.Output.Recovery
import P256.Proofs.Signing.Core.Iteration.Output.Store
import P256.Proofs.Signing.Core.Iteration.Output.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {r scalarS x y value : Nat}

theorem success (pre : SignPre s boundary) (frame : Frame s t) (payload : Payload s t r scalarS)
    (rip : t.RIP = 0x10d3c4) (valueX : Field.MontgomeryAt t (frameBase s+104) x)
    (valueY : Field.MontgomeryAt t (frameBase s+136) y)
    (reduced : Nat256At t (frameBase s+176) value)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ fuel u, Advances boundary fuel t u ∧ CalleeResult s u boundary 65 4584 ∧
      Nat256At u (s.regValue .rdi) r ∧ Nat256At u (s.regValue .rdi+32) scalarS := by
  obtain ⟨nA,a,runA,fa,pa,ipa,sa,da,ra,ma⟩ := scalar_arguments pre frame payload rip
  have xa := valueX.of_bytes_eq (fun _ _ => congrArg (·[_]?) ma)
  have ya := valueY.of_bytes_eq (fun _ _ => congrArg (·[_]?) ma)
  have va : Nat256At a (frameBase s+176) value := ⟨reduced.1,by simpa only [ma] using reduced.2⟩
  obtain ⟨nB,b,runB,fb,ipb,regsB,memB,pointB⟩ := encode_call pre fa ipa sa da va
  have pb := pa.copy (fun i hi => memB i (by omega)) (fun reg hr => regsB reg (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with rfl|rfl|rfl <;> simp))
  have xb := xa.of_bytes_eq (fun i hi => pointB i (by omega))
  have yb : Field.MontgomeryAt b (frameBase s+136) y := ya.of_bytes_eq (by
    intro i hi
    have h := pointB (32+i) (by omega)
    simp only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.ofNat_eq_ofNat] at h
    have address : frameBase s+104#64+32#64 = frameBase s+136#64 := by rw [BitVec.add_assoc]; rfl
    simpa only [address,BitVec.ofNat_eq_ofNat] using h)
  obtain ⟨nC,c,runC,fc,pc,ipc,sc,dc,xc,regsC,memC⟩ := x_arguments pre fb pb ipb xb
  have yc := yb.of_bytes_eq memC
  obtain ⟨nD,d,runD,fd,ipd,regsD,memD,yD⟩ := convert_call pre fc
    0xd423 0xffffa8d8 (by decide) (by decide +kernel) (by decide) ipc
    (by decide) (.inr (by decide)) sc dc xc
  have pd := pc.copy (fun i hi => memD i (by omega)) (fun reg hr => regsD reg (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with rfl|rfl|rfl <;> simp))
  have yd := yc.of_bytes_eq yD
  have rd : d.regValue .r14 = frameBase s+432 := (regsD _ (by simp)).trans
    ((regsC _ (by simp)).trans ((regsB _ (by simp)).trans ra))
  obtain ⟨nE,e,runE,fe,pe,ipe,se,de,count,_,yE⟩ := compare_arguments pre fd pd ipd rd
  have ye := yd.of_bytes_eq yE
  obtain ⟨nF,f,runF,ff,ipf,regsF,memF,yF⟩ := compare_call pre fe ipe se de count
  have pf := pe.copy (fun i hi => memF i (by omega)) (fun reg hr => regsF reg (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with rfl|rfl|rfl <;> simp))
  have yf := ye.of_bytes_eq yF
  obtain ⟨g,runG,fg,pg,ipg,sg,dg,agG⟩ := y_arguments pre ff pf ipf
  have yg := yf.of_bytes_eq (fun _ _ => congrArg (·[_]?) (agG.external (by simp [Component.Covers])))
  obtain ⟨nH,h,runH,fh,iph,regsH,memH,_⟩ := convert_call pre fg
    0xd4a0 0xffffa85b (by decide) (by decide +kernel) (by decide) ipg
    (by decide) (.inl (by decide)) sg dg yg
  have ph := pg.copy (fun i hi => memH i (by omega)) (fun reg hr => regsH reg (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with rfl|rfl|rfl <;> simp))
  obtain ⟨i,runI,fi,pi,ipi,_⟩ := choice_arguments pre fh ph iph
  obtain ⟨j,runJ,fj,pj,ipj⟩ := recovery_choice pre fi pi ipi
  obtain ⟨k,runK,fk,pk,ipk,_⟩ := recovery_byte pre fj pj ipj
  obtain ⟨l,runL,fl,ipl,first,second⟩ := store_signature pre fk pk ipk
  have runL' := (((((((((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runG).trans runH).trans runI).trans runJ).trans runK).trans runL)
  obtain ⟨n0,run0⟩ := execution
  obtain ⟨nU,u,runU,result,memU⟩ := epilogue pre fl ipl ⟨_,run0.trans runL'⟩
  exact ⟨_,u,runL'.trans runU,result,
    ⟨first.1,by simpa only [memU] using first.2⟩,
    ⟨second.1,by simpa only [memU,BitVec.ofNat_eq_ofNat] using second.2⟩⟩

end P256.Proofs.Signing.Core.Iteration.Output
