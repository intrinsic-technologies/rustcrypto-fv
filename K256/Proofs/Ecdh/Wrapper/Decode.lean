import K256.Proofs.Ecdh.Wrapper.Decode.Frame
import K256.Proofs.Ecdh.Wrapper.Decode.Valid
import K256.Proofs.Ecdh.Wrapper.Decode.Copy
import K256.Proofs.Ecdh.Decode.Execution
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem decodePeer {s : RamState} {secret key : ByteArray} {d : Nat} {p : Curve.Point}
    {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (peerPtr : a[14] = ⟨64, s.regValue .rdx⟩) (scalar : ScalarAt s m 0xc0 d)
    (decoded : K256.Spec.Secp256k1.groupPoint key = some p) :
    ∃ b n, Reaches .l1017b1 a m .l101831 b n ∧ Caller s b n ∧
      ScalarAt s n 0x10 d ∧ Decode.AffinePointAt n (localSp s + 0x158) p := by
  obtain ⟨b,n,path,regs,bx,si,di,mem,words,bytes,slot⟩ := copyToCall call state peerPtr scalar
  let fr := decoderActivation s n b
  have src : fr.rsi = localSp s + 48 := congrArg (Value.get 64) si
  have dst : fr.rdi = localSp s + 344 := congrArg (Value.get 64) di
  obtain ⟨entry,read,write,srcAbove,dstAbove,text⟩ := decoderEntry call mem regs src dst slot
  obtain ⟨out,run,tag,done,_,argWidths,frame,flag,point⟩ :=
    Decode.execution fr b entry read write srcAbove dstAbove text (loaded_of_stackFrame call mem.frame)
      (by rw [src]; exact bytes) decoded
  obtain ⟨after,scalarAfter⟩ := decoderMemory call mem words dst frame
  simp only [Fn120f30.doneAt, Atom.All, Atom.Holds] at done
  obtain ⟨rsp,df,rbx,rbp,r12,r13,r14,r15,mx,ft,fc,_⟩ := done
  have caller : Caller s out.values out.store := by
    refine ⟨after, rsp.trans ?_, rbx.trans ?_, df, ?_, congrArg Value.width mx,
      congrArg Value.width ft, congrArg Value.width fc⟩
    · congr 1; change s.regValue .rsp - 6160 + 8 = s.regValue .rsp - 6152; bv_omega
    · congr 1; exact congrArg (Value.get 64) bx
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first
        | exact argWidths ⟨_,hi⟩ (by dsimp only [Activation.argumentNumbers]; decide)
        | exact congrArg Value.width rbx
        | exact congrArg Value.width rbp
        | exact congrArg Value.width r12
        | exact congrArg Value.width r13
        | exact congrArg Value.width r14
        | exact congrArg Value.width r15
  have ret := ParseSignature.exec_reaches_resume run (callFrame .l101823 0x101823) [] (by rw [tag]; rfl)
  have path' : Reaches .l1017b1 a m .l101823 out.values out.store := path.trans ret
  rw [dst] at flag point
  rw [show localSp s + 344 + 88 = localSp s + 432 by bv_omega] at flag
  obtain ⟨c,last,caller'⟩ := decoderValid call caller flag
  exact ⟨c,out.store,path'.trans last,caller',scalarAfter,point⟩

end K256.Proofs.Ecdh.Wrapper
