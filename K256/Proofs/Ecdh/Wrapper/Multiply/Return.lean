import K256.Proofs.Ecdh.Wrapper.Multiply.Entry

namespace K256.Proofs.Ecdh.Wrapper.Multiply

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Generate.Generator.Multiply

theorem afterCore {s : RamState} {secret key : ByteArray} {a : Arguments} {m : Ram}
    {d : Nat} {peer : Projective} {o : Output Value Ram Reg.count}
    (call : ValidCall ecdhDiffieHellman s [secret,key]) (mem : Scalar.Memory s m)
    (entry : PeerCoreEntry (activation s m a) a d peer)
    (bx : (activation s m a).rbx = s.regValue .rdi)
    (r12 : (activation s m a).r12 = localSp s + 344)
    (post : PeerCoreResult (activation s m a) d peer o) :
    Caller s o.values o.store ∧ o.values[12] = ⟨64, localSp s + 344⟩ ∧
      Generate.Generator.Affine.ProjectiveAt o.store (localSp s + 344) (peerWindow d peer) := by
  let fr := activation s m a
  have ptr (k : BitVec 64) : fr.rsp + k = localSp s + (k - 8) := by
    change s.regValue .rsp - 6160 + k = s.regValue .rsp - 6152 + (k - 8)
    bv_omega
  have dst : fr.rdi = localSp s + 344 := entry.outputPtr.trans (ptr _)
  obtain ⟨_,regs,widths,frame,point⟩ := post
  change Atom.All _ _ _ (Generate.LIR.Fn11c880.doneAt fr) at regs
  simp only [Generate.LIR.Fn11c880.doneAt, Atom.All, Atom.Holds] at regs
  obtain ⟨rsp,df,r3,r5,r12',r13,r14,r15,mx,ft,fc,_⟩ := regs
  have room := Scalar.stack_geometry call
  have natOff (k : Nat) (h : k ≤ 10088) :
      (s.regValue .rsp - BitVec.ofNat 64 k).toNat = (stackPtr s).toNat - k :=
    Common.stackOffset call.stackAvailable h
  have low : fr.low.toNat = (stackPtr s).toNat - 9960 := natOff 9960 (by decide)
  have top : fr.rsp.toNat = (stackPtr s).toNat - 6160 := natOff 6160 (by decide)
  have add (k : BitVec 64) (h : k.toNat ≤ 6112) :
      (fr.rsp + k).toNat = fr.rsp.toNat + k.toNat := entry.aboveStack k h
  have dptr := (congrArg BitVec.toNat entry.digitPtr).trans (add _ (by decide))
  have tptr := (congrArg BitVec.toNat entry.tablePtr).trans (add _ (by decide))
  have optr := (congrArg BitVec.toNat entry.outputPtr).trans (add _ (by decide))
  change fr.r9.toNat = fr.rsp.toNat + 128 at dptr
  change fr.rcx.toNat = fr.rsp.toNat + 4192 at tptr
  change fr.rdi.toNat = fr.rsp.toNat + 352 at optr
  have after := mem.advance call frame (by
    intro r hr
    change r ∈ coreWrites fr at hr
    simp only [coreWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp only [Activation.region] <;> omega)
  have stackEq : fr.rsp + 8 = localSp s := by
    change s.regValue .rsp - 6160 + 8 = s.regValue .rsp - 6152
    bv_omega
  rw [stackEq] at rsp
  change fr.rbx = _ at bx
  change fr.r12 = _ at r12
  rw [bx] at r3
  rw [r12] at r12'
  refine ⟨⟨after,rsp,r3,df,?_,?_,?_,?_⟩,r12',dst ▸ point⟩
  · rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact widths 1 (by decide)
    · exact widths 2 (by decide)
    · exact congrArg Value.width r3
    · exact congrArg Value.width r5
    · exact widths 8 (by decide)
    · exact widths 9 (by decide)
    · exact congrArg Value.width r12'
    · exact congrArg Value.width r13
    · exact congrArg Value.width r14
    · exact congrArg Value.width r15
  · exact congrArg Value.width mx
  · exact congrArg Value.width ft
  · exact congrArg Value.width fc

end K256.Proofs.Ecdh.Wrapper.Multiply
