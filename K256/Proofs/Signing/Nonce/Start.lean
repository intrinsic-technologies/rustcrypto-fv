import K256.Proofs.Signing.Nonce.Start.Prepare
import K256.Proofs.Signing.Nonce.Start.InitializeCall

namespace K256.Proofs.Signing.Nonce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Verify.Hash

private theorem resumeCandidate {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4] = ⟨64,sp-16⟩) (df : a[22] = ⟨1,0⟩)
    (r12 : a[12] = ⟨64,sp+8⟩) (r13 : a[13] = ⟨64,sp+256⟩)
    (r14 : a[14].width = 64) (widths : ParseSignature.ArgumentWidths a) :
    ∃ b, Reaches .l10584e a m .l105886 b m ∧ CandidateRegisters b sp ∧
      ∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i] := by
  have addr : a[4].get 64 = sp-16 := congrArg (Value.get 64) rsp
  have plus : sp - 16 + 16 = sp := by bv_omega
  suffices step : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10584e,a,m⟩ =
      .jump ⟨.l105886,b,m⟩ ∧ CandidateRegisters b sp ∧
      ∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i] by
    obtain ⟨b,run,post⟩ := step
    exact ⟨b,.single (congrArg (Transfer.next _ []) run),post⟩
  refine ⟨?_,?eval,?post⟩
  case eval =>
    cfg_eval [addr,plus]
    rfl
  case post =>
    refine ⟨⟨rfl,df,rfl,rfl,r12,r13,r14,rfl,?_⟩,?_⟩
    · rintro ⟨i,hi⟩ hm
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
      · first | rfl | exact widths 7 (by decide)
      · first | rfl | exact widths 6 (by decide)
      · first | rfl | exact widths 2 (by decide)
      · first | rfl | exact widths 1 (by decide)
      · first | rfl | exact widths 8 (by decide)
      · first | rfl | exact widths 9 (by decide)
    · rintro ⟨i,hi⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl <;> rfl

theorem start {a : Registers} {m : Ram} {sp : BitVec 64} {d : Nat} {message : ByteArray}
    (rsp : a[4] = ⟨64,sp⟩) (df : a[22] = ⟨1,0⟩)
    (r13 : a[13] = ⟨64,sp + 256⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,14,15] → a[i].width = 64)
    (mxcsr : a[39].width = 32) (ftw : a[50].width = 16) (fcw : a[51].width = 16)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (stack : Writable Extracted.programImage m (sp-2232) 3392)
    (depth : 2232 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32) (align : sp.toNat % 16 = 0)
    (hash : Compression.StateAt m (sp+72) (compressBlocks initialHash (bytePadding message)))
    (key : memLoad m (sp+344) 64 = sp+1016)
    (secret : WordsAt m (sp+1016) 64 (scalarWords d))
    (pos : 0 < d) (bound : d < domain.n) :
    ∃ b t, Reaches .l105758 a m .l105886 b t ∧ CandidateRegisters b sp ∧
      (∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m t (initializationRegions sp) ∧
      (⟨(sp+352).toNat,32⟩ : MemoryRegion).HasBytes t (SHA256.hashBytes message) ∧
      WordsAt t (sp+592) 64 (scalarWords domain.n) ∧ memLoad t (sp+688) 64 = sp+592 ∧
      Initialize.StateAt t (sp+696) (initialNonceState d message) := by
  obtain ⟨b,t,first,ready,kept,writes⟩ := Start.prepare rsp df r13 widths mxcsr ftw fcw image
    stack depth limit align hash key secret bound
  have inStack : RamWriteFrame m t [⟨(sp-2232).toNat,3392⟩] := by
    apply (RamWriteFrame.refl _ _).trans writes
    have base := BitVec.toNat_sub_of_le (show (2232 : BitVec 64) ≤ sp from depth)
    intro r hr
    refine ⟨_,List.mem_cons_self,?_⟩
    simp only [initializationRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> dsimp at * <;> omega
  obtain ⟨c,u,call,crsp,cdf,c12,c13,c14,cw,kept',writes',digest,order,ptr,state⟩ :=
    Start.initializeCall ready ((congrArg Value.width (kept 39 (by decide))).trans mxcsr)
      ((congrArg Value.width (kept 50 (by decide))).trans ftw) ((congrArg Value.width (kept 51 (by decide))).trans fcw)
      (Generate.Generator.Affine.Invert.Core.stackImage stack inStack image)
      (stack.of_frame writes) depth limit align pos bound
  obtain ⟨out,last,regs,kept''⟩ := resumeCandidate (m := u) crsp cdf c12 c13 c14 cw
  exact ⟨out,u,first.trans (call.trans last),regs,
    fun i hi => (kept'' i hi).trans ((kept' i hi).trans (kept i hi)),
    writes.trans writes' (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩),digest,order,ptr,state⟩

end K256.Proofs.Signing.Nonce
