import K256.Proofs.Signing.Composition.Attempt.Arithmetic.Base

namespace K256.Proofs.Signing.Composition.Attempt.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Verify.LIR
open Verify.Core.ScalarProduct (entryInputs)

structure BinaryInputs (s : RamState) (a : Registers) (src rhs dst : BitVec 64) : Prop where
  rsp : a[4] = ⟨64,sp s-8⟩
  df : a[22] = ⟨1,0⟩
  gp : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16
  cx : a[1].width = 64
  di : a[7] = ⟨64,dst⟩
  si : a[6] = ⟨64,src⟩
  dx : a[2] = ⟨64,rhs⟩

theorem BinaryInputs.widths {s : RamState} {a : Registers} {src rhs dst : BitVec 64}
    (reg : BinaryInputs s a src rhs dst) (r8 : a[8].width = 64) (r9 : a[9].width = 64) :
    ParseSignature.ArgumentWidths a := by
  intro ⟨i,hi⟩ h
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact congrArg Value.width reg.di
  · exact congrArg Value.width reg.si
  · exact congrArg Value.width reg.dx
  · exact reg.cx
  · exact r8
  · exact r9

private theorem inputRegs {s : RamState} {a : Registers} {src rhs dst : BitVec 64}
    (reg : BinaryInputs s a src rhs dst) :
    BinaryInputs s (entryInputs a) src rhs dst := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.rsp
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.df
  · intro ⟨i,hi⟩ h
    have g := reg.gp ⟨i,hi⟩ h
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    have q8 : 8 ≠ i := by omega
    have q9 : 9 ≠ i := by omega
    simpa only [Fin.getElem_fin,entryInputs,Vector.getElem_set_ne _ _ q8,Vector.getElem_set_ne _ _ q9] using g
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.fp
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.cx
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.di
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.si
  · simpa (disch := decide) only [entryInputs,Vector.getElem_set_ne] using reg.dx

private theorem normalizedWidth {s : RamState} {a : Registers} {src rhs dst : BitVec 64}
    (reg : BinaryInputs s a src rhs dst) : ParseSignature.ArgumentWidths (entryInputs a) := by
  apply (inputRegs reg).widths
  · simp (disch := decide) only [entryInputs,Vector.getElem_set_ne,Vector.getElem_set_self,reg.rsp]
  · simp only [entryInputs,Vector.getElem_set_self,reg.rsp]

theorem invokeMultiply {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {site after entry : Signing.LIR.Label} {a c : Registers} {m n : Ram}
    {ret src rhs dst : BitVec 64} {x y : Nat}
    (siteCall : Signing.LIR.program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩ =
      .call ⟨entry,c,n⟩ (resume after ret))
    (point : entry = .l109f60 ∨ entry = .l109f70)
    (mem : Memory s n) (tag : memLoad n (sp s-8) 64 = ret) (small : ret.toNat < 2^32)
    (reg : BinaryInputs s c src rhs dst)
    (rx : Readable n src 32) (ry : Readable n rhs 32) (wr : Writable Extracted.programImage n dst 32)
    (dstAbove : (sp s-8).toNat+8 ≤ dst.toNat)
    (apart : ∀ p ∈ [src,rhs],
      (sp s-8).toNat+8 ≤ p.toNat ∧ (p.toNat+32 ≤ dst.toNat ∨ dst.toNat+32 ≤ p.toNat))
    (hx : x < domain.n) (hy : y < domain.n)
    (wx : WordsAt n src 64 (scalarWords x)) (wy : WordsAt n rhs 64 (scalarWords y)) :
    ∃ b t, Reach (core site a m) (core after b t) ∧ b[4] = ⟨64,sp s⟩ ∧ SavedRegs b c ∧
      ParseSignature.ArgumentWidths b ∧ WordsAt t dst 64 (scalarWords ((x*y)%domain.n)) ∧
      RamWriteFrame n t [⟨(sp s-8).toNat-321,321⟩,⟨dst.toNat,32⟩] := by
  let fr := activation s n (entryInputs c) 321 ret
  have q := inputRegs reg
  have atoms : Atom.All Extracted.programImage (entryInputs c) n (Fn109f60.frameAt .l109f60 fr) :=
    childAtoms call mem Fn109f60.frameInfo rfl (by decide) (by decide) q.rsp q.df q.gp q.fp (normalizedWidth reg)
      tag small
  have di : fr.rdi = dst := getWord q.di
  have si : fr.rsi = src := getWord q.si
  have dx : fr.rdx = rhs := getWord q.dx
  obtain ⟨out,run,retEq,post,widths,words,frame⟩ := Verify.Core.ScalarProduct.execution (a := c)
    atoms (mem.image call) hx hy (si.symm ▸ rx) (dx.symm ▸ ry) (di.symm ▸ wr) (di.symm ▸ dstAbove)
    (by rw [si,dx,di]; intro p hp; exact ⟨Or.inr (apart p hp).1,(apart p hp).2⟩)
    (si.symm ▸ wx) (dx.symm ▸ wy)
  have signed : Signing.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨entry,c,n⟩,[]⟩ out := by
    rcases point with rfl|rfl
    · exact Transfer.verifyExecAt rfl run
    · exact Transfer.verifyExecAt rfl (Scalar.multiply_of_product run)
  obtain ⟨rsp,keep⟩ := savedReturn q.df q.gp q.fp post
  refine ⟨_,_,callReaches siteCall signed retEq,rsp,?_,widths,di ▸ words,di ▸ frame⟩
  intro i hi
  have ne8 : 8 ≠ i.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
  have ne9 : 9 ≠ i.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
  simpa only [entryInputs,Fin.getElem_fin, Vector.getElem_set_ne _ _ ne8,
    Vector.getElem_set_ne _ _ ne9] using keep i hi

theorem invokeAdd {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {site after : Signing.LIR.Label} {a c : Registers} {m n : Ram}
    {ret src rhs dst : BitVec 64} {x y : Nat}
    (siteCall : Signing.LIR.program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩ =
      .call ⟨.l10a2e0,c,n⟩ (resume after ret))
    (mem : Memory s n) (tag : memLoad n (sp s-8) 64 = ret) (small : ret.toNat < 2^32)
    (reg : BinaryInputs s c src rhs dst) (args : ParseSignature.ArgumentWidths c)
    (rx : Readable n src 32) (ry : Readable n rhs 32) (wr : Writable Extracted.programImage n dst 32)
    (dstAbove : (sp s-8).toNat+8 ≤ dst.toNat)
    (apart : ∀ p ∈ [src,rhs],
      (sp s-8).toNat+8 ≤ p.toNat ∧ (p.toNat+32 ≤ dst.toNat ∨ dst.toNat+32 ≤ p.toNat))
    (hx : x < domain.n) (hy : y < domain.n)
    (wx : WordsAt n src 64 (scalarWords x)) (wy : WordsAt n rhs 64 (scalarWords y)) :
    ∃ b t, Reach (core site a m) (core after b t) ∧ b[4] = ⟨64,sp s⟩ ∧ SavedRegs b c ∧
      ParseSignature.ArgumentWidths b ∧ WordsAt t dst 64 (scalarWords ((x+y)%domain.n)) ∧
      RamWriteFrame n t [⟨(sp s-8).toNat-64,64⟩,⟨dst.toNat,32⟩] := by
  let fr := activation s n c 64 ret
  have atoms : Atom.All Extracted.programImage c n (Fn10a2e0.frameAt .l10a2e0 fr) :=
    childAtoms call mem Fn10a2e0.frameInfo rfl (by decide) (by decide) reg.rsp reg.df reg.gp reg.fp args
      tag small
  have di : fr.rdi = dst := getWord reg.di
  have si : fr.rsi = src := getWord reg.si
  have dx : fr.rdx = rhs := getWord reg.dx
  obtain ⟨out,run,retEq,post,widths,words,frame⟩ := Scalar.add atoms (mem.image call) hx hy
    (si.symm ▸ rx) (dx.symm ▸ ry) (di.symm ▸ wr) (di.symm ▸ dstAbove)
    (by rw [si,dx,di]; intro p hp; exact ⟨Or.inr (apart p hp).1,(apart p hp).2⟩)
    (si.symm ▸ wx) (dx.symm ▸ wy)
  obtain ⟨rsp,keep⟩ := savedReturn reg.df reg.gp reg.fp post
  exact ⟨_,_,callReaches siteCall (Transfer.verifyExecAt rfl run) retEq,rsp,keep,widths,di ▸ words,di ▸ frame⟩

end K256.Proofs.Signing.Composition.Attempt.Arithmetic
