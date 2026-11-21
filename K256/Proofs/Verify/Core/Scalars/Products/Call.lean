import K256.Proofs.Verify.Core.Scalars.Products.Geometry
import K256.Proofs.Verify.Core.Scalars.Products.Transfer

namespace K256.Proofs.Verify.Core.ScalarProduct

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)

def callFrame (resume : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨resume, #v[], rfl, some ⟨64,ret⟩⟩

structure CallRegisters (fr : Activation) (c : Registers) (src rhs dst : Nat) : Prop where
  sp : c[4] = ⟨64,localSp fr - 8⟩
  df : c[22] = ⟨1,0⟩
  si : c[6] = ⟨64,slot fr src⟩
  dx : c[2] = ⟨64,slot fr rhs⟩
  di : c[7] = ⟨64,slot fr dst⟩
  gp : ∀ i : Fin 53, i.val ∈ [1,3,5,12,13,14,15] → c[i].width = 64
  mx : c[39].width = 32
  ft : c[50].width = 16
  fc : c[51].width = 16

structure Returned (fr : Activation) (c b : Registers) (m n : Ram) (dst value : Nat) : Prop where
  sp : b[4] = ⟨64,localSp fr⟩
  keep : ∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = c[i]
  widths : ParseSignature.ArgumentWidths b
  words : WordsAt n (slot fr dst) 64 (scalarWords value)
  frame : RamWriteFrame m n (writes fr dst)
  whole : RamWriteFrame fr.original n [fr.region]

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

private theorem get_eq {v : Value} {w : Nat} (h : v.width = w) :
    v = ⟨w,v.get w⟩ := by
  cases v
  subst w
  simp [Value.get]

private def callee (fr : Activation) (c : Registers) (n : Ram) (src rhs dst : Nat)
    (ret : BitVec 64) : Activation :=
  { fr with
    original := n, rsp := localSp fr - 8, ret, rdi := slot fr dst, rsi := slot fr src,
    rdx := slot fr rhs, rcx := c[1].get 64, r8 := localSp fr - 8, r9 := localSp fr - 8,
    rbx := c[3].get 64, rbp := c[5].get 64, r12 := c[12].get 64, r13 := c[13].get 64,
    r14 := c[14].get 64, r15 := c[15].get 64, mxcsr := c[39].get 32,
    ftw := c[50].get 16, fcw := c[51].get 16}

private theorem ready (e : Entry fr a p digest r s) {c : Registers} {n : Ram}
    {src rhs dst : Nat} {ret : BitVec 64} (regs : CallRegisters fr c src rhs dst)
    (frame : RamWriteFrame fr.original n [fr.region])
    (tag : memLoad n (localSp fr - 8) 64 = ret) (small : ret.toNat < 2^32) :
    Atom.All Extracted.programImage (entryInputs c) n
      (Fn109f60.frameAt .l109f60 (callee fr c n src rhs dst ret)) := by
  have push := pushNat e
  have bottom := e.low_toNat
  have room := e.stackRoom
  have entry := e.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at entry
  have align : fr.rsp.toNat % 16 = 8 := by
    exact entry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sub : (localSp fr - 8 - 321).toNat = fr.rsp.toNat - 817 := by
    rw [localSp, BitVec.sub_sub, BitVec.sub_sub]
    exact belowNat e (off := 817) (by decide)
  have w : Writable Extracted.programImage n (localSp fr - 8 - 321) 321 :=
    (e.stack.of_frame frame).sub (by omega) (by omega)
  have gp (i : Fin 53) (hi : i.val ∈ [1,3,5,12,13,14,15]) := get_eq (regs.gp i hi)
  have norm (i : Fin 53) : (entryInputs c)[i] =
      (if 9 = i.val then c[4] else if 8 = i.val then c[4] else c[i]) := by
    change ((c.set 8 c[4]).set 9 c[4])[i.val] = _
    simp only [Vector.getElem_set]
    rfl
  simp only [Fn109f60.frameAt, Fn109f60.frameAtG11, Atom.All, Atom.Holds, callee, norm]
  exact ⟨regs.sp,regs.df,gp 1 (by decide),regs.dx,gp 3 (by decide),gp 5 (by decide),
    regs.si,regs.di,regs.sp,regs.sp,gp 12 (by decide),gp 13 (by decide),gp 14 (by decide),
    gp 15 (by decide), get_eq regs.mx, get_eq regs.ft, get_eq regs.fc,
    (writePush e frame).readable,tag,small,w,by omega,by omega,trivial⟩

theorem invoke (e : Entry fr a p digest r s) {l resume : Label} {b c : Registers}
    {m n : Ram} {src rhs dst x y : Nat} {ret : BitVec 64}
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,b,m⟩ =
      .call ⟨.l109f60,c,n⟩ (callFrame resume ret))
    (regs : CallRegisters fr c src rhs dst)
    (frame : RamWriteFrame fr.original n [fr.region])
    (tag : memLoad n (localSp fr - 8) 64 = ret) (small : ret.toNat < 2^32)
    (sx : src + 32 ≤ 488) (sy : rhs + 32 ≤ 488) (sd : dst + 32 ≤ 488)
    (dx : src + 32 ≤ dst ∨ dst + 32 ≤ src) (dy : rhs + 32 ≤ dst ∨ dst + 32 ≤ rhs)
    (hx : x < domain.n) (hy : y < domain.n)
    (wx : WordsAt n (slot fr src) 64 (scalarWords x))
    (wy : WordsAt n (slot fr rhs) 64 (scalarWords y)) :
    ∃ b' m', Reaches l b m resume b' m' ∧ Returned fr c b' n m' dst ((x*y)%domain.n) := by
  let child := callee fr c n src rhs dst ret
  have room := e.stackRoom
  have push := pushNat e
  have p₁ := slotNat e (off := src) (by omega)
  have p₂ := slotNat e (off := rhs) (by omega)
  have p₃ := slotNat e (off := dst) (by omega)
  have above : child.rsp.toNat + 8 ≤ child.rdi.toNat := by
    change (localSp fr - 8).toNat + 8 ≤ (slot fr dst).toNat
    omega
  have apart : ∀ ptr ∈ [child.rsi, child.rdx],
      (ptr.toNat + 32 ≤ child.rsp.toNat - 321 ∨ child.rsp.toNat + 8 ≤ ptr.toNat) ∧
      (ptr.toNat + 32 ≤ child.rdi.toNat ∨ child.rdi.toNat + 32 ≤ ptr.toNat) := by
    intro ptr hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl <;> dsimp only [child, callee] <;> omega
  obtain ⟨out,run,returned,done_,widths,words,foot⟩ :=
    execution (fr := child) (ready e regs frame tag small) (e.loaded_of_frame frame)
      hx hy (writeSlot e frame sx).readable (writeSlot e frame sy).readable (writeSlot e frame sd)
      above apart wx wy
  have reach : Reaches l b m resume out.values out.store := by
    refine .step (b := ⟨⟨.l109f60,c,n⟩,[callFrame resume ret]⟩) ?_ ?_
    · change (program.runBlock _ _).next _ _ = _
      rw [call]
      rfl
    · have accepted : (callFrame resume ret).Accepts (dialect Extracted.programImage) out.tag = true := by
        rw [returned]
        exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret)
      exact ParseSignature.exec_reaches_resume run _ [] accepted
  simp only [Fn109f60.doneAt, Atom.All, Atom.Holds, child, callee] at done_
  obtain ⟨sp, df, bx, bp, r12, r13, r14, r15, mx, ft, fc, _⟩ := done_
  refine ⟨_,_,reach, ⟨?_,?_,widths,words,foot,frame.trans foot (writesWithin e sd)⟩⟩
  · rw [BitVec.sub_add_cancel] at sp
    exact sp
  · intro ⟨i,hi⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact bx.trans (get_eq (regs.gp 3 (by decide))).symm
    · exact bp.trans (get_eq (regs.gp 5 (by decide))).symm
    · exact r12.trans (get_eq (regs.gp 12 (by decide))).symm
    · exact r13.trans (get_eq (regs.gp 13 (by decide))).symm
    · exact r14.trans (get_eq (regs.gp 14 (by decide))).symm
    · exact r15.trans (get_eq (regs.gp 15 (by decide))).symm
    · exact df.trans regs.df.symm
    · exact mx.trans (get_eq regs.mx).symm
    · exact ft.trans (get_eq regs.ft).symm
    · exact fc.trans (get_eq regs.fc).symm

end K256.Proofs.Verify.Core.ScalarProduct
