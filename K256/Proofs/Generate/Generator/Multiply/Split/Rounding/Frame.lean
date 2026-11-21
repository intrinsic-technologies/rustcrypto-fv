import K256.Proofs.Generate.Generator.Multiply.Split.Contract

namespace K256.Proofs.Generate.Generator.Multiply.Split.Rounding

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev addFrame (fr : Activation) (b : Registers) : Activation :=
  { fr with
    rsp := fr.rsp - 0xa0, ret := 0x11badf, rcx := 0x2021a0, rdx := 0x202180,
    rdi := fr.rsp - 0x50, rsi := fr.rsp - 0x70, r14 := fr.rdi,
    rbx := b[3].get 64, rbp := b[5].get 64, r12 := b[12].get 64,
    r13 := b[13].get 64, r15 := b[15].get 64, r8 := b[8].get 64, r9 := b[9].get 64 }

structure AdditionFrame (fr : Activation) (m : Ram) : Prop where
  saved : ∀ k r, (k,r) ∈ [(0x78,6),(0x30,3),(0x28,12),(0x20,13),(0x18,14),(0x10,15),(8,5)] →
    memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r
  readable : Readable m fr.rsp 8
  returnWord : memLoad m fr.rsp 64 = fr.ret
  returnLow : fr.ret.toNat < 2^32
  stack : Writable Extracted.programImage m (fr.rsp - 0xe0) 0xe0
  low : fr.low.toNat + 0xe0 ≤ fr.rsp.toNat
  align : fr.rsp.toNat % 16 = 8

theorem AdditionFrame.resume {fr : Activation} {b : Registers} {m : Ram}
    {out : Output Value Ram Reg.count} (s : AdditionFrame fr m)
    (done_ : Atom.All Extracted.programImage out.values out.store (Fn1109b0.doneAt (addFrame fr b)))
    (writes : RamWriteFrame m out.store
      [⟨(fr.rsp - 0xa0).toNat - 0x40, 0x40⟩, ⟨(fr.rsp - 0x50).toNat, 32⟩]) :
    Atom.All Extracted.programImage out.values out.store (Fn11b8f0.frameAt .l11badf fr) ∧
    out.values[3] = ⟨64, b[3].get 64⟩ ∧ out.values[12] = ⟨64, b[12].get 64⟩ ∧
    out.values[15] = ⟨64, b[15].get 64⟩ := by
  simp only [Fn1109b0.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨sp,df,bx,bp,r12,r13,r14,r15,mx,ftw,fcw,_⟩ := done_
  have room := s.low
  have high := s.readable.low
  have ofs (k : Nat) (hk : k ≤ 224) : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have h : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,h]; omega), h]
  have h160 : (fr.rsp - 160).toNat = fr.rsp.toNat - 160 := ofs 160 (by decide)
  have h80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := ofs 80 (by decide)
  have protectedWord (k : Nat) (hk : k ≤ 48 ∨ k = 120) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply writes.memLoad_eq
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Nat.reduceDiv, ofs k (by omega), h160, h80]
    omega
  have save (k r : Nat) (h : (k,r) ∈ [(120,6),(48,3),(40,12),(32,13),(24,14),(16,15),(8,5)])
      (hk : k ≤ 48 ∨ k = 120) := (protectedWord k hk).trans (s.saved k r h)
  refine ⟨?_,bx,r12,r15⟩
  simp only [Fn11b8f0.frameAt, Fn11b8f0.frameAtG1, Atom.All, Atom.Holds]
  rw [show fr.rsp - 160 + 8 = fr.rsp - 152 by bv_omega] at sp
  refine ⟨sp,df,r14,mx,ftw,fcw,save 120 6 (by decide) (by decide),save 48 3 (by decide) (by decide),
    save 40 12 (by decide) (by decide),save 32 13 (by decide) (by decide),
    save 24 14 (by decide) (by decide),save 16 15 (by decide) (by decide),save 8 5 (by decide) (by decide),
    s.readable.of_frame writes, ?_, s.returnLow, s.stack.of_frame writes, s.low, s.align, trivial⟩
  have p := protectedWord 0 (by decide)
  change memLoad _ (fr.rsp - 0) _ = memLoad _ (fr.rsp - 0) _ at p
  rw [show fr.rsp - 0 = fr.rsp by bv_omega] at p
  exact p.trans s.returnWord

end K256.Proofs.Generate.Generator.Multiply.Split.Rounding
