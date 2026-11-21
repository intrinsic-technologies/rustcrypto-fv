import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Start.Memory

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Start

structure ScalarRegisters (fr : Activation) (b : Registers) (d : Nat) : Prop where
  r5 : b[5] = ⟨64,(u d)[0]⟩
  r3 : b[3] = ⟨64,(u d)[1]⟩
  r13 : b[13] = ⟨64,(u d)[2]⟩
  r12 : b[12] = ⟨64,(u d)[3]⟩
  r14 : b[14] = ⟨64,(v d)[0]⟩
  r15 : b[15] = ⟨64,sp fr + 0x1d0⟩

theorem ScalarRegisters.widths {fr : Activation} {b : Registers} {d : Nat}
    (r : ScalarRegisters fr b d) : SavedWidths b := by
  rintro ⟨i,hi⟩ hm
  simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
  · exact congrArg Value.width r.r3
  · exact congrArg Value.width r.r5
  · exact congrArg Value.width r.r12
  · exact congrArg Value.width r.r13
  · exact congrArg Value.width r.r14
  · exact congrArg Value.width r.r15

structure Arguments (fr : Activation) (b : Registers) (d : Nat) : Prop extends ScalarRegisters fr b d where
  rsp : b[4] = ⟨64,sp fr - 8⟩
  rsi : b[6] = ⟨64,fr.rsi⟩
  rdi : b[7] = ⟨64,sp fr + 0x2b0⟩
  widths : ParseSignature.ArgumentWidths b
  df : b[22] = ⟨1,0⟩
  mxcsr : b[39] = ⟨32,fr.mxcsr⟩
  ftw : b[50] = ⟨16,fr.ftw⟩
  fcw : b[51] = ⟨16,fr.fcw⟩

theorem dispatch {fr : Activation} {initial a : Registers} {d : Nat} {m : Ram}
    (e : CoreEntry fr initial d) (s : SplitState fr a m d) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l11c9e7,a,m⟩ =
      .call ⟨.l10e010,b,memory fr m d⟩ (callFrame .l11ca7f 0x11ca7f) ∧ Arguments fr b d := by
  obtain ⟨rsp,df,mx,ft,fc,_⟩ := s.atoms
  obtain ⟨b,call,bsp,bs,bd,b5,b3,b13,b12,b14,b1,b2,keep⟩ :=
    dispatchEndomorphism (t := sp fr) (input := fr.rsi) (u := u d) (v := v d)
      (congrArg (Value.get 64) rsp) (callerWindow e s.frame) s.first s.second
      (s.locals (0x38,fr.rsi) (by simp))
  refine ⟨b,call,⟨b5,b3,b13,b12,b14,(keep 15 (by decide)).trans s.savedR15⟩,bsp,bs,bd,?_,
    (keep 22 (by decide)).trans df,(keep 39 (by decide)).trans mx,
    (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc⟩
  rintro ⟨i,hi⟩ hm
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
  · exact congrArg Value.width bd
  · exact congrArg Value.width bs
  · exact congrArg Value.width b2
  · exact congrArg Value.width b1
  · exact (congrArg Value.width (keep 8 (by decide))).trans (s.widths 8 (by decide))
  · exact (congrArg Value.width (keep 9 (by decide))).trans (s.widths 9 (by decide))

theorem calleeEntry {fr : Activation} {initial b : Registers} {d : Nat} {m : Ram}
    (e : CoreEntry fr initial d) (frame : RamWriteFrame fr.original (memory fr m d) [fr.region])
    (args : Arguments fr b d) :
    Atom.All Extracted.programImage b (memory fr m d) (Fn10e010.frameAt .l10e010 (callee fr b m d)) :=
  childEntry e Fn10e010.frameInfo rfl (by decide) args.widths args.toScalarRegisters.widths args.rsp
    args.df args.mxcsr args.ftw args.fcw frame
    (memLoad_memStore_same _ _ _ (by decide) (by decide)) (by decide)

end Start

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
