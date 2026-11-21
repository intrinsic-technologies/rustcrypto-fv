import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Start.Call

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Start

private theorem savedWord {x y : Value} {w : BitVec 64}
    (fromCall : y = ⟨64,x.get 64⟩) (beforeCall : x = ⟨64,w⟩) : y = ⟨64,w⟩ := by
  rw [beforeCall,Value.get_mk] at fromCall
  exact fromCall

theorem returnedRegisters {fr : Activation} {b : Registers} {m : Ram} {d : Nat}
    {out : Output Value Ram Reg.count}
    (s : ScalarRegisters fr b d) (r : Returned fr b m d out) : ScalarRegisters fr out.values d :=
  ⟨savedWord (x := b[5]) r.done_.2.2.2.1 s.r5,
   savedWord (x := b[3]) r.done_.2.2.1 s.r3,
   savedWord (x := b[13]) r.done_.2.2.2.2.2.1 s.r13,
   savedWord (x := b[12]) r.done_.2.2.2.2.1 s.r12,
   savedWord (x := b[14]) r.done_.2.2.2.2.2.2.1 s.r14,
   savedWord (x := b[15]) r.done_.2.2.2.2.2.2.2.1 s.r15⟩

theorem returnedFrame {fr : Activation} {initial b : Registers} {m : Ram} {d : Nat}
    {out : Output Value Ram Reg.count} (e : CoreEntry fr initial d) (r : Returned fr b m d out) :
    RamWriteFrame m out.store (writes fr spans) :=
  (stagedFrame e m (v d)).trans r.frame (childWithin e (i := 0x2b0) (depth := 128) (size := 120)
    (by decide) (by decide) (by decide))

theorem returnedContext {fr : Activation} {initial a b : Registers} {m : Ram} {d : Nat}
    {out : Output Value Ram Reg.count} (e : CoreEntry fr initial d) (old : Context fr a m)
    (saved : SavedWidths out.values) (r : Returned fr b m d out) : Context fr out.values out.store := by
  apply old.advance e (returnedFrame e r) (by decide) (by decide +kernel) r.widths saved
  obtain ⟨rsp,df,mx,ft,fc,_⟩ := old.atoms
  obtain ⟨osp,odf,_,_,_,_,_,_,omx,oft,ofc,_⟩ := r.done_
  change out.values[4] = ⟨64,sp fr-8+8⟩ at osp
  rw [BitVec.sub_add_cancel] at osp
  rintro ⟨i,hi⟩ hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · exact osp.trans rsp.symm
  · exact odf.trans df.symm
  · exact omx.trans mx.symm
  · exact oft.trans ft.symm
  · exact ofc.trans fc.symm

theorem comparedInput {fr : Activation} {initial a b : Registers} {m : Ram} {d : Nat}
    {out : Output Value Ram Reg.count} (e : CoreEntry fr initial d) (old : Context fr a m)
    (args : ScalarRegisters fr b d) (r : Returned fr b m d out) : ComparedInput fr out.values out.store d := by
  have s := returnedRegisters args r
  exact ⟨returnedContext e old s.widths r,r.endo,s.r5,s.r3,s.r13,s.r12,s.r14,s.r15,restoredSlots (m := m) (d := d) e r.frame⟩

end Start

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
