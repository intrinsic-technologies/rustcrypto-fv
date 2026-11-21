import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.State
import K256.Proofs.Ecdh.Decode.Convert.Barrier
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify.Core.Reduce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def resume (l : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨l,#v[],rfl,some ⟨64,ret⟩⟩

abbrev scratch (base : BitVec 64) : MemoryRegion := ⟨(base - 9).toNat, 9⟩

theorem barrier {l next : Label} {a b : Registers} {initial m : Ram} {base ret : BitVec 64}
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,a,initial⟩ =
      .call ⟨.l127d50,b,memStore m (base-8) ret⟩ (resume next ret))
    (rsp : b[4].get 64 = base-8) (win : Writable Extracted.programImage m (base-9) 9)
    (room : 9 ≤ base.toNat) (low : ret.toNat < 2^32) :
    ∃ c n, Reaches l a initial next c n ∧ c[4] = ⟨64,base⟩ ∧
      c[0] = ⟨64, ((b[7].get 64).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame m n [scratch base] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        c[i] = b[i] := by
  let pushed := memStore m (base-8) ret
  have retAt : memLoad pushed (base-8) 64 = ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have saved : RamWriteFrame m pushed [scratch base] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_,List.mem_cons_self,?_⟩
    change (base-9).toNat ≤ (base-8).toNat ∧ (base-8).toNat+8 ≤ (base-9).toNat+9 ∧ _
    bv_omega
  obtain ⟨out,step,tag,stack,flag,frame,kept⟩ := Sec1.Serialize.choiceBlock
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l127d50 x hx)) rsp
    ((win.of_offsets (show base-8-1 = base + (0-9) by bv_omega) (addr_sub base 9) (by decide)).memStore _ ret)
    ((win.readable.of_offsets (addr_sub base 8) (addr_sub base 9) (by decide)).memStore _ ret)
    (retAt ▸ low)
  let f : Sec1.LIR.Label → Label := fun _ => .l127d50
  have blocks : Generate.Serialize.Relabel.block f (Sec1.LIR.program.blocks .l127d50) =
      program.blocks .l127d50 := by rfl
  have run : program.runBlock (dialect Extracted.programImage) ⟨.l127d50,b,pushed⟩ = .returned out := by
    change (program.blocks _).eval _ _ _ = _
    rw [← blocks, Generate.Serialize.Relabel.eval_block]
    exact congrArg (Generate.Serialize.Relabel.transfer f) step
  have exec : program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,b,pushed⟩,[]⟩ out :=
    .done (by simp only [Program.step,run,CFG.Transfer.next])
  refine ⟨out.values,out.store,.step ?_ (ParseSignature.exec_reaches_resume exec (resume next ret) []
    (by rw [tag,retAt]; exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))),by simpa only [BitVec.sub_add_cancel] using stack,flag,
    saved.trans frame ?_,kept⟩
  · simp only [Program.sem,Program.step,call,CFG.Transfer.next,pushed,List.nil_append]
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_,?_⟩ <;> change _ ≤ _ <;> dsimp only [scratch] <;> bv_omega

end K256.Proofs.Verify.Core.Reduce
