import K256.Proofs.Verify.Core.Lincomb.Prepare.State
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Common.Lift.Generated.Values.Register2

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

structure SecondDoubleCall (b c : Registers) (m : Ram) (q tables : BitVec 64) : Prop where
  run : program.runBlock (dialect Extracted.programImage) ⟨.l10f8ee,b,m⟩ =
    .call ⟨.l110cd0,c,memStore (memCopy m (tables+0x348) (q+0x178) 120) (q-8) (0x10f918 : BitVec 64)⟩
      ⟨.l10f918,#v[],rfl,some ⟨64,0x10f918⟩⟩
  rsp : c[4] = ⟨64,q-8⟩
  dst : c[7] = ⟨64,q+0x38⟩
  src : c[6] = ⟨64,q+0x1f0⟩
  acc : c[14] = ⟨64,q+0x1f0⟩
  delta : c[15] = ⟨64,q+0x38⟩
  keep : ∀ k : Fin Reg.count, k.val ∈ [3,5,12,13,22,39,50,51] → c[k] = b[k]

theorem secondDoubleCall {b : Registers} {m : Ram} {q tables : BitVec 64}
    (sp : b[4].get 64 = q) (table : b[3].get 64 = tables) (acc : b[14].get 64 = q+0x178)
    (df : b[22].get 1 = 0) (src : Readable m (q+0x178) 120)
    (dst : Writable Extracted.programImage m (tables+0x348) 120)
    (sep : (q+0x178).toNat+120 ≤ (tables+0x348).toNat ∨ (tables+0x348).toNat+120 ≤ (q+0x178).toNat)
    (stack : Writable Extracted.programImage m (q-8) 8) :
    ∃ c, SecondDoubleCall b c m q tables := by
  have incl := fun x hx => Common.fnCode_subset_programImage x (code_l10f8ee x hx)
  have copy := Generate.Generator.Multiply.Prepare.copyGuard (count := 15) (size := 8) src
    (ParseSignature.storeOk_of_codeRange (off := 15) (len := 3) dst incl (by decide)) sep
  have w : Writable Extracted.programImage (memCopy m (tables+0x348) (q+0x178) 120) (q-8) 8 :=
    stack.memStore _ _
  have push := ParseSignature.storeOk_of_codeRange (off := 37) (len := 5) w incl (by decide)
  refine ⟨?_, ?run, ?sp, ?dst, ?src, ?acc, ?delta, ?keep⟩
  case run =>
    cfg_eval [sp,table,acc,df]
    refine Eq.trans (ite_eq_left (Or.inr copy)) ?_
    refine Eq.trans (ite_eq_left push) ?_
    rfl
  case sp => rfl
  case dst => rfl
  case src => rfl
  case acc => rfl
  case delta => rfl
  case keep =>
    rintro ⟨k,hk⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Prepare
