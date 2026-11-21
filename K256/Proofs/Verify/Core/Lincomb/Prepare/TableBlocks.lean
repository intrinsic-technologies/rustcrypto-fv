import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Common.Lift.Generated.Values.Register2

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def tableSite (second : Bool) (i : Fin 8) : Label :=
  (if second then
    #v[.l10f918,.l10f935,.l10f952,.l10f96f,.l10f98c,.l10f9a9,.l10f9c6,.l10f9e3]
   else
    #v[.l10f82a,.l10f843,.l10f85d,.l10f87a,.l10f897,.l10f8b4,.l10f8d1,.l10f8ee])[i]

abbrev tableSlot (tables : BitVec 64) (second : Bool) (i : Nat) :=
  tables + BitVec.ofNat 64 (120 * ((if second then 8 else 0) + i))

structure AdditionCall (second : Bool) (i : Fin 7) (a b : Registers) (m : Ram)
    (sp tables acc delta : BitVec 64) : Prop where
  run : let resume := tableSite second i.succ
        let copied := memCopy m (tableSlot tables second i.val) acc 120
        program.runBlock (dialect Extracted.programImage) ⟨tableSite second i.castSucc, a, m⟩ =
          .call ⟨.l10a410, b, memStore copied (sp - 8) (address resume)⟩
            ⟨resume, #v[], rfl, some ⟨64, address resume⟩⟩
  rsp : b[4] = ⟨64, sp - 8⟩
  destination : b[7] = ⟨64, acc⟩
  source : b[6] = ⟨64, delta⟩
  widths : ParseSignature.ArgumentWidths b
  keep : ∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[j] = a[j]

def AdditionBlock (second : Bool) (i : Fin 7) : Prop :=
  ∀ {a : Registers} {m : Ram} {sp tables acc delta : BitVec 64},
    a[4].get 64 = sp → a[3].get 64 = tables → a[14].get 64 = acc → a[15].get 64 = delta →
    a[22].get 1 = 0 → ParseSignature.ArgumentWidths a →
    let dst := tableSlot tables second i.val
    Readable m acc 120 → Writable Extracted.programImage m dst 120 →
    (acc.toNat + 120 ≤ dst.toNat ∨ dst.toNat + 120 ≤ acc.toNat) →
    Writable Extracted.programImage m (sp - 8) 8 →
    ∃ b, AdditionCall second i a b m sp tables acc delta

local macro "addition_block " l:term:max r:term:max off:num len:num incl:term:max : tactic => `(tactic| (
  intro a m sp tables acc delta rsp base cur dbl df widths dst read write apart slot
  change Writable _ m (tables + $off) 120 at write
  have includeCode := fun x hx => Common.fnCode_subset_programImage x ($incl x hx)
  have copy := Generate.Generator.Multiply.Prepare.copyGuard (count := 15) (size := 8) read
    (ParseSignature.storeOk_of_codeRange (off := $len - 14) (len := 3) write includeCode (by decide)) apart
  have slot' : Writable Extracted.programImage (memCopy m (tables + $off) acc 120) (sp - 8) 8 :=
    slot.memStore _ _
  have push := ParseSignature.storeOk_of_codeRange (off := $len - 5) (len := 5) slot' includeCode (by decide)
  refine ⟨?b, ?run, ?rsp, ?dest, ?src, ?widths, ?keep⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨$l, a, m⟩ =
      .call ⟨.l10a410, ?b, memStore (memCopy m (tables + $off) acc 120) (sp - 8) (address $r)⟩
        ⟨$r, #v[], rfl, some ⟨64, address $r⟩⟩
    simp only [address, Label.G12.address, Label.G13.address, BitVec.reduceSub, BitVec.add_zero] at copy push ⊢
    try simp only [show ∀ t : BitVec 64, t + 0 = t from BitVec.add_zero] at copy push ⊢
    cfg_eval [rsp,base,cur,dbl,df]
    refine Eq.trans (ite_eq_left (Or.inr copy)) ?_
    refine Eq.trans (ite_eq_left push) ?_
    rfl
  case rsp => rfl
  case dest => rfl
  case src => rfl
  case widths =>
    intro ⟨j,hj⟩ h
    have w := widths ⟨j,hj⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h|h|h|h|h|h <;> subst j <;> first | rfl | exact w
  case keep =>
    intro ⟨j,hj⟩ hj'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj'
    rcases hj' with h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl))

set_option maxHeartbeats 1600000 in
theorem additionBlock (second : Bool) (i : Fin 7) : AdditionBlock second i := by
  cases second <;> finite_cases i
  · addition_block .l10f82a .l10f843 0 25 code_l10f82a
  · addition_block .l10f843 .l10f85d 120 26 code_l10f843
  · addition_block .l10f85d .l10f87a 240 29 code_l10f85d
  · addition_block .l10f87a .l10f897 360 29 code_l10f87a
  · addition_block .l10f897 .l10f8b4 480 29 code_l10f897
  · addition_block .l10f8b4 .l10f8d1 600 29 code_l10f8b4
  · addition_block .l10f8d1 .l10f8ee 720 29 code_l10f8d1
  · addition_block .l10f918 .l10f935 960 29 code_l10f918
  · addition_block .l10f935 .l10f952 1080 29 code_l10f935
  · addition_block .l10f952 .l10f96f 1200 29 code_l10f952
  · addition_block .l10f96f .l10f98c 1320 29 code_l10f96f
  · addition_block .l10f98c .l10f9a9 1440 29 code_l10f98c
  · addition_block .l10f9a9 .l10f9c6 1560 29 code_l10f9a9
  · addition_block .l10f9c6 .l10f9e3 1680 29 code_l10f9c6

end K256.Proofs.Verify.Core.Lincomb.Prepare
