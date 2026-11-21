import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Refine X86Proofs.Lift

theorem adjust_rangeApart_bounds {a b : BitVec 64} {n m : Nat}
    (hn : 0 < n) (hm : 0 < m)
    (h : RangeApart a n b m) : a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat := by
  by_cases h1 : a.toNat + n ≤ b.toNat
  · exact Or.inl h1
  by_cases h2 : b.toNat + m ≤ a.toNat
  · exact Or.inr h2
  exfalso
  have hn64 : max a.toNat b.toNat < 2^64 := by omega
  have he := h (max a.toNat b.toNat - a.toNat) (by omega)
    (max a.toNat b.toNat - b.toNat) (by omega)
  apply he
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := max a.toNat b.toNat - a.toNat) (by omega),
    Nat.mod_eq_of_lt (a := max a.toNat b.toNat - b.toNat) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat + (max a.toNat b.toNat - a.toNat)) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat + (max a.toNat b.toNat - b.toNat)) (by omega)]
  omega

theorem adjust_stack_state (pc : BitVec 64) (v : Value) (mem : Ram) :
    stackPtr (stateOf pc [(Reg.gpr 4, v)] mem) = v.get 64 := by
  change ((Reg.gpr 4).read (stateOf pc [(Reg.gpr 4, v)] mem)).get 64 = v.get 64
  rw [read_stateOf_cons]
  simp only [ite_true, Reg.read_write_gpr, Value.get_mk_setWidth, BitVec.setWidth_eq]

theorem adjust_call_rsp (pc ret : BitVec 64) (am : AddrMode)
    (args : Values Value Reg.count) (mem : Ram)
    (hret : ret = pc + BitVec.ofNat 64 (callMemLen am)) :
    (EffectPart.reg (.gpr 4)).value
      (callEffect (callMemPtr pc am) ret
        (stateOf pc [(Reg.gpr 4, args[4])] mem))
      (stateOf pc [(Reg.gpr 4, args[4])] mem) = ⟨64, args[4].get 64 - 8⟩ := by
  subst ret
  calc
    _ = ⟨64, stackPtr (stateOf pc [(Reg.gpr 4, args[4])] mem) - 8⟩ :=
      callMemEffect_rsp pc am _ _
    _ = _ := congrArg (fun p : BitVec 64 ↦ (⟨64, p - 8⟩ : Value))
      (adjust_stack_state pc args[4] mem)

end AesGcm.Proofs.Machine.AES16.KeySchedule
