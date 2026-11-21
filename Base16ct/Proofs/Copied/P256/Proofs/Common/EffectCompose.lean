import X86Proofs.Program.Compose

set_option autoImplicit false

register_simp_attr x86_local_on

open X86Proofs

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.EffectCompose

open X86 X86.Machine X86.UserProcess

@[x86_compose] theorem Effect.cf_after (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).RFLAGS.extractLsb' 0 1 = BitVec.ofBool ((e.flag s .CF).getD b) := by
  have hf := e.after_flag s b .CF
  change (e.after s b).RFLAGS.getLsbD 0 = _ at hf
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he : i = 0 := by omega
  subst he
  simpa only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, Nat.zero_lt_succ,
    decide_true, Bool.true_and, Nat.add_zero] using hf

@[x86_compose] theorem Effect.gpr_after (e : Effect) (s : RamState) (b : Bool) (r : BitVec 5) :
    (e.after s b).GPR[gprIndex r] = (Operand.reg r : Operand 64).read (applyWrites s e.writes) := rfl

theorem Effect.Local.of_eq {e : RamState → Effect}
    (same : ∀ t t', Obs t t' → e t = e t')
    (full : ∀ t, ∀ w ∈ (e t).writes, w.Full) : Effect.Local e := by
  refine ⟨fun t t' ho => congrArg Effect.rip (same t t' ho),
    fun t t' ho => congrArg Effect.writes (same t t' ho),
    fun t t' ho => congrArg (fun x => x.flags.isSome) (same t t' ho), ?_, full⟩
  intro t t' ho i hi
  rw [same t t' ho]
  unfold Effect.flag
  cases (e t').flags <;> simp only [hi]

end Base16ct.Proofs.Copied.P256.Proofs.Common.EffectCompose
