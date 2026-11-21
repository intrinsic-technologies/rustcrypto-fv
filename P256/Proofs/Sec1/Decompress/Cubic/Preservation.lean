import P256.Proofs.Sec1.Decompress.Cubic.Support

set_option autoImplicit false


namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Proofs.Program P256.Proofs.Field P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def preservedWindows : List (Nat × Nat) := [(288,32), (332,4), (224,8)]

def PreservesInputs (s t u : RamState) : Prop :=
  (∀ r ∈ [Syntax.Reg.rbp, .r14], u.regValue r = t.regValue r) ∧
  (∀ window ∈ preservedWindows, ∀ i < window.2,
    u.external[stackPtr s - BitVec.ofNat 64 window.1 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 window.1 + BitVec.ofNat 64 i]?)

theorem PreservesInputs.trans {s t u v : RamState}
    (h : PreservesInputs s t u) (h' : PreservesInputs s u v) : PreservesInputs s t v :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr),
    fun w hw i hi => (h'.2 w hw i hi).trans (h.2 w hw i hi)⟩

theorem PreservesInputs.of_registers {s t u : RamState} {cs : List Component}
    (h : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (rbp : .reg 5 ∉ cs) (r14 : .reg 14 ∉ cs) :
    PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.read (n := 64) rbp
    · exact h.read (n := 64) r14
  · intro w hw i hi
    rw [h.external memory]

theorem PreservesInputs.of_copy {s t u : RamState}
    (h : AgreesExcept [.reg 0, .reg 1, .rip, .mem (stackPtr s - 408) 32] t u) :
    PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.read (n := 64) (r := 5) (by simp)
    · exact h.read (n := 64) (r := 14) (by simp)
  · intro w hw i hi
    apply h.byte
    intro c hc hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    obtain ⟨j,hj,he⟩ := hv
    have addr (off : Nat) (ho : off ≤ 408) : stackPtr s - BitVec.ofNat 64 off =
        stackPtr s - 408 + BitVec.ofNat 64 (408-off) := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 408 off (by omega) ho]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(408 : BitVec 64)),
        show -(408 : BitVec 64) + 408#64 = 0#64 by decide +kernel, BitVec.zero_add]
    simp only [preservedWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    all_goals
      simp only at hi he
      rw [addr _ (by decide)] at he
    · exact RangeApart.offsets (stackPtr s - 408) (a := 0) (b := 120) (len := 32) (count := 32)
        (by decide) (by decide) (.inl (by decide)) j hj i hi (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm)
    · exact RangeApart.offsets (stackPtr s - 408) (a := 0) (b := 76) (len := 32) (count := 4)
        (by decide) (by decide) (.inl (by decide)) j hj i hi (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm)
    · exact RangeApart.offsets (stackPtr s - 408) (a := 0) (b := 184) (len := 32) (count := 8)
        (by decide) (by decide) (.inl (by decide)) j hj i hi (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm)

theorem PreservesInputs.of_call {s t u : RamState} {outputOffset : Nat}
    (hout : outputOffset ∈ [328,112,216,80])
    (regs : ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r)
    (bytes : ∀ offset len : Nat, offset ≤ 408 → len ≤ offset+8 →
      (offset+32 ≤ outputOffset ∨ outputOffset+len ≤ offset) → ∀ i < len,
      u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) :
    PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    apply regs r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro w hw i hi
    simp only [preservedWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hw with rfl | rfl | rfl
    all_goals apply bytes _ _ (by decide) (by decide) _ i hi
    all_goals rcases hout with rfl | rfl | rfl | rfl <;> decide

theorem PreservesInputs.montgomery {s t u : RamState} {x : Nat}
    (h : PreservesInputs s t u) (hx : MontgomeryAt t (stackPtr s-288) x) :
    MontgomeryAt u (stackPtr s-288) x :=
  ⟨hx.1, hx.2.1, fun i hi => (h.2 (288,32) (by simp [preservedWindows]) i hi).trans (hx.2.2 i hi)⟩

theorem PreservesInputs.read {s t u : RamState} {offset n : Nat}
    (h : PreservesInputs s t u) (hw : (offset,n/8) ∈ preservedWindows) :
    (Operand.mem (stackPtr s-BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s-BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0
  rw [h.2 (offset,n/8) hw i hi]

end P256.Proofs.Sec1.Decompress.Cubic
