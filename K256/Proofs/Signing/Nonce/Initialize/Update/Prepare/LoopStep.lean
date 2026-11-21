import K256.Proofs.Signing.UpdateV.Prepare.PadLoops
import K256.Proofs.Verify.LIR.Fn103f30
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.State

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

open UpdateV

abbrev padOrigin (rsp : BitVec 64) (second : Bool) := rsp + (if second then 40 else 152)

private abbrev stepPC (second outer : Bool) : BitVec 64 :=
  if second then (if outer then 0x1044c0 else 0x104410)
  else (if outer then 0x104090 else 0x103fe0)

private abbrev stepCode (second outer : Bool) : List UInt8 :=
  if second then (if outer then bytes_l1044c0 else bytes_l104410)
  else (if outer then bytes_l104090 else bytes_l103fe0)

private abbrev stride (second : Bool) : Nat := if second then 5 else 8

set_option maxHeartbeats 1500000 in
theorem padStep (second outer : Bool) {rspVal : BitVec 64} {a : Values Value Reg.count}
    {m : Ram} {j : Nat} (hj : j < 16) (rsp : a[4] = ⟨64, rspVal⟩)
    (index : a[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * j)⟩)
    (wr : Writable Extracted.programImage m (padOrigin rspVal second + 8) 64) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨head second outer, a, m⟩ =
        .jump ⟨if j + 1 = 16 then exitLabel second outer else head second outer,
          b, xorPadFour (padOrigin rspVal second) (padMask outer) m (4 * j)⟩ ∧
      b[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * (j + 1))⟩ ∧
      (∀ i : Fin Reg.count, i.val ≠ 0 → i.val ≠ 19 → b[i] = a[i]) := by
  let sp := padOrigin rspVal second
  let mask := padMask outer
  let m₁ := xorPadByte sp mask m (4 * j)
  let m₂ := xorPadByte sp mask m₁ (4 * j + 1)
  let m₃ := xorPadByte sp mask m₂ (4 * j + 2)
  have code : ∀ x ∈ codeRange (stepPC second outer) (stepCode second outer), x ∈ Extracted.programImage := by
    cases second <;> cases outer
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l103fe0 x hx)
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l104090 x hx)
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l104410 x hx)
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l1044c0 x hx)
  have size : (stepCode second outer).length = 4 * stride second + 10 := by
    cases second <;> cases outer <;> rfl
  have guard {t : Ram} (w : Writable Extracted.programImage t (sp + 8) 64)
      (k : Nat) (hk : k < 4) :
      StoreOk Extracted.programImage t (padAddr sp (4 * j + k)) 1
        (stepPC second outer + BitVec.ofNat 64 (stride second * k)) (stride second) := by
    have low := w.readable.low
    have addr : (padAddr sp (4*j+k)).toNat = (sp+8).toNat + (4*j+k) := by
      rw [padAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4*j+k) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    exact ParseSignature.storeOk_of_codeRange (w.sub (by rw [addr]; omega) (by rw [addr]; omega))
      code (by rw [size]; cases second <;> simp only [stride, Bool.false_eq_true, ↓reduceIte] <;> omega)
  have g₀ := guard wr 0 (by decide)
  have w₁ : Writable Extracted.programImage m₁ (sp + 8) 64 := wr.memStore _ _
  have g₁ := guard w₁ 1 (by decide)
  have w₂ : Writable Extracted.programImage m₂ (sp + 8) 64 := w₁.memStore _ _
  have g₂ := guard w₂ 2 (by decide)
  have w₃ : Writable Extracted.programImage m₃ (sp + 8) 64 := w₂.memStore _ _
  have g₃ := guard w₃ 3 (by decide)
  have spBits : a[4].get 64 = rspVal := congrArg (Value.get 64) rsp
  have indexBits : a[0].get 64 = BitVec.ofNat 64 (3 + 4 * j) :=
    congrArg (Value.get 64) index
  have incr : BitVec.ofNat 64 (3 + 4 * j) + 4 =
      BitVec.ofNat 64 (3 + 4 * (j + 1)) := by
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add, show 3 + 4 * j + 4 = 3 + 4 * (j + 1) by omega]
  have addr (k : Nat) :
      rspVal + BitVec.ofNat 64 (3 + 4 * j) + BitVec.ofNat 64 ((if second then 45 else 157) + k) =
        padAddr sp (4 * j + k) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    change _ = rspVal + _ + 8 + BitVec.ofNat 64 (4*j+k)
    cases second
    · change rspVal + BitVec.ofNat 64 (3 + 4*j + (157+k)) =
        rspVal + BitVec.ofNat 64 152 + BitVec.ofNat 64 8 + BitVec.ofNat 64 (4*j+k)
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact congrArg (fun v => rspVal + BitVec.ofNat 64 v) (by omega)
    · change rspVal + BitVec.ofNat 64 (3 + 4*j + (45+k)) =
        rspVal + BitVec.ofNat 64 40 + BitVec.ofNat 64 8 + BitVec.ofNat 64 (4*j+k)
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact congrArg (fun v => rspVal + BitVec.ofNat 64 v) (by omega)
  have done : (BitVec.ofNat 64 (3 + 4 * (j + 1)) == 0x43) = decide (j + 1 = 16) := by
    change decide (_ = (0x43 : BitVec 64)) = _
    rw [decide_eq_decide]
    constructor
    · intro h
      have eq := congrArg BitVec.toNat h
      change (3 + 4 * (j + 1)) % 2^64 = 67 at eq
      rw [Nat.mod_eq_of_lt (by omega)] at eq
      omega
    · intro h
      rw [h]
      rfl
  let b := (a.set 0 ⟨64, BitVec.ofNat 64 (3 + 4 * (j + 1))⟩).set 19
    (.ofBool (decide (j + 1 = 16)))
  refine ⟨b, ?_, ?_, ?_⟩
  · have addr0 := addr 0
    have addr1 := addr 1
    have addr2 := addr 2
    have addr3 := addr 3
    cases second <;> cases outer
    all_goals
      first
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 157 = padAddr sp (4*j+0) at addr0
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 45 = padAddr sp (4*j+0) at addr0
      first
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 158 = padAddr sp (4*j+1) at addr1
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 46 = padAddr sp (4*j+1) at addr1
      first
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 159 = padAddr sp (4*j+2) at addr2
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 47 = padAddr sp (4*j+2) at addr2
      first
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 160 = padAddr sp (4*j+3) at addr3
      | change rspVal + BitVec.ofNat 64 (3 + 4*j) + 48 = padAddr sp (4*j+3) at addr3
      first
      | change program.runBlock _ ⟨.l103fe0, a, m⟩ = _
      | change program.runBlock _ ⟨.l104090, a, m⟩ = _
      | change program.runBlock _ ⟨.l104410, a, m⟩ = _
      | change program.runBlock _ ⟨.l1044c0, a, m⟩ = _
    all_goals
      cfg_eval [spBits, indexBits]
      rw [addr0, addr1, addr2, addr3]
      split <;> try (rename_i ng; exact (ng g₀).elim)
      split <;> try (rename_i ng; exact (ng g₁).elim)
      split <;> try (rename_i ng; exact (ng g₂).elim)
      split <;> try (rename_i ng; exact (ng g₃).elim)
      rw [incr, cmpSpec_ZF, done]
      by_cases finish : j + 1 = 16
      all_goals
        simp only [finish, decide_true, decide_false, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ↓reduceIte]
        congr 2
        all_goals
          first
          | solve | simp only [finish, ↓reduceIte, head, exitLabel] <;> rfl
          | apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
              fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
            intro i
            finite_cases i <;> simp only [b, Vector.getElem_set, finish] <;> rfl
  · simp only [b, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  · intro i h₀ h₁₉
    simp only [b, Fin.getElem_fin, Vector.getElem_set, ite_eq_right (Ne.symm h₀), ite_eq_right (Ne.symm h₁₉)]

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
