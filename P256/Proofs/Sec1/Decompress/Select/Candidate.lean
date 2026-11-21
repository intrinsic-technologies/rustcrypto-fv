import P256.Proofs.Sec1.Decompress.Select.State
import P256.Proofs.Sec1.Decompress.Select.RootValue
import P256.Proofs.Sec1.Decompress.Select.Memory
import P256.Proofs.Sec1.Decompress.Select.RootSelect
import P256.Proofs.Sec1.Decompress.Select.Neg
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Select
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.Sec1.Decompress.Cubic (montgomeryAt_of_copy)
open P256.Proofs.Common.Memory (memLoad8_of_byte)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem candidate_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} {odd : Bool}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : RootState s t x odd) :
    ∃ fuel u, Advances boundary fuel t u ∧ CandidateState s u x odd := by
  let good := (P256.Spec.Operations.sqrtMod (P256.Spec.Points.curveRhs (checkedX x))).isSome
  have root : MontgomeryAt t (stackPtr s - 328) (candidateRoot x) ∧
      t.external[stackPtr s - 296]? = some (if good then 1 else 0) := by
    have address : stackPtr s - 328 + 32 = stackPtr s - 296 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    have h := squareRoot_fields state.root
    exact ⟨h.1, by simpa only [address] using h.2⟩
  obtain ⟨n2, b, run2, sb, ipb, zerob, frameb⟩ := zero_result pre state.toFrameState state.rip
  have r13b : b.regValue .r13 = stackPtr s - 328 :=
    (frameb.read (n := 64) (r := 13) (by simp [zeroComponents])).trans state.r13
  have rootb : MontgomeryAt b (stackPtr s - 328) (candidateRoot x) :=
    montgomeryAt_of_copy root.1 (fun i hi => zero_byte frameb
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) hi)
  have rawb : b.external[stackPtr s - 296]? = some (if good then 1 else 0) := by
    have hb := zero_byte frameb (offset := 296) (len := 1)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (i := 0) (by decide)
    simp only [BitVec.add_zero] at hb
    exact hb.trans root.2
  have choice : (Operand.mem (stackPtr s - 296) : Operand 8).read b = if good then 1 else 0 := by
    have h := memLoad8_of_byte rawb
    cases hg : good
    all_goals simp only [hg, Bool.false_eq_true, ite_false, ite_true] at h ⊢
    all_goals exact h
  obtain ⟨n3, c, run3, sc, ipc, r12c, r15c, rootc', abic, keepc⟩ :=
    select_result pre sb ipb r13b zerob rootb choice
  have selected : (if good then candidateRoot x else 0) = candidateRoot x :=
    root_selected (P256.Spec.Operations.sqrtMod (P256.Spec.Points.curveRhs (checkedX x)))
  have rootc : MontgomeryAt c (stackPtr s - 256) (candidateRoot x) := selected ▸ rootc'
  obtain ⟨n4, d, run4, sd, ipd, rootd, framed⟩ := copy_payload pre sc ipc rootc
  obtain ⟨n5, e, run5, se, ipe, r13e, negative, abie, keepe⟩ := neg_result pre sd ipd rootd
  have preserved (off len : Nat) (ho : off ≤ 408) (hl : len ≤ off+8)
      (hb : OffsetsApart (-(216 : BitVec 64)) 32 (-BitVec.ofNat 64 off) len)
      (hc : off+32 ≤ 256 ∨ 256+len ≤ off)
      (hd : OffsetsApart (-(408 : BitVec 64)) 32 (-BitVec.ofNat 64 off) len)
      (he : off+32 ≤ 112 ∨ 112+len ≤ off) (hlen : 32+len < 2^64)
      (i : Nat) (hi : i < len) :
      e.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? :=
    (keepe off len ho hl he i hi).trans ((copy_byte framed hd hlen hi).trans
      ((keepc off len ho hl hc i hi).trans (zero_byte frameb hb hlen hi)))
  have xc : MontgomeryAt e (stackPtr s - 288) (checkedX x) := by
    apply montgomeryAt_of_copy state.xCoordinate
    intro i hi
    exact preserved 288 32 (by decide) (by decide)
      (by unfold OffsetsApart; decide +kernel) (by decide)
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide) i hi
  have sign : (Operand.mem (stackPtr s - 332) : Operand 32).read e = BitVec.ofNat 32 odd.toNat := by
    apply Eq.trans _ state.parity
    apply stack_read_of_bytes
    intro i hi
    exact preserved 332 4 (by decide) (by decide)
      (by unfold OffsetsApart; decide +kernel) (by decide)
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide) i hi
  have output : (Operand.mem (stackPtr s - 224) : Operand 64).read e = s.regValue .rdi := by
    apply Eq.trans _ state.output
    apply stack_read_of_bytes
    intro i hi
    exact preserved 224 8 (by decide) (by decide)
      (by unfold OffsetsApart; decide +kernel) (by decide)
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide) i hi
  have roote : MontgomeryAt e (stackPtr s - 256) (candidateRoot x) := by
    apply montgomeryAt_of_copy rootc
    intro i hi
    exact (keepe 256 32 (by decide) (by decide) (by decide) i hi).trans
      (copy_byte framed (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  have bp : e.regValue .rbp = t.regValue .rbp := by
    rw [abie .rbp (by simp), show d.regValue .rbp = c.regValue .rbp from
      framed.read (n := 64) (r := 5) (by simp [copyComponents]), abic .rbp (by simp),
      show b.regValue .rbp = t.regValue .rbp from frameb.read (n := 64) (r := 5) (by simp [zeroComponents])]
  have r14 : e.regValue .r14 = t.regValue .r14 := by
    rw [abie .r14 (by simp), show d.regValue .r14 = c.regValue .r14 from
      framed.read (n := 64) (r := 14) (by simp [copyComponents]), abic .r14 (by simp),
      show b.regValue .r14 = t.regValue .r14 from frameb.read (n := 64) (r := 14) (by simp [zeroComponents])]
  have r12 : e.regValue .r12 = stackPtr s - 256 := by
    rw [abie .r12 (by simp), show d.regValue .r12 = c.regValue .r12 from
      framed.read (n := 64) (r := 12) (by simp [copyComponents]), r12c]
  have r15 : (e.regValue .r15).setWidth 8 = if good then 1 else 0 := by
    rw [abie .r15 (by simp), show d.regValue .r15 = c.regValue .r15 from
      framed.read (n := 64) (r := 15) (by simp [copyComponents])]
    exact r15c
  refine ⟨n2+n3+n4+n5, e, ((run2.trans run3).trans run4).trans run5, ?_⟩
  exact {
    toFrameState := se
    output := output
    parity := sign
    valid := bp.trans state.valid
    xCoordinate := xc
    rip := ipe
    base := r12
    negativeBase := r13e
    root := roote
    negative := negative
    rootValid := r15.trans (root_flag good)
    r14 := r14.trans state.r14 }

end P256.Proofs.Sec1.Decompress.Select
