import P256.Proofs.Sec1.Decode.Result.Copy
import P256.Proofs.Sec1.Decode.Result.Select
import P256.Proofs.Sec1.Decode.Result.Branch
import P256.Proofs.Common.Memory.LoadByte
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem selection [Bindings] {original s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre original boundary bytes) (state : Frame original s)
    (rip : s.RIP = 0x10e632)
    (output : s.regValue .r15 = original.regValue .rdi) (zero : s.regValue .r12 = 0)
    (tag valid : UInt8)
    (tagByteInput : s.external[stackPtr original - 156]? = some tag)
    (validity : s.external[stackPtr original - 240]? = some valid)
    (tagValid : tag.toBitVec = 0 ∨ tag.toBitVec = 2 ∨ tag.toBitVec = 3 ∨
      tag.toBitVec = 4 ∨ tag.toBitVec = 5) :
    ∃ fuel t, Advances boundary fuel s t ∧ Frame original t ∧
      t.RIP = (if choice tag.toBitVec valid.toBitVec = 0 then 0x10e6a8 else 0x10e676) ∧
      t.regValue .r15 = original.regValue .rdi ∧
      (∀ i < 65, t.external[stackPtr original - 232 + BitVec.ofNat 64 i]? =
        s.external[stackPtr original - 312 + BitVec.ofNat 64 i]?) := by
  have tagAddress : stackPtr s + 156 = stackPtr original - 156 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have tagByte : memLoad s.external (stackPtr s + 156) 8 = tag.toBitVec := by
    rw [tagAddress]
    exact P256.Proofs.Common.Memory.memLoad8_of_byte tagByteInput
  obtain ⟨na, a, aa, ra, ia, axa, ga⟩ := route tag.toBitVec
    (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary rip
    (by
      rw [tagAddress]
      exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) state.allocated)
    tagByte tagValid
  have sa := state.after_registers pre ra ga (by simp [Component.Covers]) (by simp)
  have ma := ga.external (by simp [Component.Covers])
  obtain ⟨b, nb, ab, sb, ib, copied, gb⟩ := copy pre sa ia
  have rb := readyToStep sb.machine sb.bindingsSupported
  have validAddress : stackPtr b + 72 = stackPtr original - 240 :=
    ScalarFrame.scalar_stack_address sb.rsp (by decide) (by decide)
  have validByte : memLoad b.external (stackPtr b + 72) 8 = valid.toBitVec := by
    rw [validAddress]
    have read : memLoad b.external (stackPtr original - 240) 8 =
        memLoad a.external (stackPtr original - 240) 8 := by
      apply memLoad_agrees_apart gb
      intro address len member
      have eq : address = stackPtr original - 232 ∧ len = 72 := by simpa using member
      obtain ⟨rfl, rfl⟩ := eq
      exact stack_sub_apart pre.stack (a := 232) (b := 240) (na := 72) (nb := 1)
        (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
    rw [read, ma]
    exact P256.Proofs.Common.Memory.memLoad8_of_byte validity
  have axb : b.regValue .rax = tag.toBitVec.setWidth 64 :=
    (gb.read (n := 64) (r := 0) (by simp)).trans axa
  have zeroB : b.regValue .r12 = 0 :=
    ((ga.trans gb).read (n := 64) (r := 12) (by simp)).trans zero
  obtain ⟨c, bc, rc, ic, axc, gc⟩ := select tag.toBitVec valid.toBitVec
    rb sb.loaded pre.outerBoundary ib
    (by
      rw [validAddress]
      exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) sb.allocated) validByte axb zeroB
  have sc := sb.after_registers pre rc gc (by simp [Component.Covers]) (by simp)
  have mc := gc.external (by simp [Component.Covers])
  have outC : c.regValue .r15 = original.regValue .rdi :=
    (((ga.trans gb).trans gc).read (n := 64) (r := 15) (by simp)).trans output
  obtain ⟨t, ct, st, it, gt⟩ := branch pre sc (choice tag.toBitVec valid.toBitVec) ic axc
  refine ⟨na + nb + 5 + 4, t, ((aa.trans ab).trans bc).trans ct, st, it,
    (gt.read (n := 64) (r := 15) (by simp)).trans outC, ?_⟩
  intro i hi
  have memory : t.external[stackPtr original - 232 + BitVec.ofNat 64 i]? =
      c.external[stackPtr original - 232 + BitVec.ofNat 64 i]? := by
    apply gt.byte
    intro component member covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    exact stack_sub_apart pre.stack (a := 312) (b := 232) (na := 1) (nb := 65)
      (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm
  exact memory.trans (by rw [mc, copied i (by omega), ma])

end P256.Proofs.Sec1.Decode.Result
