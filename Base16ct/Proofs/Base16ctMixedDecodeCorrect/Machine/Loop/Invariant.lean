import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Program
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

def mixedLoopChanges (address : BitVec 64) (length : Nat) : List Component :=
  [.reg 6, .reg 3, .reg 5, .reg 0, .reg 8, .reg 10, .reg 11, .reg 14, .flags, .rip,
    .mem address length]

def mixedLoopPC (input : List UInt8) : BitVec 64 :=
  if input = [] then 0x1002ec else 0x1001f0

structure MixedLoopPre (src dst : BitVec 64) (index : Nat) (input : List UInt8)
    (s : RamState) : Prop where
  rip : s.RIP = mixedLoopPC input
  lengthBound : index + input.length / 2 < 2 ^ 64
  r9 : s.regValue .r9 = BitVec.ofNat 64 (index + input.length / 2)
  rax : s.regValue .rax = BitVec.ofNat 64 index
  rdi : s.regValue .rdi = src
  rcx : s.regValue .rcx = dst
  accumulator : s.regValue .rsi = 0 ∨ s.regValue .rsi = 255
  source : MemReadable s (src + BitVec.ofNat 64 (2 * index)) input.length
  bytes : ∀ j (hj : j < input.length),
    s.external[src + BitVec.ofNat 64 (2 * index) + BitVec.ofNat 64 j]? = some input[j]
  output : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (dst + BitVec.ofNat 64 index) (input.length / 2)
  avoid : ∀ j < input.length / 2, ¬ InProgram (dst + BitVec.ofNat 64 index + BitVec.ofNat 64 j)
  apart : RangeApart (src + BitVec.ofNat 64 (2 * index)) input.length
    (dst + BitVec.ofNat 64 index) (input.length / 2)

theorem mixedLoopChanges_trans {s t u : RamState} {address : BitVec 64} {length : Nat}
    (hFirst : AgreesExcept (mixedLoopChanges address 1) s t)
    (hRest : AgreesExcept (mixedLoopChanges (address + 1#64) length) t u) :
    AgreesExcept (mixedLoopChanges address (length + 1)) s u := by
  apply (hFirst.trans hRest).widen
  · intro c hc hm
    simp only [mixedLoopChanges, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc ⊢
    rcases hc with hc | hc
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem]
  · intro x c hc hcov
    simp only [mixedLoopChanges, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with hc | hc
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      obtain ⟨i, hi, he⟩ := hcov
      refine ⟨.mem address (length + 1), by simp [mixedLoopChanges], i, by omega, he⟩
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      obtain ⟨i, hi, he⟩ := hcov
      refine ⟨.mem address (length + 1), by simp [mixedLoopChanges], 1 + i, by omega, ?_⟩
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he

theorem mixedLoopChanges_preserve_head {s t : RamState} {address : BitVec 64} {length : Nat}
    (h : AgreesExcept (mixedLoopChanges (address + 1#64) length) s t)
    (hLength : length + 1 < 2 ^ 64) : t.external[address]? = s.external[address]? := by
  apply h.byte
  intro c hc hcov
  simp only [mixedLoopChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  obtain ⟨i, hi, he⟩ := hcov
  have hz : (0#64 : BitVec 64) = BitVec.ofNat 64 (1 + i) := by
    apply (BitVec.add_right_inj address).mp
    simpa only [BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add] using he
  have hn := congrArg BitVec.toNat hz
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 1 + i < 2 ^ 64 by omega)] at hn
  omega

theorem MixedLoopPre.next {src dst : BitVec 64} {index : Nat} {hi lo : UInt8}
    {input : List UInt8} {s t : RamState}
    (h : MixedLoopPre src dst index (hi :: lo :: input) s)
    (hFrame : AgreesExcept (mixedLoopChanges (dst + BitVec.ofNat 64 index) 1) s t)
    (hRip : t.RIP = mixedLoopPC input)
    (hRax : t.regValue .rax = BitVec.ofNat 64 (index + 1))
    (hAcc : t.regValue .rsi = 0 ∨ t.regValue .rsi = 255) :
    MixedLoopPre src dst (index + 1) input t := by
  have hLength : (hi :: lo :: input).length / 2 = input.length / 2 + 1 := by
    simp only [List.length_cons]
    omega
  have hSrc : src + BitVec.ofNat 64 (2 * (index + 1)) =
      src + BitVec.ofNat 64 (2 * index) + BitVec.ofNat 64 2 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2 <;> omega
  have hDst : dst + BitVec.ofNat 64 (index + 1) =
      dst + BitVec.ofNat 64 index + 1#64 := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨hRip, ?_, ?_, hRax, ?_, ?_, hAcc, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.lengthBound
    rw [hLength] at this
    omega
  · have hr := hFrame.read (n := 64) (r := 9) (by simp [mixedLoopChanges])
    change t.regValue .r9 = s.regValue .r9 at hr
    rw [hr, h.r9, hLength]
    congr 1
    omega
  · exact (hFrame.read (n := 64) (r := 7) (by simp [mixedLoopChanges])).trans h.rdi
  · exact (hFrame.read (n := 64) (r := 1) (by simp [mixedLoopChanges])).trans h.rcx
  · rw [hSrc]
    exact readable_of_agrees (readable_sub h.source 2 input.length
      (by simp only [List.length_cons]; omega)) hFrame
  · intro j hj
    have hb : s.external[src + BitVec.ofNat 64 (2 * index) + BitVec.ofNat 64 (2 + j)]? =
        some input[j] := by
      simpa only [Nat.add_comm 2 j, List.getElem_cons_succ] using
        h.bytes (2 + j) (by simp only [List.length_cons]; omega)
    rw [hSrc, BitVec.add_assoc, ← BitVec.ofNat_add]
    refine (hFrame.byte ?_).trans hb
    intro c hc hcov
    simp only [mixedLoopChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    obtain ⟨k, hk, he⟩ := hcov
    exact h.apart (2 + j) (by simp; omega) k (by rw [hLength]; omega) he
  · rw [hDst]
    exact writable_of_agrees (writable_sub h.output 1 (input.length / 2)
      (by rw [hLength]; omega)) hFrame
  · intro j hj
    rw [hDst, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.avoid (1 + j) (by rw [hLength]; omega)
  · intro j hj k hk
    rw [hSrc, hDst]
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] using
      h.apart (2 + j) (by simp only [List.length_cons]; omega) (1 + k)
        (by rw [hLength]; omega)

theorem MixedLoopPre.next_rip {src dst : BitVec 64} {index : Nat} {hi lo : UInt8}
    {input : List UInt8} {s : RamState}
    (h : MixedLoopPre src dst index (hi :: lo :: input) s)
    (hEven : input.length % 2 = 0) :
    (if s.regValue .r9 = s.regValue .rax + 1#64 then 0x1002ec else 0x1001f0) =
      mixedLoopPC input := by
  rw [h.r9, h.rax, ← BitVec.ofNat_add]
  by_cases hNil : input = []
  · subst input
    simp [mixedLoopPC]
  · have hPos : 0 < input.length / 2 := by
      have hNe : input.length ≠ 0 := fun hz ↦ hNil (List.length_eq_zero_iff.mp hz)
      omega
    have hLength : (hi :: lo :: input).length / 2 = input.length / 2 + 1 := by
      simp only [List.length_cons]
      omega
    have hNe : BitVec.ofNat 64 (index + (hi :: lo :: input).length / 2) ≠
        BitVec.ofNat 64 (index + 1) := by
      intro he
      have hn := congrArg BitVec.toNat he
      have hb := h.lengthBound
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (show index + 1 < 2 ^ 64 by rw [hLength] at hb; omega)] at hn
      rw [hLength] at hn
      omega
    simp only [hNe, ite_false, mixedLoopPC, hNil]

theorem MixedLoopPre.read_pair {src dst : BitVec 64} {index : Nat} {hi lo : UInt8}
    {input : List UInt8} {s : RamState}
    (h : MixedLoopPre src dst index (hi :: lo :: input) s) :
    MemReadable s (s.regValue .rdi + s.regValue .rax * 2#64) 1 ∧
      (Operand.mem (s.regValue .rdi + s.regValue .rax * 2#64) : Operand 8).read s = hi.toBitVec ∧
      MemReadable s (s.regValue .rdi + s.regValue .rax * 2#64 + 1#64) 1 ∧
      (Operand.mem (s.regValue .rdi + s.regValue .rax * 2#64 + 1#64) : Operand 8).read s =
        lo.toBitVec := by
  have hAddr : s.regValue .rdi + s.regValue .rax * 2#64 =
      src + BitVec.ofNat 64 (2 * index) := by
    rw [h.rdi, h.rax, ← BitVec.ofNat_mul, Nat.mul_comm index 2]
  rw [hAddr]
  have hHi := h.bytes 0 (by simp)
  have hLo := h.bytes 1 (by simp)
  simp only [BitVec.add_zero, List.getElem_cons_zero] at hHi
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hLo
  refine ⟨?_, ?_, readable_sub h.source 1 1 (by simp), ?_⟩
  · simpa only [BitVec.add_zero] using readable_sub h.source 0 1 (by simp)
  · change memLoad s.external _ 8 = hi.toBitVec
    rw [memLoad_8]
    change ((s.external[src + BitVec.ofNat 64 (2 * index)]?).getD (0 : UInt8)).toBitVec =
      hi.toBitVec
    rw [hHi]
    rfl
  · change memLoad s.external _ 8 = lo.toBitVec
    rw [memLoad_8]
    change ((s.external[src + BitVec.ofNat 64 (2 * index) + 1#64]?).getD (0 : UInt8)).toBitVec =
      lo.toBitVec
    rw [hLo]
    rfl

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
