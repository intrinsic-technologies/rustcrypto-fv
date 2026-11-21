import P256.Proofs.Projective.Double.Memory
import P256.Proofs.Field.Representation
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false



namespace P256.Proofs.Projective.Double.CrossTerms

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scratchComponents (s : RamState) (rs : List (BitVec 5)) (len : Nat := 64) : List Component :=
  rs.map Component.reg ++ [.rip, .mem (stackSlot s 8) len]

theorem scratch_trans {s t u v : RamState} {rs : List (BitVec 5)} {len : Nat}
    (h : AgreesExcept (scratchComponents s rs len) t u)
    (h' : AgreesExcept (scratchComponents s rs len) u v) :
    AgreesExcept (scratchComponents s rs len) t v :=
  (h.trans h').mono (by simp)

theorem scratch_reg {s t u : RamState} {rs : List (BitVec 5)} {len : Nat} {r : BitVec 5}
    (h : AgreesExcept [.reg r, .rip] t u) (hr : r ∈ rs) :
    AgreesExcept (scratchComponents s rs len) t u := by
  apply h.mono
  simp [scratchComponents, hr]

theorem slot_add (s : RamState) (a b : Nat) :
    stackSlot s a + BitVec.ofNat 64 b = stackSlot s (a+b) := by
  simp only [stackSlot, BitVec.ofNat_add, BitVec.add_assoc]

theorem scratch_store {s t u : RamState} {rs : List (BitVec 5)} {len : Nat} {offset : Nat}
    (h : AgreesExcept [.mem (stackSlot s offset) 8, .rip] t u)
    (lo : 8 ≤ offset) (hi : offset + 8 ≤ 8+len) :
    AgreesExcept (scratchComponents s rs len) t u := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hc hm
    apply h.agree c ?_ hm
    intro member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · contradiction
    · exact hc (by simp [scratchComponents])
  · intro a ha
    apply h.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi', rfl⟩ := covered
      apply ha (.mem (stackSlot s 8) len) (by simp [scratchComponents])
      refine ⟨offset-8+i, by omega, ?_⟩
      rw [slot_add, slot_add]
      congr 1
      omega
    · exact covered.elim

theorem scratch_byte {s t u : RamState} {rs : List (BitVec 5)} {len : Nat} {a : BitVec 64}
    (h : AgreesExcept (scratchComponents s rs len) t u)
    (ha : ¬ (Component.mem (stackSlot s 8) len).Covers a) : u.external[a]? = t.external[a]? := by
  apply h.byte
  intro c hc hv
  simp only [scratchComponents, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨r, _, rfl⟩ | rfl | rfl
  · exact hv.elim
  · exact hv.elim
  · exact ha hv

theorem scratch_read {s t u : RamState} {rs : List (BitVec 5)} {len : Nat} {a : BitVec 64}
    (h : AgreesExcept (scratchComponents s rs len) t u)
    (apart : RangeApart (stackSlot s 8) len a 8) :
    memLoad u.external a 64 = memLoad t.external a 64 := by
  apply memLoad_congr
  intro i hi
  change (u.external[a + BitVec.ofNat 64 i]?).getD 0 = (t.external[a + BitVec.ofNat 64 i]?).getD 0
  congr 1
  apply scratch_byte h
  rintro ⟨j, hj, he⟩
  exact apart j hj i hi he.symm

theorem scratch_montgomery {s t u : RamState} {rs : List (BitVec 5)} {len : Nat} {a : BitVec 64} {x : Nat}
    (h : AgreesExcept (scratchComponents s rs len) t u)
    (apart : RangeApart (stackSlot s 8) len a 32)
    (hx : MontgomeryAt t a x) : MontgomeryAt u a x := by
  apply hx.of_bytes_eq
  intro i hi
  apply scratch_byte h
  rintro ⟨j, hj, he⟩
  exact apart j hj i hi he.symm

theorem slots_apart {s : RamState} {a b m n : Nat}
    (ha : a+m ≤ 2^64) (hb : b+n ≤ 2^64) (apart : a+m ≤ b ∨ b+n ≤ a) :
    RangeApart (stackSlot s a) m (stackSlot s b) n :=
  RangeApart.offsets _ ha hb apart

theorem scratch_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {rs : List (BitVec 5)} {len : Nat} {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (h : AgreesExcept (scratchComponents s rs len) t u)
    (bound : 8+len ≤ 728)
    (hx : ProjectiveAt t (s.regValue .rdi) point) : ProjectiveAt u (s.regValue .rdi) point := by
  refine ⟨scratch_montgomery h ?_ hx.1, scratch_montgomery h ?_ hx.2.1,
    scratch_montgomery h ?_ hx.2.2⟩
  · simpa only [BitVec.add_zero] using stack_point_apart pre (offset := 8) (len := len)
      (poffset := 0) (plen := 32) bound (by decide)
  · exact stack_point_apart pre bound (by decide)
  · exact stack_point_apart pre bound (by decide)

theorem store_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    {offset : Nat} (bound : offset+56 ≤ 728) :
    WritesWithin [.mem (stackPtr t + BitVec.ofNat 64 offset) 8, .rip]
      #v[registerRegion s .rdi 96, workRegion s 1016] := by
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega)] at ha
    exact ⟨workRegion s 1016, by simp, work_contains pre (by omega) (by omega) ha⟩
  · exact ha.elim

theorem copied [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {src : BitVec 64} {dst x : Nat} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s u 96 1016 728) (bound : dst+32 ≤ 728) (hx : MontgomeryAt t src x)
    (h0 : memLoad u.external (stackSlot s dst) 64 = memLoad t.external src 64)
    (h1 : memLoad u.external (stackSlot s (dst+8)) 64 = memLoad t.external (src+8) 64)
    (h2 : memLoad u.external (stackSlot s (dst+16)) 64 = memLoad t.external (src+16) 64)
    (h3 : memLoad u.external (stackSlot s (dst+24)) 64 = memLoad t.external (src+24) 64) :
    MontgomeryAt u (stackSlot s dst) x := by
  apply Field.montgomeryAt_of_memLoad_limbs hx.1
  · have h := stack_readable (frameOffset := 728) pre state (by decide) bound
    rw [state.rsp] at h
    exact h.mem
  · intro j hj
    rw [← hx.memLoad_limb j hj]
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.mul_zero, BitVec.reduceOfNat, BitVec.add_zero] using h0
    · rw [slot_add]
      exact h1
    · rw [slot_add]
      exact h2
    · rw [slot_add]
      exact h3

end P256.Proofs.Projective.Double.CrossTerms
