import P256.Proofs.Projective.Multiply.Machine.Radix.Memory
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Progress

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open ProjectiveRadix
open Recenter (rawDigit)

def BytesAt (t : RamState) (address : BitVec 64) (n : Nat)
    (bytes : Nat → BitVec 8) : Prop :=
  ∀ i, i < n → (Operand.mem (address + BitVec.ofNat 64 i) : Operand 8).read t = bytes i

def digitComponents (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 6,.flags,.mem (stackPtr s-112) 65,.rip]

structure NibbleState [Bindings] (s t : RamState) (d : Nat) : Prop extends State s t where
  rip : t.RIP = 0x10ba30
  digits : BytesAt t (stackPtr s-112) 65 (rawDigit d)
  rax : (t.regValue .rax).setWidth 8 = BitVec.ofNat 8 (nibble d 0)
  rcx : t.regValue .rcx = 2

structure DigitsState [Bindings] (s t : RamState) (d : Nat) : Prop extends State s t where
  rip : t.RIP = 0x10ba6c
  digits : BytesAt t (stackPtr s-112) 65 (digitByte d)

theorem recoding_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, c.Covers a → (Component.mem (stackPtr s - 112) 65).Covers a)
    {offset len : Nat} (ho : offset ≤ 120) (hl : len ≤ offset + 8)
    (apart : offset + 65 ≤ 112 ∨ 112 + len ≤ offset) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have hd := stack_sub_toNat pre.stack (offset := 112) (by decide)
  change (stackPtr s - 112).toNat = (stackPtr s).toNat - 112 at hd
  have hr := stack_sub_toNat pre.stack (offset := offset) (by omega)
  have ranges : RangeApart (stackPtr s - 112) 65 (stackPtr s - BitVec.ofNat 64 offset) len := by
    apply RangeApart.of_toNat
    · rw [hd]
      omega
    · rw [hr]
      omega
    · rw [hd,hr]
      omega
  apply agrees.byte
  intro c hc covered
  obtain ⟨j,hj,he⟩ := memory c hc _ covered
  exact ranges j hj i hi he.symm

theorem digit_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (agrees : AgreesExcept (digitComponents s) t u)
    {offset len : Nat} (ho : offset ≤ 120) (hl : len ≤ offset + 8)
    (apart : offset + 65 ≤ 112 ∨ 112 + len ≤ offset) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply recoding_byte pre agrees ?_ ho hl apart hi
  intro c hc a covered
  simp only [digitComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact covered | exact covered.elim

theorem frame_after_digits [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t)
    (ready : ReadyToStep u) (ag : AgreesExcept (digitComponents s) t u) : State s u := by
  apply state.after_stack pre ready ag
  · intro c hc hm
    simp only [digitComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all [registers,Component.isMem]
  · intro p n hc
    simp only [digitComponents,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,
      false_or,or_false,Component.mem.injEq] at hc
    obtain ⟨rfl,rfl⟩ := hc
    exact ⟨112,by decide,by decide,rfl⟩
  · exact (ag.read (n := 64) (r := 4) (by simp [digitComponents])).trans state.rsp

end P256.Proofs.Projective.Multiply.Machine.Radix
