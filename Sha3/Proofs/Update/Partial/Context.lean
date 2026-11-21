import Sha3.Proofs.Update.Partial.Absorb
import Sha3.Proofs.Update.Partial.Code
import Sha3.Proofs.Update.Frame

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def destination (pointer : BitVec 64) (position : Nat) : BitVec 64 :=
  pointer + BitVec.ofNat 64 position

structure Context [Bindings] (v : Variant) (pointer source : BitVec 64)
    (position count : Nat) (initial input : Nat → UInt8) (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  pointerReg : (Operand.reg 15 : Operand 64).read s = pointer
  sourceReg : (Operand.reg 3 : Operand 64).read s = source
  positionReg : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 position
  position_lt : position < v.rate
  count_le : position + count ≤ v.rate
  sourceBytes : Bytes s.external source count input
  stateBytes : Bytes s.external (destination pointer position) (200 - position) initial
  sourceLow : source.toNat + count ≤ 2 ^ 32
  stateLow : (destination pointer position).toNat + (200 - position) ≤ 2 ^ 32
  apart : RangeApart (destination pointer position) (200 - position) source count
  avoids : ∀ i < 200 - position,
    ¬ (InProgram (destination pointer position + BitVec.ofNat 64 i) ∨
      InPageTables (destination pointer position + BitVec.ofNat 64 i))

def clobbers (pointer : BitVec 64) (position : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 3, .reg 10, .reg 15,
    .mem (destination pointer position) (200 - position), .flags, .rip]

theorem frame_trans {pointer : BitVec 64} {position : Nat} {s u t : RamState}
    (h : AgreesExcept (clobbers pointer position) s u)
    (h' : AgreesExcept (clobbers pointer position) u t) :
    AgreesExcept (clobbers pointer position) s t :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem Context.sourceBytes_of_frame [Bindings] {v : Variant} {pointer source : BitVec 64}
    {position count : Nat} {initial input : Nat → UInt8} {s t : RamState}
    (hc : Context v pointer source position count initial input s)
    (hframe : AgreesExcept (clobbers pointer position) s t) :
    Bytes t.external source count input := by
  apply hc.sourceBytes.of_agreesExcept hframe
  intro i hi c hcm hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨j, hj, he⟩ := hcover
  exact hc.apart j hj i hi he.symm

theorem stateWrites_clobbers (initial : RamState) (position : Nat) :
    StateWrites initial (clobbers (initial.regValue .rsi) position) := by
  intro c hcm address hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨j, hj, rfl⟩ := hcover
  refine ⟨position + j, by omega, ?_⟩
  simp only [destination, BitVec.add_assoc, BitVec.ofNat_add]

theorem bodyInvariant_of_frame [Bindings] {v : Variant} {caller s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} {position : Nat}
    (hc : CallContext v caller bytes state) (hi : BodyInvariant caller s)
    (hr : ReadyToStep t) (hf : AgreesExcept (clobbers (caller.regValue .rsi) position) s t) :
    BodyInvariant caller t :=
  hi.of_stateWrites hc hr hf (stateWrites_clobbers caller position)
    (by simp [clobbers])

structure ShortResult [Bindings] (v : Variant) (pointer : BitVec 64) (position count : Nat)
    (initial input : Nat → UInt8) (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = cursorWriteAddress v
  cursorReg : (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (position + count)
  pointerReg : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s
  stateBytes : Bytes t.external (destination pointer position) (200 - position)
    (fun i ↦ initial i ^^^ (if i < count then input i else 0))
  frame : AgreesExcept (clobbers pointer position) s t

structure FillResult [Bindings] (v : Variant) (pointer source : BitVec 64)
    (position count : Nat) (initial input : Nat → UInt8) (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = v.updateAddress + 0xe7#64
  pointerReg : (Operand.reg 7 : Operand 64).read t = pointer
  sourceReg : (Operand.reg 3 : Operand 64).read t = source + BitVec.ofNat 64 count
  lanesReg : (Operand.reg 15 : Operand 64).read t = pointer
  stateBytes : Bytes t.external (destination pointer position) (200 - position)
    (fun i ↦ initial i ^^^ (if i < count then input i else 0))
  frame : AgreesExcept (clobbers pointer position) s t

end Sha3.Proofs.Update.Partial
