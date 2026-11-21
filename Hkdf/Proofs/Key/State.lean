import Hkdf.Proofs.Common.Machine
import Hkdf.Proofs.Common.CallFrame
import Hkdf.Proofs.Common.HMAC

set_option autoImplicit false

namespace Hkdf.Proofs.Key

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine

abbrev entryAddress : BitVec 64 := 0x116320
abbrev stackBytes : Nat := 720
abbrev localBytes : Nat := 376

def blockAddress (initial : RamState) : BitVec 64 := stackPtr initial - 376

def writeRegions (initial : RamState) : Vector MemoryRegion 2 :=
  #v[registerRegion initial .rdi 64, Stack.region initial stackBytes]

structure Context [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (key : ByteArray) : Prop extends
    CalleePre initial boundary entryAddress key.size 64 stackBytes where
  length : (initial.regValue .rdx).toNat = key.size
  bytes : (registerRegion initial .rsi key.size).HasBytes initial.external key

structure SavedStackAt (initial s : RamState) : Prop where
  words : ∀ slot ∈ ([(Syntax.Reg.r15, 8), (.r14, 16), (.r13, 24),
      (.r12, 32), (.rbx, 40)] : List (Syntax.Reg × Nat)),
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 slot.2) 64 =
      initial.regValue slot.1
  returnAddress : memLoad s.external (stackPtr initial) 64 =
    memLoad initial.external (stackPtr initial) 64

theorem SavedStackAt.of_agrees {initial s t : RamState} (saved : SavedStackAt initial s)
    (same : (Component.mem (stackPtr initial - 40) 48).Agrees s t) :
    SavedStackAt initial t := by
  constructor
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
        (width := 64) (offset := 32) same (by decide)
      have value := saved.words (.r15, 8) (by simp)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] at word value ⊢
      exact word.trans value
    · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
        (width := 64) (offset := 24) same (by decide)
      have value := saved.words (.r14, 16) (by simp)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] at word value ⊢
      exact word.trans value
    · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
        (width := 64) (offset := 16) same (by decide)
      have value := saved.words (.r13, 24) (by simp)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] at word value ⊢
      exact word.trans value
    · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
        (width := 64) (offset := 8) same (by decide)
      have value := saved.words (.r12, 32) (by simp)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] at word value ⊢
      exact word.trans value
    · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
        (width := 64) (offset := 0) same (by decide)
      have value := saved.words (.rbx, 40) (by simp)
      simp only [BitVec.sub_eq_add_neg, BitVec.reduceNeg, BitVec.add_zero] at word value ⊢
      exact word.trans value
  · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
      (width := 64) (offset := 40) same (by decide)
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, BitVec.add_zero] at word
    exact word.trans saved.returnAddress

structure State [bindings : Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (s : RamState) : Prop extends
    Hkdf.Proofs.Common.CallFrame.Running initial boundary (writeRegions initial) s where
  saved : SavedStackAt initial s
  rbp : s.regValue .rbp = initial.regValue .rbp
  mxcsr : s.MXCSR = initial.MXCSR
  fcw : s.FP87_Control = initial.FP87_Control

theorem State.of_observations [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} (state : State initial boundary s)
    (running : Hkdf.Proofs.Common.CallFrame.Running initial boundary (writeRegions initial) t)
    (saved : (Component.mem (stackPtr initial - 40) 48).Agrees s t)
    (rbp : t.regValue .rbp = s.regValue .rbp)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    State initial boundary t :=
  ⟨running, state.saved.of_agrees saved, rbp.trans state.rbp,
    mxcsr.trans state.mxcsr, fcw.trans state.fcw⟩

structure Prepared [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (s : RamState) : Prop extends State initial boundary s where
  rsp : stackPtr s = blockAddress initial
  outputPointer : s.regValue .rbx = initial.regValue .rdi
  inputPointer : s.regValue .rsi = initial.regValue .rsi
  inputLength : s.regValue .rdx = initial.regValue .rdx
  zeroBlock : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    ⟨Array.replicate 64 0⟩

structure Ready [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (key : ByteArray) (s : RamState) : Prop extends State initial boundary s where
  rip : s.RIP = 0x116639
  rsp : stackPtr s = blockAddress initial
  outputPointer : s.regValue .rbx = initial.regValue .rdi
  block : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    (Hkdf.Proofs.Common.HMAC.keyBlock key)

end Hkdf.Proofs.Key
