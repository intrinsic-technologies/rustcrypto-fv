import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Program
import Sha2.Proofs.Wrapper.Inputs
import Sha2.Proofs.Common.Machine.CallReturn
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.Machine.StackRegion
import Sha2.Proofs.Common.SHA256.Interfaces

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256

structure Context [bindings : Bindings] (initial : RamState) (inputs : Array Input)
    (v : Variant := .sha256) : Prop where
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings initial
  call : ValidCall v.routine initial inputs

structure SavedStackAt (initial s : RamState) : Prop where
  words : ∀ slot ∈ ([(Syntax.Reg.rbp, 8), (.r15, 16), (.r14, 24),
      (.r13, 32), (.r12, 40), (.rbx, 48)] : List (Syntax.Reg × Nat)),
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 slot.2) 64 =
      initial.regValue slot.1
  returnAddress : memLoad s.external (stackPtr initial) 64 =
    memLoad initial.external (stackPtr initial) 64

structure State [bindings : Bindings] (initial s : RamState) (v : Variant := .sha256) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  machine : SupportedMachine bindings s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  saved : SavedStackAt initial s
  directionFlag : DirectionFlagUnset s
  frame : MemoryWriteFrame initial s
    #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes]

structure Preserved [Bindings] (initial s : RamState) (v : Variant := .sha256) : Prop
    extends State initial s v where
  rsp : stackPtr s = stackPtr initial - 344
  outputPointer : memLoad s.external (stackPtr initial - 176) 64 = initial.regValue .rcx
  pointerTable : memLoad s.external (stackPtr initial - 168) 64 = initial.regValue .rdi
  lengthTable : memLoad s.external (stackPtr initial - 160) 64 = initial.regValue .rdx

structure Buffered [Bindings] (initial s : RamState) (message : ByteArray) (v : Variant := .sha256) : Prop
    extends Preserved initial s v where
  hashWords : HashStateAt s (stackPtr initial - 88)
    (compressBlocks v.initialHash message)
  tailBytes : (⟨(stackPtr initial - 152).toNat, message.size % 64⟩ : MemoryRegion).HasBytes
    s.external (message.extract (64 * (message.size / 64)) message.size)
  tailLength : s.external[stackPtr initial - 89]? = some (UInt8.ofNat (message.size % 64))
  blocks : memLoad s.external (stackPtr initial - 56) 64 = BitVec.ofNat 64 (message.size / 64)

structure LoopState [Bindings] (initial s : RamState) (inputs : Array Input) (index : Nat)
    (v : Variant := .sha256) : Prop
    extends Buffered initial s (prefixMessage inputs index) v where
  rip : s.RIP = v.pc 0xcd
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  countRegister : s.regValue .r15 = BitVec.ofNat 64 inputs.size
  remaining : index < inputs.size

structure Compressed [Bindings] (initial s : RamState) (message : ByteArray) (v : Variant := .sha256) : Prop
    extends Preserved initial s v where
  rip : s.RIP = v.pc 0x332
  digest : ∃ hash, HashStateAt s (stackPtr initial - 280) hash ∧
    v.serializeHash hash = v.hash message

variable {v : Variant}

theorem SavedStackAt.of_bytes {initial s t : RamState} (h : SavedStackAt initial s)
    (bytes : ∀ a, (Component.mem (stackPtr initial - 48) 56).Covers a →
      t.external[a]? = s.external[a]?) : SavedStackAt initial t := by
  have read (offset : Nat) (bound : offset ≤ 48) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    have addr : stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
        stackPtr initial - 48 + BitVec.ofNat 64 (48 - offset + i) := by
      have offsetEq : (48 : BitVec 64) = BitVec.ofNat 64 offset + BitVec.ofNat 64 (48 - offset) := by
        rw [← BitVec.ofNat_add, Nat.add_sub_cancel' bound]
        rfl
      rw [BitVec.ofNat_add, offsetEq]
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
      congr 2
      rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [bytes _ ⟨48 - offset + i, by omega, addr⟩]
  constructor
  · intro slot hs
    exact (read slot.2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (h.words slot hs)
  · have zero := read 0 (by decide)
    simp only [BitVec.sub_zero] at zero
    exact zero.trans h.returnAddress

theorem State.of_agrees [bindings : Bindings] {initial s t : RamState}
    {inputs : Array Input} {components : List Component} {fuel : Nat}
    (h : State initial s v) (ctx : Context initial inputs v)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (writes : WritesWithin components
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes])
    (saved : ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a)
    (hdf : .df ∉ components := by simp) :
    State initial t v := by
  have memory := frame.memoryWriteFrame writes
  obtain ⟨n, hn⟩ := h.execution
  refine ⟨⟨n + fuel, hn.trans run⟩,
    supportedMachine_of_ready_agrees h.machine ready frame, ?_,
    fun a ha => frame.grow a (h.allocated a ha),
    h.saved.of_bytes (fun a ha => frame.memory a (fun c hc => saved c hc a ha)),
    frame.directionFlagClear hdf h.directionFlag, memoryWriteFrame_trans h.frame memory⟩
  intro address byte fetch
  rw [memory address]
  · exact h.loaded address byte fetch
  · intro region hr ha
    exact (ctx.call.separation.2 region (by simpa using hr)).2 address ha (.inl ⟨byte, fetch⟩)

end Sha2.Proofs.Wrapper
