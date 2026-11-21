import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Inputs
import Hkdf.Proofs.Common.CallFrame
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace Hkdf.Proofs.Standard

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Program
open Hkdf.Proofs.Common

def saltKey (salt : Option ByteArray) : ByteArray :=
  salt.getD ⟨Array.replicate 32 0⟩

def frameBase (initial : RamState) : BitVec 64 := initial.regValue .rsp - 520

def hmacBase (initial : RamState) : BitVec 64 := frameBase initial + 120

structure Context [bindings : Bindings] (initial : RamState)
    (salt : Option ByteArray) (inputs : Array Input) : Prop where
  environment : MachineRamUnitStrideDecodable bindings initial
  machine : SupportedIntegerMachineState bindings.processor initial
  call : ValidExtractCall hkdfSha256Extract initial salt inputs

structure SavedStackAt (initial s : RamState) : Prop where
  words : ∀ slot ∈ ([(Syntax.Reg.rbp, 8), (.r15, 16), (.r14, 24),
      (.r13, 32), (.r12, 40), (.rbx, 48)] : List (Syntax.Reg × Nat)),
    memLoad s.external (initial.regValue .rsp - BitVec.ofNat 64 slot.2) 64 =
      initial.regValue slot.1
  returnAddress : memLoad s.external (initial.regValue .rsp) 64 =
    memLoad initial.external (initial.regValue .rsp) 64

theorem SavedStackAt.of_agrees {initial s t : RamState} (saved : SavedStackAt initial s)
    (same : (Component.mem (stackPtr initial - 48) 56).Agrees s t) :
    SavedStackAt initial t := by
  constructor
  · intro slot member
    have within : slot.2 ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have address : stackPtr initial - 48 + BitVec.ofNat 64 (48 - slot.2) =
        initial.regValue .rsp - BitVec.ofNat 64 slot.2 := by
      apply BitVec.eq_sub_iff_add_eq.mpr
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        show 48 - slot.2 + slot.2 = 48 by omega]
      exact BitVec.sub_add_cancel _ _
    have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
      (width := 64) (offset := 48 - slot.2) same (by omega)
    rw [address] at word
    exact word.trans (saved.words slot member)
  · have word := Hkdf.Proofs.Common.CallFrame.agrees_memLoad_offset
      (width := 64) (offset := 48) same (by decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel] at word
    exact word.trans saved.returnAddress

structure State [bindings : Bindings] (initial s : RamState) : Prop extends
    Hkdf.Proofs.Common.CallFrame.Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] s where
  saved : SavedStackAt initial s

structure Preserved [Bindings] (initial s : RamState) : Prop extends State initial s where
  rsp : s.regValue .rsp = frameBase initial
  inputCount : memLoad s.external (frameBase initial + 8) 64 = initial.regValue .rsi
  outputPointer : memLoad s.external (frameBase initial + 96) 64 = initial.regValue .r9
  pointerTable : memLoad s.external (frameBase initial + 104) 64 = initial.regValue .rdi
  lengthTable : memLoad s.external (frameBase initial + 112) 64 = initial.regValue .rdx

theorem Preserved.of_observations [Bindings] {initial s t : RamState}
    (h : Preserved initial s)
    (running : Hkdf.Proofs.Common.CallFrame.Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] t)
    (saved : (Component.mem (stackPtr initial - 48) 56).Agrees s t)
    (persistent : ∀ offset ∈ ([8, 96, 104, 112] : List Nat),
      (Component.mem (frameBase initial + BitVec.ofNat 64 offset) 8).Agrees s t)
    (rsp : t.regValue .rsp = frameBase initial) : Preserved initial t := by
  refine ⟨⟨running, h.saved.of_agrees saved⟩, rsp, ?_, ?_, ?_, ?_⟩
  · exact (Hkdf.Proofs.Common.CallFrame.agrees_memLoad (persistent 8 (by simp))).trans h.inputCount
  · exact (Hkdf.Proofs.Common.CallFrame.agrees_memLoad (persistent 96 (by simp))).trans h.outputPointer
  · exact (Hkdf.Proofs.Common.CallFrame.agrees_memLoad (persistent 104 (by simp))).trans h.pointerTable
  · exact (Hkdf.Proofs.Common.CallFrame.agrees_memLoad (persistent 112 (by simp))).trans h.lengthTable

theorem Preserved.of_noMem [Bindings] {initial s t : RamState}
    {salt : Option ByteArray} {inputs : Array Input} {fuel : Nat}
    {components : List Component} (ctx : Context initial salt inputs)
    (state : Preserved initial s) (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (rsp : Component.reg 4 ∉ components) (df : Component.df ∉ components) :
    Preserved initial t := by
  have memory := frame.external noMem
  apply state.of_observations
    (state.toRunning.of_agrees run ready frame
      (fun c hc a ha ↦ (noMem c hc a ha).elim) (by
        intro region member a contains inside
        have equal : region = Stack.region initial hkdfSha256Extract.minStackBytes := by
          simpa using member
        subst region
        exact (ctx.call.stackSeparation.2 _ (by simp)).2 a contains (.inl inside)) df)
    (by intro i hi; rw [memory])
    (by intro offset member i hi; rw [memory])
    ((frame.read (n := 64) (r := 4) rsp).trans state.rsp)

structure Buffered [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (message : ByteArray) : Prop extends Preserved initial s where
  hmac : HmacAt s (hmacBase initial) (saltKey salt) message

structure Initialized [Bindings] (initial s : RamState) (salt : Option ByteArray) : Prop
    extends Buffered initial s salt ByteArray.empty where
  rip : s.RIP = 0x101601

structure LoopState [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (inputs : Array Input) (index : Nat) : Prop
    extends Buffered initial s salt (prefixConcatenation inputs index) where
  rip : s.RIP = 0x101649
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  copyRegister : s.regValue .r12 = 0x10dd60
  remaining : index < inputs.size

structure Completed [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (inputs : Array Input) : Prop
    extends Buffered initial s salt (concatenation inputs) where
  rip : s.RIP = 0x101724

end Hkdf.Proofs.Standard
