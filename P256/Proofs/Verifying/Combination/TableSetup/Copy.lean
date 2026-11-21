import P256.Proofs.Verifying.Combination.Copy
import P256.Proofs.Verifying.Combination.Preparation.Setup
import P256.Proofs.Verifying.Combination.Table.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.TableSetup

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Common.Field
open P256.Spec.Program.Routines

abbrev CopyKept (s t u : RamState) (destination n : Nat) : Prop :=
  ∀ off len : Nat, off ≤ 6552 → len ≤ off + 8 →
    (off + n ≤ destination ∨ destination + len ≤ off) →
    ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?

abbrev CopiesKept (s t u : RamState) (destinations : List Nat) (n : Nat := 768) : Prop :=
  ∀ off len : Nat, off ≤ 6552 → len ≤ off + 8 →
    (∀ destination ∈ destinations, off + n ≤ destination ∨ destination + len ≤ off) →
    ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?

structure CopyRegisters (s t : RamState) (temporary : Nat) : Prop where
  input : t.regValue .r15 = stackPtr s - 6520
  target : t.regValue .r14 = 0x11c930
  first : t.regValue .rbx = stackPtr s - 6240
  second : t.regValue .r12 = stackPtr s - 3888
  third : t.regValue .r13 = stackPtr s - 3120
  temporary : t.regValue .rbp = stackPtr s - BitVec.ofNat 64 temporary

structure CopyResult [Bindings] {n : Nat} (s t u : RamState) (site : CopyCallSite n)
    (effect : RamState → Effect) : Prop extends FrameState s u 96 8808 6552 where
  rip : u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + 3#64
  bytes : ∀ i < n,
    u.external[stackPtr s - BitVec.ofNat 64 site.layout.outputOffset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 site.layout.inputOffset + BitVec.ofNat 64 i]?
  registers : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], ∀ value : BitVec 64,
    (∀ a, (effect t).Holds t a → a.regValue r = value) → u.regValue r = value
  kept : CopyKept s t u site.layout.outputOffset n

theorem copy_after_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {n : Nat}
    (pre : Pre s boundary) (state : State s t)
    (site : CopyCallSite n) (offset : Nat) (bytes : List UInt8) (effect : RamState → Effect)
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (correct : AdvanceTriple boundary (fun a => a.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post effect))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (memory : ∀ c ∈ (effect t).components, ∀ a, ¬ c.Covers a)
    (rsp : .reg 4 ∉ (effect t).components)
    (next : (effect t).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (args : ∀ a, (effect t).Holds t a → a.regValue .r14 = 0x11c930 ∧
      a.regValue .rdx = BitVec.ofNat 64 n ∧
      a.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset ∧
      a.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hdf : Component.df ∉ (effect t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (effect t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (effect t).components := by component_not_mem) :
    ∃ fuel u, Advances boundary fuel t u ∧ CopyResult s t u site effect := by
  obtain ⟨n0, a, run0, ready, _, effectA⟩ := correct t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code) rip
  have stateA := state.after_registers ready effectA.agrees memory rsp
  have memoryA := effectA.agrees.external memory
  obtain ⟨target, count, input, output⟩ := args a effectA
  obtain ⟨n1, u, run1, stateU, ripU, bytesU, abiU, keptU⟩ := copy_call pre stateA site
    (effectA.rip.trans next) target count input output
  refine ⟨n0+n1, u, run0.trans run1, stateU, ripU, ?_, ?_, ?_⟩
  · intro i hi
    exact (bytesU i hi).trans (congrArg (fun m : Ram => m[_]?) memoryA)
  · intro r hr value valueA
    exact (abiU r hr).trans (valueA a effectA)
  · intro off len ho hl apart i hi
    exact (keptU off len ho hl apart i hi).trans
      (congrArg (fun m : Ram => m[_]?) memoryA)

end P256.Proofs.Verifying.Combination.TableSetup
