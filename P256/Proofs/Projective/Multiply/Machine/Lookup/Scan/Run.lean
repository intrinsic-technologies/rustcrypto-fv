import P256.Proofs.Projective.Multiply.Machine.Lookup.Call.Choice
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Choice
import P256.Proofs.Projective.Multiply.Machine.Lookup.Copy
import P256.Proofs.Projective.Multiply.Machine.Lookup.Call.External
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (state : FrameState s t) (offset : Nat) (bytes : List UInt8) (E : RamState → Effect)
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (block : AdvanceTriple boundary (fun t => t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (noMem : ∀ t, ∀ c ∈ (E t).components, ∀ a, ¬ c.Covers a)
    (noSp : ∀ t, .reg 4 ∉ (E t).components)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (hdf : Component.df ∉ (E t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (E t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (E t).components := by component_not_mem) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ (E t).Holds t u ∧
      u.external = t.external := by
  obtain ⟨n,u,run,ready,_,effect⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code) rip
  exact ⟨n,u,run,state.after_registers ready effect.agrees (noMem t) (noSp t),
    effect,effect.agrees.external (noMem t)⟩

theorem montgomery_mem {t u : RamState} {address : BitVec 64} {value : Nat}
    (h : MontgomeryAt t address value) (memory : u.external = t.external) :
    MontgomeryAt u address value := by
  exact Field.MontgomeryAt.of_bytes_eq h (by intro i hi; rw [memory])

theorem projective_mem {t u : RamState} {address : BitVec 64} {value : Projective}
    (h : ProjectiveAt t address value) (memory : u.external = t.external) :
    ProjectiveAt u address value := by
  exact h.of_bytes_eq (by intro i hi; rw [memory])

theorem read_bytes {t u : RamState} {address : BitVec 64} {n : Nat}
    (memory : ∀ i < n/8, u.external[address + BitVec.ofNat 64 i]? =
      t.external[address + BitVec.ofNat 64 i]?) :
    (Operand.mem address : Operand n).read u = (Operand.mem address : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  exact congrArg (Option.getD · 0) (memory i hi)

theorem select_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {select : Bool}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (site : StackCallSite 0x114380 32 128)
    (rightOffset : Nat) (rightBound : rightOffset + 32 ≤ 768)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = s.regValue .rsi + BitVec.ofNat 64 rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) x)
    (hy : MontgomeryAt s (s.regValue .rsi + BitVec.ofNat 64 rightOffset) y)
    (choice : t.regValue .rcx = if select then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 site.layout.outputOffset) (if select then y else x) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 360 → len ≤ offset + 8 →
        (offset + 32 ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  exact external_binary_call (op := fun x y => if select then y else x) pre state site
    rightOffset rightBound
    (fun v hp hc hx hy => Select.field_select_correct hp hx hy (hc.trans choice))
    rip input right output hx hy

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
