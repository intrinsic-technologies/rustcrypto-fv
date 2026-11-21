import P256.Spec
import P256.Proofs.Sec1.Wrapper.ReturnState
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStackRegion
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CallSite (inputBytes outputBytes reserve : Nat) where
  codeOffset : Nat
  disp : BitVec 32
  entry : BitVec 64
  codeBound : codeOffset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5
    (disp.signExtend 64) = entry
  entryProgram : InProgram entry
  layout : StackCallLayout 4048 inputBytes outputBytes reserve
  stack : layout.stackOffset = 240

structure Called [bindings : Bindings] (initial s t : RamState)
    {inputBytes outputBytes reserve : Nat} (site : CallSite inputBytes outputBytes reserve) : Prop where
  execution : Advances (returnBoundary initial) 1 s t
  pre : CalleePre t (returnBoundary initial) site.entry inputBytes outputBytes reserve
  rsp : stackPtr t = stackPtr initial - 240
  input : t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 site.layout.inputOffset
  output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 site.layout.outputOffset
  ret : (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64)
  registers : ∀ r : Syntax.Reg, r ≠ .rsp → t.regValue r = s.regValue r
  bytes : ∀ offset len : Nat, offset ≤ 232 → len ≤ offset + 8 →
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[Stack.region initial 4048]

 theorem call [bindings : Bindings] {initial s : RamState}
    {inputs : List ByteArray} {slices : Array Input} {inputBytes outputBytes reserve : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial inputs slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (state : ReturnState initial s) (site : CallSite inputBytes outputBytes reserve)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 site.layout.inputOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 site.layout.outputOffset) :
    ∃ t, Called initial s t site := by
  obtain ⟨t,run,ready,loaded,effect,memory⟩ := call_rel32_exists valid.stackAvailable.1
    (call_stack_avoids valid) outside (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    232 site.codeOffset site.disp state.rsp rip (by decide) (by decide)
    (Nat.le_of_lt site.codeBound) site.bytes (by rw [site.target]; exact site.entryProgram)
  have sp : stackPtr t = stackPtr initial - 240 := by
    have h := (callEffect_stack effect).2
    have hsub := congrArg (fun x : BitVec 64 => x - 8) h
    simp only [BitVec.add_sub_cancel] at hsub
    rw [hsub, state.rsp, BitVec.sub_sub]
    rfl
  have regs : ∀ r : Syntax.Reg, r ≠ .rsp → t.regValue r = s.regValue r := by
    intro r hr
    cases r <;> try contradiction
    all_goals first
    | exact effect.agrees.read (n := 64) (r := 0) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 3) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 5) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 8) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 9) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 10) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 11) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 12) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 13) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 14) (by simp [pushEffect_components])
    | exact effect.agrees.read (n := 64) (r := 15) (by simp [pushEffect_components])
  have src := (regs .rsi (by decide)).trans input
  have dst := (regs .rdi (by decide)).trans output
  have ret : (returnBoundary t).rip =
      Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) :=
    (callEffect_stack effect).1
  have pre : CalleePre t (returnBoundary initial) site.entry inputBytes outputBytes reserve :=
    CalleePre.of_stack_region valid.stackAvailable.1 (call_stack_avoids valid) outside
      site.layout (bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees)
      (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
      (effect.agrees.directionFlagClear (by simp [pushEffect_components]) state.directionFlag)
      loaded (fun a ha => effect.agrees.grow a (state.allocated a ha))
      (effect.rip.trans site.target) (by rw [site.stack]; exact sp) src dst (by
        rw [ret]
        rw [show Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) =
          Extracted.textAddress + BitVec.ofNat 64 (site.codeOffset + 5) by
            rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
        exact inProgram_of_textOffset _ site.codeBound)
  refine ⟨t,run,pre,sp,src,dst,ret,regs,?_,(fun a ha => effect.agrees.grow a (state.allocated a ha)),?_⟩
  · intro offset len ho hl i hi
    exact ScalarFrame.call_byte (by decide) state.rsp effect ho hl hi
  · apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨Stack.region initial 4048, by simp, ?_⟩
      obtain ⟨i,hi,rfl⟩ := ha
      have address : pushAddr s = stackPtr initial - 240 := by
        rw [pushAddr, state.rsp, BitVec.sub_sub]
        rfl
      rw [address]
      apply memoryRegion_contains_add valid.stackAvailable.1.1 (len := 8) _ _ hi
      · change (stackPtr initial).toNat - 4048 ≤
          (stackPtr initial - BitVec.ofNat 64 240).toNat
        rw [stack_sub_toNat valid.stackAvailable.1 (offset := 240) (by decide)]
        change (stackPtr initial).toNat - 4048 ≤ (stackPtr initial).toNat - 240
        omega
      · change (stackPtr initial - BitVec.ofNat 64 240).toNat + 8 ≤
          (Stack.region initial 4048).start + (Stack.region initial 4048).size
        rw [stack_region_end, stack_sub_toNat valid.stackAvailable.1 (offset := 240) (by decide)]
        omega
    · exact ha.elim

end P256.Proofs.Sec1.Wrapper.Success
