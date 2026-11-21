import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Interface
import P256.Proofs.SHA256

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

structure OuterPadCall [Bindings] (initial s : RamState) (key : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 336 where
  rip : s.RIP = 0x115990
  inputPointer : s.regValue .rsi = initial.regValue .rdi
  hashPointer : s.regValue .rdi = stackPtr initial - 88#64
  countRegister : s.regValue .rdx = 1
  inputBytes : (registerRegion s .rsi 64).HasBytes s.external (keyPad key 0x5c)
  hashWords : SHA256.HashStateAt s (s.regValue .rdi) P256.Proofs.SHA256.initialHash
  returnInProgram : InProgram (returnBoundary s).rip

theorem outer_pad_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : OuterPadCall initial s key) :
    SHA256.CompressionPre s boundary P256.Proofs.SHA256.initialHash (keyPad key 0x5c) 1 := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hp : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 88 := by
    rw [state.hashPointer]
    exact stack_sub_toNat pre.stack (by decide)
  have stackSub (a : Nat) (ha : (Stack.region s 336).Contains a) :
      (Stack.region initial 672).Contains a := by
    change (stackPtr s).toNat - 336 ≤ a ∧
      a < (Stack.region s 336).start + (Stack.region s 336).size at ha
    rw [stack_region_end, sp] at ha
    change (stackPtr initial).toNat - 672 ≤ a ∧
      a < (Stack.region initial 672).start + (Stack.region initial 672).size
    rw [stack_region_end]
    constructor <;> omega
  have inputSub (a : Nat) (ha : (registerRegion s .rsi 64).Contains a) :
      (registerRegion initial .rdi 168).Contains a := by
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 64 at ha
    rw [state.inputPointer] at ha
    change (initial.regValue .rdi).toNat ≤ a ∧ a < (initial.regValue .rdi).toNat + 168
    constructor <;> omega
  have hashSub (a : Nat) (ha : (registerRegion s .rdi 32).Contains a) :
      (Stack.region initial 672).Contains a := by
    change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 32 at ha
    rw [hp] at ha
    change (stackPtr initial).toNat - 672 ≤ a ∧
      a < (Stack.region initial 672).start + (Stack.region initial 672).size
    rw [stack_region_end]
    constructor <;> omega
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, s.external[a]? = some b :=
    Option.isSome_iff_exists.mp (state.allocated a (Option.isSome_iff_exists.mpr ha))
  refine {
    bindingsSupported := state.bindingsSupported
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := state.rip
    inputBounded := ?_
    inputAllocated := fun a ha => grow a (pre.outputAllocated a (inputSub a.toNat ha))
    outputBounded := ?_
    outputAllocated := fun a ha => grow a (pre.stack.2.1 a (hashSub a.toNat ha))
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := state.returnInProgram
    countRegister := state.countRegister
    inputBytes := state.inputBytes
    hashWords := state.hashWords
  }
  · change (s.regValue .rsi).toNat + 64 < 2^32
    rw [state.inputPointer]
    have h := pre.outputBounded
    change (initial.regValue .rdi).toNat + 168 < 2^32 at h
    omega
  · change (s.regValue .rdi).toNat + 32 < 2^32
    rw [hp]
    omega
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), ?_, ?_⟩
    · change (Stack.region s 336).start + (Stack.region s 336).size < 2^32
      rw [stack_region_end, sp]
      omega
    · change 336 ≤ (stackPtr s).toNat
      rw [sp]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [sp]
      have align := pre.stack.2.2.2
      change (stackPtr initial).toNat % 16 = 8 at align
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha hb
      exact pre.separation 1 2 (by decide) a (inputSub a ha) (hashSub a hb)
    · intro a ha hb
      exact pre.separation 1 2 (by decide) a (inputSub a ha) (stackSub a hb)
    · intro a ha hb
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 32 at ha
      change (Stack.region s 336).start ≤ a ∧
        a < (Stack.region s 336).start + (Stack.region s 336).size at hb
      rw [hp] at ha
      rw [stack_region_end, sp] at hb
      omega
  · intro region member a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pre.avoids _ (by simp) a (hashSub a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)

theorem outer_pad_result_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : OuterPadCall initial s key)
    (result : SHA256.CompressionResult s t boundary P256.Proofs.SHA256.initialHash (keyPad key 0x5c)) :
    MemoryWriteFrame s t #v[workRegion initial 672] := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hp : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 88 := by
    rw [state.hashPointer]
    exact stack_sub_toNat pre.stack (by decide)
  intro a ha
  apply result.frame a
  intro region member hin
  have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 336 := by simpa using member
  apply ha (workRegion initial 672) (by simp)
  change (stackPtr initial).toNat - 672 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 672 + (672 - 48)
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat + 32 at hin
    rw [hp] at hin
    constructor <;> omega
  · change (stackPtr s).toNat - 336 ≤ a.toNat ∧
      a.toNat < (Stack.region s 336).start + (Stack.region s 336).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

end P256.Proofs.HMAC.Finalize.Prepare
