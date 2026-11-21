import X86Proofs.Program.ReadWrite.Bytes
import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Padding.Memory
import P256.Proofs.Program.Fill
import P256.Proofs.HMAC.Finalize.Branch

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

def fillCall (outer : Bool) : BitVec 64 := if outer then 0x101288 else 0x100fea

def fillReturn (outer : Bool) : BitVec 64 := if outer then 0x10128e else 0x100ff0

def remainingRegister (outer : Bool) : Syntax.Reg := if outer then .r15 else .r12

structure Marked [Bindings] (initial s : RamState) (message : ByteArray) (outer : Bool) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  position : s.regValue (positionRegister outer) = BitVec.ofNat 64 (message.size % 64)
  count : s.regValue (countRegister outer) = BitVec.ofNat 64 (message.size / 64)
  hashPointer : s.regValue (hashRegister outer) = stackPtr initial - 192#64
  remaining : s.regValue (remainingRegister outer) = BitVec.ofNat 64 (63 - message.size % 64)
  destination : s.regValue .rdi = stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64 + 1)
  zero : s.regValue .rsi = 0
  length : s.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64)
  tail : (MemoryRegion.mk (stackPtr initial - 256#64).toNat (message.size % 64)).HasBytes
    s.external (SHA256.remainderBytes message)
  marker : s.external[stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64)]? = some 128
  hash : SHA256.HashStateAt s (stackPtr initial - 192#64)
    (SHA256.compressBlocks P256.Proofs.SHA256.initialHash message)

theorem memset_pointer {t : RamState} (loaded : ProgramLoaded t) :
    MemReadable t 0x204550 8 ∧ (Operand.mem 0x204550 : Operand 64).read t = 0x11c810 := by
  have hbytes : ∀ i : Fin 8,
      Extracted.programSections.fetchByte (0x204550 + BitVec.ofNat 64 i.val) =
        some (storedByte (0x11c810 : BitVec 64) i.val) := by decide +kernel
  have hb : Bytes t.external 0x204550 8 (storedByte (0x11c810 : BitVec 64)) :=
    fun i hi => loaded _ _ (hbytes ⟨i, hi⟩)
  exact ⟨hb.readable (by decide), hb.memLoad (by decide) (by decide)⟩

theorem fill_call [Bindings] (outer : Bool) {initial s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328) (rip : s.RIP = fillCall outer) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      (callEffect (fun _ => 0x11c810) (fillReturn outer) s).Holds s t ∧
      ScalarFrame.FrameState initial t 0 672 336 := by
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [call_address state]
    exact Program.writable_of_grow
      (Program.stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (offset := 336) (by decide) (by decide)) state.allocated
  have apart : RangeApart (pushAddr s) 8 (fillCall outer) 6 := by
    rw [call_address state]
    cases outer
    · exact P256.Proofs.HMAC.Key.stack_code_apart (pre.toCalleePre)
        (offset := 336) (codeOffset := 0xfea) (by decide) (by decide) (by decide)
    · exact P256.Proofs.HMAC.Key.stack_code_apart (pre.toCalleePre)
        (offset := 336) (codeOffset := 0x1288) (by decide) (by decide) (by decide)
  let disp : BitVec 32 := if outer then 0x1032c2 else 0x103560
  have pointer := memset_pointer state.loaded
  have target : callMemPtr (fillCall outer) (.rip disp) s = 0x11c810 := by
    cases outer <;> exact pointer.2
  have code : CodeIn (codeRange (fillCall outer) (encodeCallM64 (.rip disp))) s := by
    cases outer
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xfea _ (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn state.loaded) 0x1288 _ (by decide) (by decide +kernel)
  obtain ⟨t, step, ready, effect⟩ := call_m64_effect_step (fillCall outer) (.rip disp)
    trivial rfl rfl s (readyToStep state.machine state.bindingsSupported) code
    ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide +kernel⟩, by cases outer <;> exact pointer.1⟩
  have atTarget : t.RIP = 0x11c810 := effect.rip.trans target
  have ret : fillCall outer + 6#64 = fillReturn outer := by cases outer <;> rfl
  have converted : (callEffect (fun _ => 0x11c810) (fillReturn outer) s).Holds s t := by
    have h : (callEffect (fun _ => 0x11c810) (fillCall outer + 6#64) s).Holds s t :=
      ⟨atTarget, effect.writes, effect.flags, effect.agrees⟩
    simpa only [ret] using h
  refine ⟨t, Advances.of_step step (.inl ?_), ready, converted, after_call pre state ready converted⟩
  rw [atTarget]
  exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c810 (by decide))

theorem fill_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 336) (rip : s.RIP = 0x11c810)
    (destination : s.regValue .rdi = stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64 + 1))
    (zero : s.regValue .rsi = 0) (ret : InProgram (returnBoundary s).rip) :
    CalleePre s boundary 0x11c810 0 (63 - message.size % 64) 0 := by
  have bounds := stack_bounds pre.stack
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 256 + (message.size % 64 + 1) := by
    rw [destination, toNat_add_ofNat _ _ (by rw [stack_sub_toNat pre.stack (by decide : 256 ≤ 672)]; omega),
      stack_sub_toNat pre.stack (by decide : 256 ≤ 672)]
  have sub (region : MemoryRegion)
      (lo : (stackPtr initial).toNat - 672 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial 672).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr initial).toNat - 672 ≤ a ∧
      a < (Stack.region initial 672).start + (Stack.region initial 672).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub := sub (Stack.region s 0)
    (by change _ ≤ (stackPtr s).toNat - 0; rw [sp]; omega)
    (by rw [stack_region_end, sp]; omega)
  have outputSub := sub (registerRegion s .rdi (63 - message.size % 64))
    (by change _ ≤ (s.regValue .rdi).toNat; rw [dst]; omega)
    (by change (s.regValue .rdi).toNat + (63 - message.size % 64) ≤ _; rw [dst]; omega)
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, s.external[a]? = some b :=
    Option.isSome_iff_exists.mp (state.allocated a (Option.isSome_iff_exists.mpr ha))
  refine {
    bindingsSupported := state.bindingsSupported
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := by change (s.regValue .rsi).toNat + 0 < 2^32; rw [zero]; decide
    inputAllocated := ?_
    outputBounded := by change (s.regValue .rdi).toNat + (63 - message.size % 64) < 2^32; rw [dst]; omega
    outputAllocated := fun a ha => grow a (pre.stack.2.1 a (outputSub a.toNat ha))
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret
  }
  · intro a ha
    change (s.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rsi).toNat + 0 at ha
    omega
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), Nat.zero_le _, ?_⟩
    · change (Stack.region s 0).start + (Stack.region s 0).size < 2^32
      rw [stack_region_end, sp]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [sp]
      have align := pre.stack.2.2.2
      change (stackPtr initial).toNat % 16 = 8 at align
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha _
      change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha _
      change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha hb
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + (63 - message.size % 64) at ha
      change (stackPtr s).toNat - 0 ≤ a ∧ a < (Stack.region s 0).start + (Stack.region s 0).size at hb
      rw [dst] at ha
      rw [stack_region_end, sp] at hb
      omega
  · intro region member a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)

theorem fill_result_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (rsp : stackPtr s = stackPtr initial - 336#64)
    (destination : s.regValue .rdi = stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64 + 1))
    (result : CalleeResult s t boundary (63 - message.size % 64) 0) :
    MemoryWriteFrame s t #v[scratchRegion initial] := by
  have bounds := stack_bounds pre.stack
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 256 + (message.size % 64 + 1) := by
    rw [destination, toNat_add_ofNat _ _ (by rw [stack_sub_toNat pre.stack (by decide : 256 ≤ 672)]; omega),
      stack_sub_toNat pre.stack (by decide : 256 ≤ 672)]
  intro a ha
  apply result.frame a
  intro region member hin
  have cases : region = registerRegion s .rdi (63 - message.size % 64) ∨ region = Stack.region s 0 := by
    simpa using member
  apply ha (scratchRegion initial) (by simp)
  change (stackPtr initial).toNat - 672 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 672 + 520
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat + (63 - message.size % 64) at hin
    rw [dst] at hin
    constructor <;> omega
  · change (stackPtr s).toNat - 0 ≤ a.toNat ∧
      a.toNat < (Stack.region s 0).start + (Stack.region s 0).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

theorem fill_result_byte [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (rsp : stackPtr s = stackPtr initial - 336#64)
    (destination : s.regValue .rdi = stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64 + 1))
    (result : CalleeResult s t boundary (63 - message.size % 64) 0)
    {i : Nat} (bound : i < 104) (outside : i ≤ message.size % 64 ∨ 64 ≤ i) :
    t.external[stackPtr initial - 256#64 + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - 256#64 + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have address (j : Nat) (hj : j ≤ 104) :
      (stackPtr initial - 256#64 + BitVec.ofNat 64 j).toNat = (stackPtr initial).toNat - 256 + j := by
    rw [toNat_add_ofNat _ _ (by rw [stack_sub_toNat pre.stack (by decide : 256 ≤ 672)]; omega),
      stack_sub_toNat pre.stack (by decide : 256 ≤ 672)]
  apply result.frame
  intro region member hin
  have cases : region = registerRegion s .rdi (63 - message.size % 64) ∨ region = Stack.region s 0 := by
    simpa using member
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ _ ∧
      (stackPtr initial - 256#64 + BitVec.ofNat 64 i).toNat <
        (s.regValue .rdi).toNat + (63 - message.size % 64) at hin
    rw [destination, address _ (by omega), address _ (by omega)] at hin
    omega
  · change (stackPtr s).toNat - 0 ≤ _ ∧
      (stackPtr initial - 256#64 + BitVec.ofNat 64 i).toNat <
        (Stack.region s 0).start + (Stack.region s 0).size at hin
    have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
      rw [rsp]
      exact stack_sub_toNat pre.stack (by decide)
    rw [stack_region_end, sp, address _ (by omega)] at hin
    omega

end P256.Proofs.HMAC.Finalize.Padding
