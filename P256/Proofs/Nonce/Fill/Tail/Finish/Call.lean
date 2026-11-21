import P256.Proofs.Nonce.Fill.Tail.Finish.Setup
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar


theorem call_address [Bindings] {initial s : RamState} (input : Frame initial s) :
    pushAddr s = stackPtr initial - 240 := by
  simp only [pushAddr, input.rsp, frameBase, BitVec.sub_sub]
  rfl

theorem call_writes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {state : Nonce.State} {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : Pre initial boundary orderAddress state) (input : Frame initial s) :
    WritesWithin (callEffect target ret s).components #v[Stack.region initial 2096] := by
  intro c hc a hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · refine ⟨Stack.region initial 2096, by simp, ?_⟩
    rw [call_address input] at hv
    exact ScalarFrame.stack_contains pre.toCalleePre (offset := 240)
      (by decide) (by decide) hv
  · exact hv.elim

theorem call_loaded [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {state : Nonce.State} {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : Pre initial boundary orderAddress state) (input : Frame initial s)
    (effect : (callEffect target ret s).Holds s t) : ProgramLoaded t := by
  intro a b hb
  rw [effect.agrees.memoryWriteFrame (call_writes pre input) a]
  · exact input.loaded a b hb
  · intro region hr hin
    have he : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)

theorem call_pre [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => 0x106f40) 0x1076fa s).Holds s t) :
    Initialize.Conversions.Int2Octets.Pre t boundary := by
  have agrees := effect.agrees
  have sp : stackPtr t = stackPtr initial - 240 := effect.writes.1.trans (call_address input.toFrame)
  have di : t.regValue .rdi = frameBase initial + 72 :=
    (agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans input.rdi
  have dx : t.regValue .rdx = initial.regValue .rsi :=
    (agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans input.rdx
  have si : t.regValue .rsi = orderAddress :=
    (agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans input.rsi
  have bounds := stack_bounds pre.stack
  have spn : (stackPtr t).toNat = (stackPtr initial).toNat - 240 := by
    rw [sp]
    exact stack_sub_toNat pre.stack (by decide)
  have din : (t.regValue .rdi).toNat = (stackPtr initial).toNat - 160 := by
    rw [di]
    change (frameBase initial + 72#64).toNat = _
    rw [frameBase_add initial (offset := 72) (by decide)]
    exact stack_sub_toNat pre.stack (by decide)
  have stackSub (a : Nat) (ha : (Stack.region t 128).Contains a) :
      (Stack.region initial 2096).Contains a := by
    change (stackPtr t).toNat - 128 ≤ a ∧ a < (Stack.region t 128).start + (Stack.region t 128).size at ha
    rw [stack_region_end, spn] at ha
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
    rw [stack_region_end]
    constructor <;> omega
  have inputSub (a : Nat) (ha : (registerRegion t .rdi 32).Contains a) :
      (Stack.region initial 2096).Contains a := by
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
    rw [din] at ha
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
    rw [stack_region_end]
    constructor <;> omega
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, t.external[a]? = some b :=
    Option.isSome_iff_exists.mp (agrees.grow a (input.allocated a (Option.isSome_iff_exists.mpr ha)))
  have sameOutput : registerRegion t .rdx 32 = registerRegion initial .rsi 32 := by
    simp only [registerRegion, dx]
  have sameOrder : registerRegion t .rsi 32 = MemoryRegion.mk orderAddress.toNat 32 := by
    simp only [registerRegion, si]
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees input.bindingsSupported ready agrees
    machine := supportedMachine_of_ready_agrees input.machine ready agrees
    directionFlag := agrees.directionFlagClear (by simp) input.directionFlag
    loaded := call_loaded pre input.toFrame effect
    rip := effect.rip
    outputBounded := sameOutput ▸ pre.inputBounded
    outputAllocated := ?_
    inputBounded := ?_
    inputAllocated := fun a ha => grow a (pre.stack.2.1 a (inputSub a.toNat ha))
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ?_
    length := (agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])).trans input.rcx
    orderBounded := sameOrder ▸ pre.orderBounded
    orderAllocated := ?_
    orderOutput := ?_
    orderStack := ?_
    order := ?_
  }
  · change (t.regValue .rdi).toNat + 32 < 2^32
    rw [din]
    omega
  · rw [sameOrder]
    exact fun a ha => grow a (pre.orderAllocated a ha)
  · rw [sameOutput]
    exact fun a ha => grow a (pre.inputAllocated a ha)
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), ?_, ?_⟩
    · change (Stack.region t 128).start + (Stack.region t 128).size < 2^32
      rw [stack_region_end, spn]
      omega
    · change 128 ≤ (stackPtr t).toNat
      rw [spn]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [spn]
      have align := pre.stack.2.2.2
      change (stackPtr initial).toNat % 16 = 8 at align
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha hb
      change (registerRegion t .rdx 32).Contains a at hb
      rw [sameOutput] at hb
      exact pre.separation 0 2 (by decide) a hb (inputSub a ha)
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
      change (Stack.region t 128).start ≤ a ∧ a < (Stack.region t 128).start + (Stack.region t 128).size at hb
      rw [din] at ha
      rw [stack_region_end] at hb
      change (stackPtr t).toNat - 128 ≤ a ∧ a < (stackPtr t).toNat + 8 at hb
      rw [spn] at hb
      omega
    · intro a ha hb
      change (registerRegion t .rdx 32).Contains a at ha
      rw [sameOutput] at ha
      exact pre.separation 0 2 (by decide) a ha (stackSub a hb)
  · rw [sameOrder]
    intro a ha hb
    rw [sameOutput] at hb
    exact pre.orderDisjoint _ (by simp) a ha hb
  · rw [sameOrder]
    intro a ha hb
    exact pre.orderDisjoint _ (by simp) a ha (stackSub a hb)
  · intro region member a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [sameOutput] at ha
      exact pre.outputAvoids a ha
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)
  · change InProgram (stackTop t)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0x76fa (by decide)
  · rw [si]
    refine ⟨input.generator.2.1.1, ?_⟩
    intro i hi
    rw [agrees.memoryWriteFrame (call_writes pre input.toFrame) _]
    · exact input.generator.2.1.2 i hi
    · intro region member inside
      have eq : region = Stack.region initial 2096 := by simpa using member
      subst region
      exact pre.orderDisjoint _ (by simp) _
        (memoryRegion_contains_add (len := 32) pre.orderBounded (Nat.le_refl _) (Nat.le_refl _) hi) inside

end P256.Proofs.Nonce.Fill.Tail.Finish
