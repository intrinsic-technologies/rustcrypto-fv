import P256.Proofs.ReadBe.Frame
import P256.Proofs.Program.Interface
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem Frame.push_address (frame : Frame s t) : pushAddr t = stackPtr s - 80 := by
  change stackPtr t - 8 = _
  rw [frame.rsp]
  simp only [frameBase, BitVec.sub_sub, BitVec.reduceAdd]
  rfl

theorem Pre.call_writes (pre : Pre s boundary) (frame : Frame s t)
    {target ret : BitVec 64} :
    WritesWithin (callEffect (fun _ => target) ret t).components
      #v[registerRegion s .rdx 32, scratchRegion s] := by
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨scratchRegion s, by simp, ?_⟩
  rw [frame.push_address]
  exact pre.scratch_contains (offset := 80) (by decide) (by decide) (len := 8) (by decide) hi

theorem Pre.memcpy_pre (pre : Pre s boundary) (frame : Frame s t) {k : Nat}
    (hk : k < 4) (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x11c930) 0x119131 t).Holds t u)
    (source : t.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 (24-8*k))
    (destination : t.regValue .rdi = frameBase s + 16) :
    CalleePre u boundary 0x11c930 8 8 0 := by
  have grow (a : BitVec 64) (ha : (s.external[a]?).isSome) : (u.external[a]?).isSome :=
    effect.agrees.grow a (frame.allocated a ha)
  have bounds := (stack_bounds pre.stack)
  have inputBound : (s.regValue .rdi).toNat + 32 < 2^32 := pre.inputBounded
  have hsp : stackPtr u = stackPtr s - 80 := effect.writes.1.trans frame.push_address
  have hspn : (stackPtr u).toNat = (stackPtr s).toNat - 80 := by
    rw [hsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hsource : u.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 (24-8*k) :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have hdest : u.regValue .rdi = stackPtr s - 56 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
    change u.regValue .rdi = (stackPtr s - 72) + 16 at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have hin : (registerRegion u .rsi 8).start = (s.regValue .rdi).toNat + (24-8*k) := by
    change (u.regValue .rsi).toNat = _
    rw [hsource, toNat_add_ofNat _ _ (by omega)]
  have hout : (registerRegion u .rdi 8).start = (stackPtr s).toNat - 56 := by
    change (u.regValue .rdi).toNat = _
    rw [hdest]
    exact stack_sub_toNat pre.stack (by decide)
  have hs : (Stack.region u 0).start = (stackPtr s).toNat - 80 := by
    change (stackPtr u).toNat - 0 = _
    rw [Nat.sub_zero, hspn]
  have he : (Stack.region u 0).start + (Stack.region u 0).size = (stackPtr s).toNat - 80 + 8 := by
    rw [stack_region_end, hspn]
  have inputSub (a : Nat) (ha : (registerRegion u .rsi 8).Contains a) :
      (registerRegion s .rdi 32).Contains a := by
    change (registerRegion u .rsi 8).start ≤ a ∧ a < (registerRegion u .rsi 8).start + 8 at ha
    rw [hin] at ha
    change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 32
    omega
  have outputSub (a : Nat) (ha : (registerRegion u .rdi 8).Contains a) :
      (Stack.region s 128).Contains a := by
    change (registerRegion u .rdi 8).start ≤ a ∧ a < (registerRegion u .rdi 8).start + 8 at ha
    rw [hout] at ha
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (Stack.region s 128).start + (Stack.region s 128).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub (a : Nat) (ha : (Stack.region u 0).Contains a) :
      (Stack.region s 128).Contains a := by
    change (Stack.region u 0).start ≤ a ∧ a < (Stack.region u 0).start + (Stack.region u 0).size at ha
    rw [he, hs] at ha
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (Stack.region s 128).start + (Stack.region s 128).size
    rw [stack_region_end]
    constructor <;> omega
  have alloc (r : MemoryRegion) (sub : ∀ a, r.Contains a → (Stack.region s 128).Contains a) :
      r.Allocated u.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (sub a.toNat ha))))
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees frame.bindingsSupported ready effect.agrees
    machine := supportedMachine_of_ready_agrees frame.machine ready effect.agrees
    directionFlag := effect.agrees.directionFlagClear (by simp) frame.directionFlag
    loaded := pre.loaded_of_frame (memoryWriteFrame_trans frame.frame
      (pre.local_frame (effect.agrees.memoryWriteFrame (pre.call_writes frame))))
    rip := effect.rip
    inputBounded := ?_
    inputAllocated := ?_
    outputBounded := ?_
    outputAllocated := alloc _ outputSub
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ?_ }
  · change (registerRegion u .rsi 8).start + 8 < 2^32
    rw [hin]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (pre.inputAllocated a (inputSub a.toNat ha))))
  · change (registerRegion u .rdi 8).start + 8 < 2^32
    rw [hout]
    omega
  · refine ⟨?_, alloc _ stackSub, Nat.zero_le _, ?_⟩
    · change (Stack.region u 0).start + (Stack.region u 0).size < 2^32
      rw [he]
      omega
    · change (stackPtr u).toNat % 16 = 8
      rw [hspn]
      have hm : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro a ha hb
      exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (inputSub a ha) (outputSub a hb)
    · intro a ha hb
      exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (inputSub a ha) (stackSub a hb)
    · intro a ha hb
      change (registerRegion u .rdi 8).start ≤ a ∧ a < (registerRegion u .rdi 8).start + 8 at ha
      change (Stack.region u 0).start ≤ a ∧ a < (Stack.region u 0).start + (Stack.region u 0).size at hb
      rw [hout] at ha
      rw [he, hs] at hb
      omega
  · intro r hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)
  · change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0x19131 (by decide)

end P256.Proofs.ReadBe
