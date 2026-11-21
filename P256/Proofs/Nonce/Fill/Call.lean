import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Nonce.Fill.Memory
import P256.Proofs.Nonce.UpdateValue.Interface
import P256.Proofs.Program.ScalarFrame.CallStep

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

theorem call_address (frame : Frame initial s) :
    pushAddr s = stackPtr initial - 240 := by
  simp only [pushAddr, frame.rsp, frameBase, BitVec.sub_sub]
  rfl

theorem call_writes (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {target : RamState → BitVec 64} {ret : BitVec 64} :
    WritesWithin (callEffect target ret s).components #v[Stack.region initial 2096] := by
  intro c hc a hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · refine ⟨Stack.region initial 2096, by simp, ?_⟩
    rw [call_address frame] at hv
    exact ScalarFrame.stack_contains pre.toCalleePre (offset := 240)
      (by decide) (by decide) hv
  · exact hv.elim

theorem call_loaded (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret s).Holds s t) : ProgramLoaded t := by
  intro a b hb
  rw [effect.agrees.memoryWriteFrame (call_writes pre frame) a]
  · exact frame.loaded a b hb
  · intro region hr hin
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)

theorem call_generator (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret s).Holds s t)
    (generator : GeneratorAt s (initial.regValue .rdi) orderAddress state) :
    GeneratorAt t (initial.regValue .rdi) orderAddress state := by
  apply generator.of_frame pre.outputBounded pre.orderBounded
    (effect.agrees.memoryWriteFrame (call_writes pre frame))
  · intro region member
    have eq : region = Stack.region initial 2096 := by simpa using member
    subst region
    exact pre.separation 1 2 (by decide)
  · intro region member
    have eq : region = Stack.region initial 2096 := by simpa using member
    subst region
    exact pre.orderDisjoint _ (by simp)

theorem drbg_address (pre : Pre initial boundary orderAddress original) :
    (initial.regValue .rdi + 8).toNat = (initial.regValue .rdi).toNat + 8 := by
  have bound : (initial.regValue .rdi).toNat + 72 < 2^32 := pre.outputBounded
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by change (initial.regValue .rdi).toNat + 8 < 2^64; omega)

theorem drbg_sub (pre : Pre initial boundary orderAddress original) {a : Nat}
    (inside : (MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64).Contains a) :
    (registerRegion initial .rdi 72).Contains a := by
  change (initial.regValue .rdi + 8).toNat ≤ a ∧
    a < (initial.regValue .rdi + 8).toNat + 64 at inside
  rw [drbg_address pre] at inside
  change (initial.regValue .rdi).toNat ≤ a ∧ a < (initial.regValue .rdi).toNat + 72
  constructor <;> omega

theorem call_drbg_pre (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {entry ret : BitVec 64} {reserve : Nat}
    (capacity : reserve ≤ 1856) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => entry) ret s).Holds s t)
    (pointer : s.regValue .rdi = initial.regValue .rdi + 8)
    (returnInProgram : InProgram ret)
    (generator : GeneratorAt s (initial.regValue .rdi) orderAddress state) :
    DrbgCalleePre t boundary entry reserve state := by
  have bounds := stack_bounds pre.stack
  have rsp : stackPtr t = stackPtr initial - 240 :=
    effect.writes.1.trans (call_address frame)
  have sp : (stackPtr t).toNat = (stackPtr initial).toNat - 240 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (offset := 240) (by decide)
  have output : t.regValue .rdi = initial.regValue .rdi + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans pointer
  have sub : ∀ a, (registerRegion t .rdi 64).Contains a →
      (registerRegion initial .rdi 72).Contains a := by
    intro a ha
    apply drbg_sub pre
    simpa only [registerRegion, output] using ha
  have stackSub : ∀ a, (Stack.region t reserve).Contains a →
      (Stack.region initial 2096).Contains a := by
    intro a ha
    change (stackPtr t).toNat - reserve ≤ a ∧
      a < (Stack.region t reserve).start + (Stack.region t reserve).size at ha
    rw [stack_region_end, sp] at ha
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
    rw [stack_region_end]
    constructor <;> omega
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, t.external[a]? = some b :=
    Option.isSome_iff_exists.mp
      (effect.agrees.grow a (frame.allocated a (Option.isSome_iff_exists.mpr ha)))
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees frame.bindingsSupported ready effect.agrees
    machine := supportedMachine_of_ready_agrees frame.machine ready effect.agrees
    directionFlag := effect.agrees.directionFlagClear (by simp) frame.directionFlag
    loaded := call_loaded pre frame effect
    rip := effect.rip
    stateBounded := ?_
    stateAllocated := fun a ha => grow a (pre.outputAllocated a (sub a.toNat ha))
    stack := ?_
    separation := fun a ha hb => pre.separation 1 2 (by decide) a (sub a ha) (stackSub a hb)
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := by
      change InProgram (stackTop t)
      rw [(callEffect_stack effect).1]
      exact returnInProgram
    stateBytes := by rw [output]; exact (call_generator pre frame effect generator).2.2
  }
  · change (t.regValue .rdi).toNat + 64 < 2^32
    rw [output, drbg_address pre]
    have h : (initial.regValue .rdi).toNat + 72 < 2^32 := pre.outputBounded
    omega
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), ?_, ?_⟩
    · change (Stack.region t reserve).start + (Stack.region t reserve).size < 2^32
      rw [stack_region_end, sp]
      omega
    · change reserve ≤ (stackPtr t).toNat
      rw [sp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [sp]
      have hm : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro region member a inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pre.avoids _ (by simp) a (sub a.toNat inside)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat inside)

end P256.Proofs.Nonce.Fill
