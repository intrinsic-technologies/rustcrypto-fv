import Hkdf.Proofs.Program
import Hkdf.Proofs.Common.Machine
import Hkdf.Proofs.Common.Machine.CallReturn
import Hkdf.Proofs.Common.Machine.Entry
import Hkdf.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

namespace Hkdf.Proofs.Common.CallFrame

theorem programLoaded_of_memoryWriteFrame {s t : RamState}
    {n : Nat} {regions : Vector MemoryRegion n}
    (h : MemoryWriteFrame s t regions)
    (hLoaded : Hkdf.Spec.Program.ProgramLoaded s)
    (havoid : ∀ r ∈ regions, r.Avoids Hkdf.Spec.Program.InProgram) :
    Hkdf.Spec.Program.ProgramLoaded t := by
  intro address byte hmem
  rw [h address (by
    intro r hr hin
    exact havoid r hr address hin ⟨byte, hmem⟩)]
  exact hLoaded address byte hmem

structure Running [bindings : Bindings] {n : Nat} (initial : RamState)
    (boundary : ReturnBoundary) (regions : Vector MemoryRegion n) (s : RamState) : Prop where
  execution : ∃ fuel, Advances boundary fuel initial s
  machine : SupportedMachine bindings s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  directionFlag : RFLAGS.DirectionFlagClear s.RFLAGS
  frame : MemoryWriteFrame initial s regions

theorem frame_mono {s t : RamState} {m n : Nat}
    {small : Vector MemoryRegion m} {large : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t small)
    (within : ∀ region ∈ small, ∀ a, region.Contains a → ∃ outer ∈ large, outer.Contains a) :
    MemoryWriteFrame s t large := by
  intro a outside
  apply frame a
  intro region hr ha
  obtain ⟨outer, ho, hin⟩ := within region hr a.toNat ha
  exact outside outer ho hin

theorem frame_agrees {s t : RamState} {n : Nat} {regions : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t regions) {address : BitVec 64} {size : Nat}
    (apart : ∀ a, (Component.mem address size).Covers a →
      ∀ region ∈ regions, ¬ region.Contains a.toNat) :
    (Component.mem address size).Agrees s t :=
  fun i hi ↦ frame _ (apart _ ⟨i, hi, rfl⟩)

theorem frame_agrees_of_disjoint {s t : RamState} {n : Nat}
    {regions : Vector MemoryRegion n} (frame : MemoryWriteFrame s t regions)
    {address : BitVec 64} {size : Nat}
    (bounded : address.toNat + size ≤ 2^64)
    (apart : ∀ region ∈ regions, (⟨address.toNat, size⟩ : MemoryRegion).Disjoint region) :
    (Component.mem address size).Agrees s t := by
  apply frame_agrees frame
  intro a ha region hr hin
  obtain ⟨i, hi, rfl⟩ := ha
  have hi64 : i < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
    Nat.mod_eq_of_lt (by omega)] at hin
  apply apart region hr _ ?_ hin
  change address.toNat ≤ address.toNat + i ∧ address.toNat + i < address.toNat + size
  constructor <;> omega

theorem frame_hasBytes {s t : RamState} {n : Nat} {regions : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t regions) {region : MemoryRegion} {bytes : ByteArray}
    (apart : ∀ written ∈ regions, region.Disjoint written)
    (bounded : region.start + region.size ≤ 2^64)
    (stored : region.HasBytes s.external bytes) : region.HasBytes t.external bytes := by
  refine ⟨stored.1, fun i ↦ ?_⟩
  rw [frame _]
  · exact stored.2 i
  · intro written hw hin
    have low : region.start + i.val < 2^64 := by
      have := i.isLt
      have := stored.1
      change bytes.size = region.size at this
      omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt low] at hin
    exact apart written hw _ ⟨by omega, by have := i.isLt; have := stored.1; unfold MemoryRegion.HasLength at this; omega⟩ hin

theorem agrees_memLoad {s t : RamState} {address : BitVec 64} {width : Nat}
    (same : (Component.mem address (width / 8)).Agrees s t) :
    memLoad t.external address width = memLoad s.external address width := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [same i hi]

theorem agrees_memLoad_offset {s t : RamState} {base : BitVec 64}
    {length offset width : Nat} (same : (Component.mem base length).Agrees s t)
    (within : offset + width / 8 ≤ length) :
    memLoad t.external (base + BitVec.ofNat 64 offset) width =
      memLoad s.external (base + BitVec.ofNat 64 offset) width := by
  apply agrees_memLoad
  intro i hi
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using same (offset + i) (by omega)

theorem agrees_memLoad_slots {s t : RamState} {base : BitVec 64} {length : Nat}
    {α : Type} (same : (Component.mem base length).Agrees s t)
    (slots : List α) (offset : α → Nat) (within : ∀ slot ∈ slots, offset slot + 8 ≤ length) :
    ∀ slot ∈ slots, memLoad t.external (base + BitVec.ofNat 64 (offset slot)) 64 =
      memLoad s.external (base + BitVec.ofNat 64 (offset slot)) 64 :=
  fun slot member ↦ agrees_memLoad_offset same (within slot member)

theorem agrees_loadBytes {s t : RamState} {address : BitVec 64} {size : Nat}
    (same : (Component.mem address size).Agrees s t) :
    loadBytes t.external address size = loadBytes s.external address size :=
  Hkdf.Proofs.Common.Memory.loadBytes_congr same

theorem Running.initial [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {n : Nat} {regions : Vector MemoryRegion n}
    (machine : SupportedMachine bindings s) (loaded : ProgramLoaded s)
    (direction : RFLAGS.DirectionFlagClear s.RFLAGS) : Running s boundary regions s :=
  ⟨⟨0, (advances_zero boundary s s).mpr rfl⟩, machine, loaded, fun _ h ↦ h, direction,
    memoryWriteFrame_refl s regions⟩

theorem Running.of_agrees [bindings : Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {n fuel : Nat} {regions : Vector MemoryRegion n}
    {components : List Component} (h : Running initial boundary regions s)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (writes : WritesWithin components regions)
    (avoids : ∀ region ∈ regions, region.Avoids InProgram)
    (df : .df ∉ components) : Running initial boundary regions t := by
  have frame := agrees.memoryWriteFrame writes
  obtain ⟨previous, execution⟩ := h.execution
  exact ⟨⟨previous + fuel, execution.trans run⟩,
    supportedMachine_of_ready_agrees h.machine ready agrees,
    programLoaded_of_memoryWriteFrame frame h.loaded avoids,
    fun a ha ↦ agrees.grow a (h.allocated a ha),
    agrees.directionFlagClear df h.directionFlag, memoryWriteFrame_trans h.frame frame⟩

theorem Running.of_callee [bindings : Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {n outputBytes reserve : Nat}
    {regions : Vector MemoryRegion n} (h : Running initial boundary regions s)
    (result : CalleeResult s t boundary outputBytes reserve)
    (within : ∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
      ∀ a, region.Contains a → ∃ outer ∈ regions, outer.Contains a) :
    Running initial boundary regions t := by
  obtain ⟨previous, execution⟩ := h.execution
  obtain ⟨fuel, run⟩ := result.execution
  exact ⟨⟨previous + fuel, execution.trans run⟩, result.machine, result.loaded,
    fun a ha ↦ result.allocated a (h.allocated a ha), result.abi.2.1,
    memoryWriteFrame_trans h.frame (frame_mono result.frame within)⟩

theorem callee_agrees [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve : Nat} (result : CalleeResult s t boundary outputBytes reserve)
    {address : BitVec 64} {size : Nat}
    (apart : ∀ a, (Component.mem address size).Covers a →
      ∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
        ¬ region.Contains a.toNat) : (Component.mem address size).Agrees s t :=
  frame_agrees result.frame apart

theorem call_boundary {s t : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret s).Holds s t) :
    returnBoundary t = ⟨ret, stackPtr s⟩ := by
  obtain ⟨top, rsp⟩ := callEffect_stack effect
  change (⟨stackTop t, stackPtr t + 8⟩ : ReturnBoundary) = _
  rw [top, rsp]

theorem Running.call [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {n : Nat} {regions : Vector MemoryRegion n}
    {pre : RamState → Prop} {code : CodeMap} {target : RamState → BitVec 64}
    {ret : BitVec 64} (h : Running initial boundary regions s)
    (step : StepEffect pre code (callEffect target ret))
    (instruction : CodeIn code s) (precondition : pre s)
    (continues : target s ≠ boundary.rip)
    (writes : WritesWithin (callEffect target ret s).components regions)
    (avoids : ∀ region ∈ regions, region.Avoids InProgram) :
    ∃ t, Running initial boundary regions t ∧
      (callEffect target ret s).Holds s t ∧ returnBoundary t = ⟨ret, stackPtr s⟩ := by
  obtain ⟨t, run, ready, effect⟩ := step.advances
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep h.machine)
    instruction precondition continues
  exact ⟨t, h.of_agrees run ready effect.agrees writes avoids
    (by simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil,
      or_false, reduceCtorEq, not_false_eq_true]), effect, call_boundary effect⟩

theorem call_frame {s u : RamState} {reserve : Nat}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (stack : Stack.Valid u reserve) (call : (callEffect target ret s).Holds s u) :
    MemoryWriteFrame s u #v[Stack.region u reserve] := by
  apply call.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · refine ⟨Stack.region u reserve, by simp, ?_⟩
    rw [show pushAddr s = stackPtr u from call.writes.1.symm] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact Hkdf.Proofs.Common.Machine.memoryRegion_contains_add stack.1
      (len := 8) (by change (stackPtr u).toNat - reserve ≤ (stackPtr u).toNat; omega)
      (by rw [stack_region_end]; exact Nat.le_refl _) hi
  · exact ha.elim

theorem call_result [Bindings] {s u t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre u boundary entry inputBytes outputBytes reserve)
    (call : (callEffect target ret s).Holds s u)
    (result : CalleeResult u t boundary outputBytes reserve)
    (direction : RFLAGS.DirectionFlagClear s.RFLAGS) :
    MemoryWriteFrame s t #v[registerRegion u .rdi outputBytes, Stack.region u reserve] ∧
      PreservesABI s t := by
  have frame : MemoryWriteFrame s u
      #v[registerRegion u .rdi outputBytes, Stack.region u reserve] :=
    frame_mono (call_frame pre.stack call) (by
      intro region member a contains
      have eq : region = Stack.region u reserve := by simpa using member
      subst region
      exact ⟨Stack.region u reserve, by simp, contains⟩)
  have abi : PreservesABI s u := by
    apply Hkdf.Proofs.Common.Machine.preservesABI_of_agrees call.agrees direction
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact call.agrees.read (n := 64) (r := 3) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 5) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 12) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 13) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 14) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 15) (by simp [callEffect, pushEffect_components])
    all_goals simp [callEffect, pushEffect_components]
  exact ⟨memoryWriteFrame_trans frame result.frame,
    Hkdf.Proofs.Common.Machine.preservesABI_trans abi result.abi⟩

end Hkdf.Proofs.Common.CallFrame
