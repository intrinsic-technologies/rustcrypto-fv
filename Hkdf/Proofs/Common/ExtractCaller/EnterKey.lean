import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.ExtractCaller.Prepare
import Hkdf.Proofs.Common.ExtractCaller.Call
import Hkdf.Proofs.Common.ExtractCaller.KeyContext

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.EnterKey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine

abbrev routine (simple : Bool) : Routine :=
  if simple then simpleHkdfSha256Extract else hkdfSha256Extract

def layout (simple : Bool) :
    Hkdf.Proofs.Common.CallFrame.StackCallLayout (routine simple).minStackBytes 32 64 720 :=
  match simple with
  | false => KeyContext.standardLayout
  | true => KeyContext.simpleLayout

def returnPC (simple : Bool) : BitVec 64 := if simple then 0x105cec else 0x101497

theorem return_outside {initial : RamState} {r : Routine}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall r initial salt inputs) : ¬ InProgram (returnBoundary initial).rip := by
  obtain ⟨address, stored, _, outside⟩ := call.returnAddress
  have value : (returnBoundary initial).rip = address := by
    change memLoad initial.external (initial.regValue .rsp) 64 = address
    apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using stored.2
  rwa [value]

theorem default_address {initial s : RamState} (simple : Bool)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple)) :
    rspOf s + (BitVec.ofNat 32 (Prepare.saltDisplacement simple)).signExtend 64 =
      stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset := by
  rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp]
  cases simple
  all_goals simp only [Prepare.allocation, Prepare.saltDisplacement, layout,
    KeyContext.standardLayout, KeyContext.simpleLayout, ↓reduceIte, Bool.false_eq_true,
    BitVec.reduceSignExtend]
  all_goals rw [Prepare.stack_offset_address]
  all_goals rfl

theorem default_apart_call (simple : Bool) :
    OffsetsApart (-BitVec.ofNat 64 (layout simple).inputOffset) 32
      (-BitVec.ofNat 64 (Prepare.allocation simple + 8)) 8 := by
  cases simple <;> unfold OffsetsApart <;> decide +kernel

theorem default_after_call {initial u t : RamState} {ret : BitVec 64} (simple : Bool)
    (rsp : stackPtr u = stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple))
    (effect : (callEffect (fun _ => 0x116320) ret u).Holds u t)
    (zeros : (⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat, 32⟩ :
      MemoryRegion).HasBytes u.external ⟨Array.replicate 32 0⟩) :
    (⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat, 32⟩ :
      MemoryRegion).HasBytes t.external ⟨Array.replicate 32 0⟩ := by
  refine ⟨zeros.1, ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
  have pushed : pushAddr u =
      stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  rw [effect.agrees.memory _]
  · exact zeros.2 i
  · intro c hc cover
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact cover.elim
    · obtain ⟨j, hj, eq⟩ := cover
      apply OffsetsApart.ne (default_apart_call simple) (stackPtr initial) hi hj (by decide)
      simpa only [pushed, BitVec.sub_eq_add_neg, BitVec.ofNat_add, BitVec.ofNat_toNat,
        BitVec.setWidth_eq] using eq
    · exact cover.elim

theorem selected_arguments {initial s u : RamState} {r : Routine}
    {salt : Option ByteArray} {inputs : Array Input} {default : BitVec 64}
    (call : ValidExtractCall r initial salt inputs)
    (rcx : s.regValue .rcx = initial.regValue .rcx)
    (r8 : s.regValue .r8 = initial.regValue .r8)
    (input : (Operand.reg 6 : Operand 64).read u =
      if (Operand.reg 1 : Operand 64).read s = 0 then default else (Operand.reg 1 : Operand 64).read s)
    (length : (Operand.reg 2 : Operand 64).read u =
      if (Operand.reg 1 : Operand 64).read s = 0 then 32 else (Operand.reg 8 : Operand 64).read s) :
    u.regValue .rsi = (match salt with | none => default | some _ => initial.regValue .rcx) ∧
      (u.regValue .rdx).toNat = (Standard.saltKey salt).size := by
  have cx : (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx := by
    exact (show (Operand.reg 1 : Operand 64).read s = s.regValue .rcx from by
      rw [Operand.read_reg64]; rfl).trans rcx
  have r8read : (Operand.reg 8 : Operand 64).read s = initial.regValue .r8 := by
    exact (show (Operand.reg 8 : Operand 64).read s = s.regValue .r8 from by
      rw [Operand.read_reg64]; rfl).trans r8
  have si : (Operand.reg 6 : Operand 64).read u = u.regValue .rsi := by
    rw [Operand.read_reg64]; rfl
  have dx : (Operand.reg 2 : Operand 64).read u = u.regValue .rdx := by
    rw [Operand.read_reg64]; rfl
  rw [cx, si] at input
  rw [cx, dx, r8read] at length
  cases salt with
  | none =>
    have null := call.saltPointerArgumentIsNullIffNoSalt.mpr rfl
    simp only [null, ↓reduceIte] at input length
    refine ⟨input, ?_⟩
    rw [length]
    rfl
  | some bytes =>
    have nonnull : initial.regValue .rcx ≠ 0 := by
      intro zero
      have impossible := call.saltPointerArgumentIsNullIffNoSalt.mp zero
      cases impossible
    simp only [nonnull, ↓reduceIte] at input length
    refine ⟨input, ?_⟩
    rw [length]
    exact call.saltLengthArgumentMatchesSalt bytes (by simp)

theorem run [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input} (simple : Bool)
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (call : ValidExtractCall (routine simple) initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial (routine simple).minStackBytes] s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (Prepare.middleOffset simple))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple))
    (rcx : s.regValue .rcx = initial.regValue .rcx)
    (r8 : s.regValue .r8 = initial.regValue .r8) :
    ∃ t, Running initial (returnBoundary initial)
        #v[Stack.region initial (routine simple).minStackBytes] t ∧
      Key.Context t (returnBoundary initial) (Standard.saltKey salt) ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (layout simple).stackOffset ∧
      t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (layout simple).outputOffset ∧
      returnBoundary t =
        ⟨returnPC simple, stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple)⟩ ∧
      MemoryWriteFrame s t
        #v[(⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat, 32⟩ :
          MemoryRegion),
          (⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).stackOffset).toNat, 8⟩ :
          MemoryRegion)] ∧ Hkdf.Proofs.Program.PreservesABI s t := by
  have outside := return_outside call
  have avoid : (Stack.region initial (routine simple).minStackBytes).Avoids
      (fun a => InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (call.stackSeparation.2 _ (by simp)).2
  obtain ⟨_, u, _, _, runningU, ripU, rspU, outputU, inputU, lengthU, zerosU, prepareFrame⟩ :=
    Prepare.run simple call.stack avoid running (by cases simple <;> decide +kernel)
      outside rip rsp
  have output : u.regValue .rdi =
      stackPtr initial - BitVec.ofNat 64 (layout simple).outputOffset := by
    have read : (Operand.reg 7 : Operand 64).read u = u.regValue .rdi := by
      rw [Operand.read_reg64]; rfl
    rw [read] at outputU
    rw [outputU]
    cases simple
    · change rspOf s + 120 = stackPtr initial - 400
      rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp,
        Prepare.stack_offset_address]
      rfl
    · exact (show rspOf s = stackPtr s from Operand.read_reg64 s 4).trans rsp
  obtain ⟨input, length⟩ := selected_arguments call rcx r8 inputU lengthU
  have zeros : (⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat, 32⟩ :
      MemoryRegion).HasBytes u.external ⟨Array.replicate 32 0⟩ := by
    rw [default_address simple rsp] at zerosU
    exact zerosU
  have called : ∃ t, Running initial (returnBoundary initial)
        #v[Stack.region initial (routine simple).minStackBytes] t ∧
      (callEffect (fun _ => 0x116320) (returnPC simple) u).Holds u t ∧
      t.RIP = 0x116320 ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (layout simple).stackOffset ∧
      returnBoundary t =
        ⟨returnPC simple, stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple)⟩ := by
    cases simple
    · exact Call.standard call runningU outside (rspU.trans rsp) ripU
    · exact Call.simple call runningU outside (rspU.trans rsp) ripU
  obtain ⟨t, runningT, effect, ripT, rspT, retT⟩ := called
  let zeroRegion : MemoryRegion :=
    ⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat, 32⟩
  let callRegion : MemoryRegion :=
    ⟨(stackPtr initial - BitVec.ofNat 64 (layout simple).stackOffset).toNat, 8⟩
  have capacity := (layout simple).capacity
  have above := (layout simple).inputAbove
  have inputEnd := (layout simple).inputEnd
  have stackBounds := stack_bounds call.stack
  have zeroNat : (stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat =
      (stackPtr initial).toNat - (layout simple).inputOffset :=
    Hkdf.Proofs.Common.CallFrame.stack_sub_toNat call.stack (by omega)
  have zeroBounded : zeroRegion.Bounded := by
    change (stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset).toNat + 32 < 2^32
    rw [zeroNat]
    omega
  have preparation : MemoryWriteFrame s u #v[zeroRegion, callRegion] := by
    apply prepareFrame.memoryWriteFrame
    intro c hc a cover
    simp only [Prepare.middleEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals refine ⟨zeroRegion, by simp, ?_⟩
    all_goals rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp] at cover
    all_goals cases simple
    all_goals simp only [Prepare.allocation, Prepare.saltDisplacement, Bool.false_eq_true,
      ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSignExtend] at cover
    all_goals rw [Prepare.stack_offset_address] at cover
    all_goals simp only [BitVec.reduceSub] at cover
    all_goals obtain ⟨i, hi, rfl⟩ := cover
    all_goals apply Common.Machine.contains_offset_of_subrange zeroBounded ?_ ?_ i hi
    all_goals dsimp only [zeroRegion]
    all_goals rw [zeroNat, Hkdf.Proofs.Common.CallFrame.stack_sub_toNat call.stack (by decide +kernel)]
    all_goals simp only [layout, KeyContext.standardLayout, KeyContext.simpleLayout] at *
    all_goals omega
  have pushed : pushAddr u =
      stackPtr initial - BitVec.ofNat 64 (layout simple).stackOffset :=
    effect.writes.1.symm.trans rspT
  have callBounded : callRegion.Bounded := by
    change (stackPtr initial - BitVec.ofNat 64 (layout simple).stackOffset).toNat + 8 < 2^32
    rw [Hkdf.Proofs.Common.CallFrame.stack_sub_toNat call.stack (by omega)]
    omega
  have callFrame : MemoryWriteFrame u t #v[zeroRegion, callRegion] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a cover
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact cover.elim
    · refine ⟨callRegion, by simp, ?_⟩
      apply Hkdf.Proofs.Common.Machine.contains_of_mem_covers callBounded
      simpa only [pushed, callRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using cover
    · exact cover.elim
  have preciseFrame := memoryWriteFrame_trans preparation callFrame
  have outputT : t.regValue .rdi =
      stackPtr initial - BitVec.ofNat 64 (layout simple).outputOffset :=
    (effect.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans output
  have inputT : t.regValue .rsi =
      (match salt with
        | none => stackPtr initial - BitVec.ofNat 64 (layout simple).inputOffset
        | some _ => initial.regValue .rcx) := by
    have same : t.regValue .rsi = u.regValue .rsi :=
      effect.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])
    cases salt
    · exact same.trans (input.trans (default_address simple rsp))
    · exact same.trans input
  have lengthT : (t.regValue .rdx).toNat = (Standard.saltKey salt).size := by
    have same : t.regValue .rdx = u.regValue .rdx :=
      effect.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])
    rw [same]
    exact length
  have zerosT := default_after_call simple (rspU.trans rsp) effect zeros
  have ret : InProgram (returnBoundary t).rip := by
    rw [retT]
    cases simple
    · exact inProgram_of_textOffset 0x1497 (by decide)
    · exact inProgram_of_textOffset 0x5cec (by decide)
  have totalFrame := prepareFrame.trans effect.agrees
  have abi : Hkdf.Proofs.Program.PreservesABI s t :=
    Hkdf.Proofs.Common.Machine.preservesABI_of_agrees totalFrame running.directionFlag (by
      intro register member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact totalFrame.read (n := 64) (r := 3) (by simp [Prepare.middleEffect,
            Effect.components, Write.component, Operand.component, callEffect, pushEffect])
        | exact totalFrame.read (n := 64) (r := 5) (by simp [Prepare.middleEffect,
            Effect.components, Write.component, Operand.component, callEffect, pushEffect])
        | exact totalFrame.read (n := 64) (r := 12) (by simp [Prepare.middleEffect,
            Effect.components, Write.component, Operand.component, callEffect, pushEffect])
        | exact totalFrame.read (n := 64) (r := 13) (by simp [Prepare.middleEffect,
            Effect.components, Write.component, Operand.component, callEffect, pushEffect])
        | exact totalFrame.read (n := 64) (r := 14) (by simp [Prepare.middleEffect,
            Effect.components, Write.component, Operand.component, callEffect, pushEffect])
        | exact totalFrame.read (n := 64) (r := 15) (by simp [Prepare.middleEffect,
            Effect.components, Write.component, Operand.component, callEffect, pushEffect]))
      (by simp [Prepare.middleEffect, Effect.components, Write.component, Operand.component,
        callEffect, pushEffect])
      (by simp [Prepare.middleEffect, Effect.components, Write.component, Operand.component,
        callEffect, pushEffect])
      (by simp [Prepare.middleEffect, Effect.components, Write.component, Operand.component,
        callEffect, pushEffect])
  refine ⟨t, runningT, ?_, rspT, outputT, retT, preciseFrame, abi⟩
  cases salt
  all_goals (exact KeyContext.key_context environment call runningT (layout simple) ripT rspT outputT ret lengthT inputT (fun _ => zerosT))

end Hkdf.Proofs.Common.ExtractCaller.EnterKey
