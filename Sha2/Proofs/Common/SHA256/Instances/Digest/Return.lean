import Sha2.Proofs.Common.SHA256.Instances.Digest.Entry
import Sha2.Proofs.Common.Machine.Epilogue.ABI

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem returned {v : Wrapper.Variant} [bindings : Bindings] {initial p w : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data)
    (push : (Prologue.effect (Segment.prologue.pc v) .five272 initial).Holds initial p)
    (state : ExecutionState initial w (regions initial v))
    (rsp : rspOf w = stackPtr initial - 312)
    (rip : w.RIP = (Segment.epilogue.pc v))
    (rbp : w.regValue .rbp = initial.regValue .rbp)
    (preserved : ∀ x : BitVec 64, (stackPtr initial).toNat - 40 ≤ x.toNat →
      x.toNat < (stackPtr initial).toNat + 8 → w.external[x]? = p.external[x]?) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions initial v) ∧ final.external = w.external := by
  have stack : Stack.Valid initial 784 := call.stack
  have bounds : 784 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 :=
    stack_valid_bounds call.stack
  have word (offset : Nat) (bound : offset ≤ 40) :
      memLoad w.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad p.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (w.external[_]?).getD 0 = (p.external[_]?).getD 0
    have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - offset + i := by
      rw [BitVec.toNat_add, stack_valid_sub_toNat stack (by omega), BitVec.toNat_ofNat]
      omega
    rw [preserved _ (by rw [address]; omega) (by rw [address]; omega)]
  have returnP : memLoad p.external (stackPtr initial) 64 =
      memLoad initial.external (stackPtr initial) 64 := by
    apply memLoad_congr
    intro i hi
    change (p.external[_]?).getD 0 = (initial.external[_]?).getD 0
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply push.agrees.memory
    intro comp hc covered
    have rspeq : rspOf initial = stackPtr initial := by simp [rspOf, stackPtr, Operand.read]
    simp only [Prologue.effect, Prologue.registers, Epilogue.Layout.six,
      Bool.false_eq_true, ite_false, List.nil_append, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.append, List.cons_append, Effect.components,
      Write.component, Operand.component] at hc
    change comp ∈ [.mem (rspOf initial - 8) 8, .mem (rspOf initial - 16) 8,
      .mem (rspOf initial - 24) 8, .mem (rspOf initial - 32) 8,
      .mem (rspOf initial - 40) 8, .reg 4, .flags, .rip] at hc
    rw [rspeq] at hc
    have cannot (offset : Nat) (lo : 8 ≤ offset) (up : offset ≤ 40)
        (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Covers
          (stackPtr initial + BitVec.ofNat 64 i)) : False := by
      obtain ⟨j, hj, equal⟩ := covered
      have values := congrArg BitVec.toNat equal
      rw [BitVec.toNat_add, BitVec.toNat_add, stack_valid_sub_toNat stack (by omega),
        BitVec.toNat_ofNat, BitVec.toNat_ofNat] at values
      omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cannot 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) covered
    · exact cannot 16 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) covered
    · exact cannot 24 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) covered
    · exact cannot 32 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) covered
    · exact cannot 40 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) covered
    all_goals exact covered.elim
  have returnWord : memLoad w.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have same := word 0 (by (try dsimp only [routine]); decide +kernel)
    simp only [BitVec.sub_zero] at same
    exact same.trans returnP
  have read (offset : Nat) (bound : offset + 8 ≤ 312) :
      MemReadable w (rspOf w + BitVec.ofNat 64 offset) 8 := by
    rw [rsp]
    exact stack_frame_readable call.stack (frame := 312) (by (try dsimp only [routine]); decide +kernel) state.allocated bound
  have pre : Epilogue.Pre (Segment.epilogue.pc v) .five272 w :=
    ⟨rip, read 272 (by (try dsimp only [routine]); decide +kernel), read 280 (by (try dsimp only [routine]); decide +kernel), read 288 (by (try dsimp only [routine]); decide +kernel),
      read 296 (by (try dsimp only [routine]); decide +kernel), read 304 (by (try dsimp only [routine]); decide +kernel), trivial⟩
  have originalRSP : rspOf w + BitVec.ofNat 64 312 = stackPtr initial := by
    rw [rsp]; exact BitVec.sub_add_cancel _ _
  have retRead : MemReadable w (rspOf w + BitVec.ofNat 64 312) 8 := by
    rw [originalRSP]
    have h := Common.Encoding.Serialize.readable_of_grow
      (stack_valid_sub_readable call.stack (offset := 0) (len := 8) (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)) state.allocated
    simpa only [BitVec.sub_zero] using h
  have code : CodeIn (codeRange (Segment.epilogue.pc v) (Epilogue.bytes .five272 ++ [0xc3])) w := by
    rw [codeRange_append, CodeIn.append_iff]
    refine ⟨Segment.code .epilogue (v := v) state.loaded, ?_⟩
    have nextPC : Segment.epilogue.pc v + BitVec.ofNat 64 (Epilogue.bytes .five272).length =
        Segment.ret.pc v := by cases v <;> decide +kernel
    rw [nextPC]
    exact Segment.code .ret (v := v) state.loaded
  obtain ⟨steps, final, restored, run, ready, restoreEffect, retEffect, memory⟩ :=
    Epilogue.finish (Segment.epilogue.pc v) .five272 (returnBoundary initial)
      (valid_return_boundary machine call.stack call.returnAddress).2.2 (Segment.inside .epilogue (v := v))
      w (supportedMachine_readyToStep state.machine) code pre retRead
      (by change memLoad w.external (rspOf w + BitVec.ofNat 64 312) 64 = _
          rw [originalRSP]; exact returnWord)
      (by change rspOf w + BitVec.ofNat 64 312 + 8 = stackPtr initial + 8
          rw [originalRSP])
      (valid_return_boundary machine call.stack call.returnAddress).2.1
  have saved : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad w.external (rspOf w + BitVec.ofNat 64 (272 + offset)) 64 =
        (.reg r : Operand 64).read initial := by
    intro r offset member
    have bound : offset ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with h | h | h | h | h <;> omega
    rw [rsp]
    change memLoad w.external
      (stackPtr initial - BitVec.ofNat 64 312 + BitVec.ofNat 64 (272 + offset)) 64 = _
    rw [stack_frame_address initial (frame := 312) (offset := 272+offset) (by omega)]
    have sub : 312 - (272 + offset) = 40 - offset := by omega
    rw [sub, word (40-offset) (by omega)]
    have pushed := Write.allHold_iff.mp push.writes
    apply pushed (⟨(.mem (stackPtr initial - BitVec.ofNat 64 (40-offset)) : Operand 64),
      (.reg r : Operand 64).read initial⟩ : Write)
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six,
      List.zipIdx_cons, List.zipIdx_nil, rspOf, stackPtr, Operand.read]
  have abi := Epilogue.calleeSaved restoreEffect retEffect saved rbp
  have agrees := restoreEffect.agrees.trans retEffect.agrees
  have machineFinal := supportedMachine_of_ready_agrees state.machine ready agrees
  obtain ⟨prior, execution⟩ := state.execution
  have unique := (execution.returns run).unique_of_boundary
    (valid_return_boundary machine call.stack call.returnAddress).1
  obtain ⟨fuel, unique⟩ := unique
  refine ⟨fuel, final, unique, machineFinal, abi, ?_, ?_, memory⟩
  · exact agrees.directionFlagClear (by
      simp [Epilogue.effect, Epilogue.Layout.six, Effect.components, X86Proofs.retEffect]) state.directionFlag
  · intro addr outside
    rw [memory]
    exact state.frame addr outside

end Sha2.Proofs.Common.SHA256.Instances.Digest
