import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Input
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.XLoad
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.YLoad
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.XStore
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.YStore
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def loadEffect (y : Bool) : RamState → Effect := if y then yLoadEffect else xLoadEffect

def storeEffect (y : Bool) : RamState → Effect := if y then yStoreEffect else xStoreEffect

def storeComponents (t : RamState) : List Component :=
  [.mem (stackPtr t + 168) 8, .mem (stackPtr t + 176) 8,
    .mem (stackPtr t + 184) 8, .mem (stackPtr t + 192) 8, .rip]

theorem load_components (y : Bool) (t : RamState) :
    (loadEffect y t).components = [.reg 0, .reg 1, .reg (if y then 7 else 6), .reg 2, .rip] := by
  cases y <;> rfl

theorem store_components (y : Bool) (t : RamState) :
    (storeEffect y t).components = storeComponents t := by
  cases y <;> simp [storeEffect, xStoreEffect, yStoreEffect, Effect.components, storeComponents]

theorem load_correct [Bindings] (y : Bool) {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = if y then 0x110635 else 0x110820)
    (source : (if y then t.regValue .rsi else t.regValue .rbp) = s.regValue .rsi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (loadEffect y t).Holds t u := by
  have run : ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧
      (loadEffect y t).Holds t u := by
    cases y with
    | false =>
      obtain ⟨fuel, u, run, ready, _, effect⟩ := x_load boundary pre.outerBoundary t
        (readyToStep state.machine state.bindingsSupported)
        (programText_slice (programLoaded_codeIn state.loaded) 0x10820 xLoadBytes
          (by decide) (by decide +kernel))
        ⟨rip, by
          intro off hoff
          have cases : off = 1 ∨ off = 9 ∨ off = 17 ∨ off = 25 := by simpa using hoff
          rcases cases with rfl | rfl | rfl | rfl
          · change MemReadable t (t.regValue .rbp + 1) 8
            rw [show t.regValue .rbp = s.regValue .rsi from source]
            exact input_limb_readable pre state 1 (by decide)
          · change MemReadable t (t.regValue .rbp + 9) 8
            rw [show t.regValue .rbp = s.regValue .rsi from source]
            exact input_limb_readable pre state 9 (by decide)
          · change MemReadable t (t.regValue .rbp + 17) 8
            rw [show t.regValue .rbp = s.regValue .rsi from source]
            exact input_limb_readable pre state 17 (by decide)
          · change MemReadable t (t.regValue .rbp + 25) 8
            rw [show t.regValue .rbp = s.regValue .rsi from source]
            exact input_limb_readable pre state 25 (by decide)
        ⟩
      exact ⟨fuel, u, run, ready, effect⟩
    | true =>
      obtain ⟨fuel, u, run, ready, _, effect⟩ := y_load boundary pre.outerBoundary t
        (readyToStep state.machine state.bindingsSupported)
        (programText_slice (programLoaded_codeIn state.loaded) 0x10635 yLoadBytes
          (by decide) (by decide +kernel))
        ⟨rip, by
          intro off hoff
          have cases : off = 33 ∨ off = 41 ∨ off = 49 ∨ off = 57 := by simpa using hoff
          rcases cases with rfl | rfl | rfl | rfl
          · change MemReadable t (t.regValue .rsi + 33) 8
            rw [show t.regValue .rsi = s.regValue .rsi from source]
            exact input_limb_readable pre state 33 (by decide)
          · change MemReadable t (t.regValue .rsi + 41) 8
            rw [show t.regValue .rsi = s.regValue .rsi from source]
            exact input_limb_readable pre state 41 (by decide)
          · change MemReadable t (t.regValue .rsi + 49) 8
            rw [show t.regValue .rsi = s.regValue .rsi from source]
            exact input_limb_readable pre state 49 (by decide)
          · change MemReadable t (t.regValue .rsi + 57) 8
            rw [show t.regValue .rsi = s.regValue .rsi from source]
            exact input_limb_readable pre state 57 (by decide)
        ⟩
      exact ⟨fuel, u, run, ready, effect⟩
  obtain ⟨fuel, u, run, ready, effect⟩ := run
  have agrees := effect.agrees
  rw [load_components] at agrees
  exact ⟨fuel, u, run, state.after_registers ready agrees
    (by simp [Component.Covers]) (by cases y <;> simp), effect⟩

theorem store_run [Bindings] (y : Bool) {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = if y then 0x110651 else 0x11083c) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧
      (storeEffect y t).Holds t u := by
  have writable : ∀ off ∈ ([168,176,184,192] : List (BitVec 64)),
      P256.Proofs.Common.Instructions.CrossPageStore.Writable t (stackPtr t + off) 8 := by
    intro off hoff
    have cases : off = 168 ∨ off = 176 ∨ off = 184 ∨ off = 192 := by simpa using hoff
    rcases cases with rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_writable pre.toCalleePre state (by decide) (by decide) (by decide)
  cases y with
  | false =>
    obtain ⟨fuel, u, run, ready, _, effect⟩ := x_store boundary pre.outerBoundary t
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x1083c xStoreBytes
        (by decide) (by decide +kernel))
      ⟨rip, writable, by
        intro off hoff
        have cases : off = 168 ∨ off = 176 ∨ off = 184 ∨ off = 192 := by simpa using hoff
        rcases cases with rfl | rfl | rfl | rfl
        all_goals exact ScalarFrame.stack_code pre.toCalleePre state (codeOffset := 0x1083c) (by decide) (by decide) (by decide)
      ⟩
    exact ⟨fuel, u, run, ready, effect⟩
  | true =>
    obtain ⟨fuel, u, run, ready, _, effect⟩ := y_store boundary pre.outerBoundary t
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x10651 yStoreBytes
        (by decide) (by decide +kernel))
      ⟨rip, writable, by
        intro off hoff
        have cases : off = 168 ∨ off = 176 ∨ off = 184 ∨ off = 192 := by simpa using hoff
        rcases cases with rfl | rfl | rfl | rfl
        all_goals exact ScalarFrame.stack_code pre.toCalleePre state (codeOffset := 0x10651) (by decide) (by decide) (by decide)
      ⟩
    exact ⟨fuel, u, run, ready, effect⟩

theorem store_work [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t) :
    WritesWithin (storeComponents t)
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
  intro c hc a ha
  simp only [storeComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  all_goals
    refine ⟨ScalarFrame.workRegion s 3360, by simp, ?_⟩
    first
    | have address : stackPtr t + 168 = stackPtr s - 592 := by
        rw [state.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [address] at ha
    | have address : stackPtr t + 176 = stackPtr s - 584 := by
        rw [state.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [address] at ha
    | have address : stackPtr t + 184 = stackPtr s - 576 := by
        rw [state.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [address] at ha
    | have address : stackPtr t + 192 = stackPtr s - 568 := by
        rw [state.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [address] at ha
    exact ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha

theorem store_correct [Bindings] (y : Bool) {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = if y then 0x110651 else 0x11083c) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (storeEffect y t).Holds t u := by
  obtain ⟨fuel, u, run, ready, effect⟩ := store_run y pre state rip
  have agrees := effect.agrees
  rw [store_components] at agrees
  exact ⟨fuel, u, run, state.after_effect pre.toCalleePre (by decide) ready agrees
    (store_work pre state) (by simp [storeComponents]), effect⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
