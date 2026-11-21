import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.Buffered.Update.Contracts

namespace Sha1.Proofs.Streaming

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered

namespace UpdateFinalize

def stackWord (s : RamState) (offset : Nat) : BitVec 64 :=
  (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s

structure LoopInvariant (P : Nat → RamState → Prop)
    (initial : RamState) (start finish index : Nat) (s : RamState) : Prop where
  state : P index s
  indexValue : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 index
  countValue : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 finish
  pointers : stackWord s 0xc8 = (Operand.reg 7 : Operand 64).read initial
  lengths : stackWord s 0xd0 = (Operand.reg 6 : Operand 64).read initial

theorem updatePre_of_invariant [Bindings] {boundary : ReturnBoundary}
    {initial s : RamState} {message input : ByteArray}
    {start finish index : Nat}
    (h : LoopInvariant
      (fun _ s => UpdatePre .updateFinalize boundary message input s)
      initial start finish index s) :
    UpdatePre .updateFinalize boundary message input s :=
  h.state

theorem loop_complete [Bindings] {P : Nat → RamState → Prop} {boundary : ReturnBoundary}
    {initial : RamState} {start finish : Nat} {s : RamState}
    (hbound : start ≤ finish)
    (hstep : ∀ i, start ≤ i → i < finish → ∀ t,
      LoopInvariant P initial start finish i t →
      ∃ fuel u, Advances boundary fuel t u ∧
        LoopInvariant P initial start finish (i + 1) u)
    (hs : LoopInvariant P initial start finish start s) :
    ∃ fuel t, Advances boundary fuel s t ∧
      LoopInvariant P initial start finish finish t := by
  have loop (count : Nat) (hcount : start + count ≤ finish) :
      ∃ fuel t, Advances boundary fuel s t ∧
        LoopInvariant P initial start finish (start + count) t := by
    induction count with
    | zero => exact ⟨0, s, (advances_zero boundary s s).mpr rfl, hs⟩
    | succ count ih =>
      obtain ⟨fuel, t, hrun, ht⟩ := ih (by omega)
      obtain ⟨steps, u, hrun', hu⟩ := hstep (start + count) (by omega) (by omega) t ht
      exact ⟨fuel + steps, u, hrun.trans hrun', hu⟩
  simpa only [Nat.add_sub_of_le hbound] using loop (finish - start) (by omega)

end UpdateFinalize


theorem advances_loop [Bindings] {boundary : ReturnBoundary}
    {invariant : Nat → RamState → Prop} {start finish : Nat}
    (hbound : start ≤ finish)
    (hstep : ∀ i, start ≤ i → i < finish → ∀ s, invariant i s →
      ∃ fuel t, Advances boundary fuel s t ∧ invariant (i + 1) t)
    {s : RamState} (hs : invariant start s) :
    ∃ fuel t, Advances boundary fuel s t ∧ invariant finish t := by
  have loop (count : Nat) (hcount : start + count ≤ finish) :
      ∃ fuel t, Advances boundary fuel s t ∧ invariant (start + count) t := by
    induction count with
    | zero => exact ⟨0, s, (advances_zero boundary s s).mpr rfl, hs⟩
    | succ count ih =>
      obtain ⟨fuel, t, hrun, ht⟩ := ih (by omega)
      obtain ⟨steps, u, hrun', hu⟩ := hstep (start + count) (by omega) (by omega) t ht
      exact ⟨fuel + steps, u, hrun.trans hrun', hu⟩
  simpa only [Nat.add_sub_of_le hbound] using loop (finish - start) (by omega)


structure EffectRun [Bindings] (boundary : ReturnBoundary)
    (pre : RamState → Prop) (code : CodeMap) (effect : RamState → Effect)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  codeIn : CodeIn code t
  holds : (effect s).Holds s t


theorem EffectRun.of_block [Bindings] {boundary : ReturnBoundary}
    {pre : RamState → Prop} {code : CodeMap} {effect : RamState → Effect}
    {s : RamState} (h : ReadyToStep s) (hc : CodeIn code s) (hp : pre s)
    (hblock : AdvancesBlock boundary pre code effect) :
    ∃ t, EffectRun boundary pre code effect s t := by
  rcases hblock s h hc hp with ⟨fuel, t, ha, hr, hcode, he⟩
  exact ⟨t, ⟨⟨fuel, ha⟩, hr, hcode, he⟩⟩


theorem effect_seq [Bindings] {boundary : ReturnBoundary}
    {P Q : RamState → Prop} {code code₂ : CodeMap}
    {E e : RamState → Effect}
    (hFirst : AdvancesBlock boundary P code E)
    (hSecond : AdvancesBlock boundary Q code₂ e)
    (hLocal : Effect.Local e)
    (hSub : ∀ x ∈ code₂, x ∈ code)
    (hFull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hMid : ∀ s t, P s → (E s).Holds s t →
      (∀ b, Obs ((E s).after s b) t) → Q t ∧ (e t).Avoids code) :
    AdvancesBlock boundary P code (Effect.seq E e) := by
  exact Sha1.Proofs.Compress.Machine.AdvancesBlock.seq_block
    hFirst hSecond hLocal hSub hFull hMid

end Sha1.Proofs.Streaming
