import P256.Proofs.Signing.Wrapper.Entry.Stages
import P256.Proofs.Signing.Wrapper.State
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t : RamState} {secret message : ByteArray}

theorem address (state : State initial s 520) {off : Nat} (bound : off ≤ 520) :
    stackPtr s + BitVec.ofNat 64 off = stackPtr initial - BitVec.ofNat 64 (520-off) := by
  rw [state.rsp]
  rw [show (520#64 : BitVec 64) = BitVec.ofNat 64 (520-off)+BitVec.ofNat 64 off by
    rw [← BitVec.ofNat_add]; congr 1; omega, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem readable (ctx : Context initial secret message) (state : State initial s 520)
    {off len : Nat} (bound : off+len ≤ 520) :
    MemReadable s (stackPtr s+BitVec.ofNat 64 off) len := by
  obtain ⟨slices,call⟩ := ctx.call
  have stack : Stack.Valid initial 5112 := call.stackAvailable.1
  rw [address state (by omega)]
  exact readable_of_grow (stack_sub_readable stack
    (offset := 520-off) (by omega) (by omega)) state.allocated

theorem writable (ctx : Context initial secret message) (state : State initial s 520)
    {off len : Nat} (bound : off+len ≤ 472) (positive : 0<len) :
    Common.Instructions.CrossPageStore.Writable s (stackPtr s+BitVec.ofNat 64 off) len := by
  obtain ⟨slices,call⟩ := ctx.call
  have stack : Stack.Valid initial 5112 := call.stackAvailable.1
  rw [address state (by omega)]
  have avoids : (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    call_stack_avoids (routine := signingKeyTrySign) call
  exact stack_buffer_writable stack avoids
    state.allocated (by omega) (by omega) positive

theorem code_apart (ctx : Context initial secret message) (state : State initial s 520)
    {off len co cl : Nat} (bound : off+len ≤ 472) (codeBound : co+cl ≤ 118431) :
    RangeApart (stackPtr s+BitVec.ofNat 64 off) len
      (Extracted.textAddress+BitVec.ofNat 64 co) cl := by
  obtain ⟨slices,call⟩ := ctx.call
  have stack : Stack.Valid initial 5112 := call.stackAvailable.1
  rw [address state (by omega)]
  have avoids : (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    call_stack_avoids (routine := signingKeyTrySign) call
  exact stack_buffer_code_apart stack avoids
    (by omega) (by omega) codeBound

theorem work (ctx : Context initial secret message) (state : State initial s 520)
    {off len : Nat} (bound : off+len ≤ 472) {a : BitVec 64}
    (cover : (Component.mem (stackPtr s+BitVec.ofNat 64 off) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  obtain ⟨slices,call⟩ := ctx.call
  have stack : Stack.Valid initial 5112 := call.stackAvailable.1
  rw [address state (by omega)] at cover
  exact work_contains stack (by omega) (by omega) cover

theorem after
    {fuel : Nat} {cs : List Component}
    (ctx : Context initial secret message) (state : State initial s 520)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (ag : AgreesExcept cs s t) (writes : WritesWithin cs #v[workRegion initial])
    (kept : ∀ r ∈ [14,3,5,4], Component.reg r ∉ cs) (df : Component.df ∉ cs) :
    State initial t 520 := by
  obtain ⟨slices,call⟩ := ctx.call
  exact state.after_effect call run ready ag writes
    ((ag.read (n := 64) (kept 4 (by simp))).trans state.rsp)
    df

end P256.Proofs.Signing.Wrapper.Entry.Construct
