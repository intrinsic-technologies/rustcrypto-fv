import P256.Proofs.Verifying.Core.Products.Entry
import P256.Proofs.Field.Montgomery.Wrapper.Schoolbook

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Products

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field.Montgomery.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem right_of_frame {b : Nat} (pre : MultiplyPre s boundary)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 280])
    (hb : Nat256At s (s.regValue .rdx) b) : Nat256At t (s.regValue .rdx) b := by
  refine ⟨hb.1, fun i hi => Eq.trans (frame _ ?_) (hb.2 i hi)⟩
  intro region hr hin
  have hright := memoryRegion_contains_add pre.rightBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : region = registerRegion s .rdi 32 ∨ region = Stack.region s 280 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.rightOutput _ hright hin
  · exact pre.rightStack _ hright hin

theorem schoolbook_stage {a b : Nat} (pre : MultiplyPre s boundary)
    (ha : Nat256At s (s.regValue .rsi) a) (hb : Nat256At s (s.regValue .rdx) b) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t ∧ t.RIP = 0x113343 ∧
      Bytes t.external (scratch s + 64) 64 (fun i => UInt8.ofNat ((a*b) / 256^i % 256)) := by
  obtain ⟨entered, entry⟩ := schoolbook_entry_correct pre
  have state := entered_state pre.toCalleePre entry
  have left : Nat256At entered (entered.regValue .rsi) a := by
    rw [entry.left]
    exact input_of_frame pre.toCalleePre state.frame ha
  have right : Nat256At entered (entered.regValue .rcx) b := by
    rw [entry.right]
    exact right_of_frame pre state.frame hb
  exact schoolbook_of_entry pre.toCalleePre entry left right

end P256.Proofs.Verifying.Core.Products
