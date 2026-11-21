import P256.Proofs.Sec1.Decode.Prepare.Copy.First
import P256.Proofs.Sec1.Decode.Prepare.Copy.Last

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copiedWindow {α : Type} (f : Nat → α) : Nat → α := copyLastWindow (copyFirstWindow f)

theorem copiedWindow_map {α β : Type} (g : α → β) (f : Nat → α) :
    copiedWindow (fun i ↦ g (f i)) = fun i ↦ g (copiedWindow f i) := by
  have first : copyFirstWindow (fun i ↦ g (f i)) = fun i ↦ g (copyFirstWindow f i) := by
    simp only [copyFirstWindow, update_map]
  have last (v : Nat → α) : copyLastWindow (fun i ↦ g (v i)) =
      fun i ↦ g (copyLastWindow v i) := by
    simp only [copyLastWindow, update_map]
  exact (congrArg copyLastWindow first).trans (last _)

theorem copiedWindow_eq (f : Nat → UInt8) {i : Nat} (hi : i < 65) :
    copiedWindow f (156+i) = f i := by
  have index : ∀ j : Fin 65, copiedWindow (fun k ↦ k) (156+j.val) = j.val := by
    decide +kernel
  have mapped := congrFun (copiedWindow_map f (fun k ↦ k)) (156+i)
  change copiedWindow f (156+i) = f (copiedWindow (fun k ↦ k) (156+i)) at mapped
  rw [mapped, index ⟨i,hi⟩]

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {f : Nat → UInt8} (pre : DecodePre initial boundary bytes)
    (frame : Frame initial s) (window : Window s f) (rip : s.RIP = 0x10e561) :
    ∃ t fuel, Advances boundary fuel s t ∧ Frame initial t ∧ t.RIP = 0x10e622 ∧
      Window t (copiedWindow f) ∧ t.regValue .r12 = s.regValue .r12 ∧
      t.regValue .r15 = s.regValue .r15 := by
  obtain ⟨u, n, hu, fu, pu, wu, u12, u15, ax⟩ := runFirst pre frame window rip
  obtain ⟨t, m, ht, ft, pt, wt, t12, t15⟩ := runLast pre fu wu pu ax
  exact ⟨t, n+m, hu.trans ht, ft, pt, wt, t12.trans u12, t15.trans u15⟩

end P256.Proofs.Sec1.Decode.Prepare.Copy
