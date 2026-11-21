import Sha2.Proofs.Common.SHA256.Instances.Absorb.Compose
import Sha2.Proofs.Common.EffectCompose

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem branch_localOn (p : BitVec 64) (len : Nat) (cc : BitVec 4) (off : BitVec 64)
    (supported : cc = 2 ∨ cc = 4 ∨ cc = 5) :
    Common.EffectCompose.Effect.LocalOn (if cc = 2 then [.CF] else [.ZF])
      (jccEffect p len cc off) := by
  apply Common.EffectCompose.Effect.LocalOn.of_eq
  · intro s t _ flags
    have flag := flags (if cc = 2 then .CF else .ZF) (by split <;> simp)
    rcases supported with rfl | rfl | rfl <;>
      simp_all [jccEffect, condHolds, StatusFlags.get]
  · intro s
    simp [jccEffect, branchEffect]

def nextEffect (site : Site) (E : RamState → Effect) (s : RamState) : Effect :=
  if (E s).rip = site.pc then Effect.seq E (effect site.pc site.block) s else E s

def foldEffect : List Site → (RamState → Effect) → RamState → Effect
  | [], E => E
  | site :: rest, E => foldEffect rest (nextEffect site E)

def Composable (P : RamState → Prop) : List Site → (RamState → Effect) → Prop
  | [], _ => True
  | site :: rest, E =>
      (∀ s u v, P s → (E s).Holds s u → (E s).rip = site.pc →
        (effect site.pc site.block u).Holds u v →
        (Effect.seq E (effect site.pc site.block) s).Holds s v) ∧
      Composable P rest (nextEffect site E)

theorem SiteTrace.fold {P : RamState → Prop} {sites : List Site} {E : RamState → Effect}
    (compose : Composable P sites E) {s u t : RamState} (pre : P s)
    (before : (E s).Holds s u) (trace : SiteTrace sites u t) :
    (foldEffect sites E s).Holds s t := by
  induction sites generalizing E u with
  | nil =>
    change t = u at trace
    subst t
    exact before
  | cons site rest ih =>
    change (∀ s u v, P s → (E s).Holds s u → (E s).rip = site.pc →
      (effect site.pc site.block u).Holds u v →
      (Effect.seq E (effect site.pc site.block) s).Holds s v) ∧
      Composable P rest (nextEffect site E) at compose
    by_cases atSite : (E s).rip = site.pc
    · have hip : u.RIP = site.pc := before.rip.trans atSite
      simp only [SiteTrace, hip, ite_true] at trace
      obtain ⟨v, step, trace⟩ := trace
      apply ih compose.2 (u := v) _ trace
      simpa only [nextEffect, atSite, ite_true] using compose.1 s u v pre before atSite step
    · have hip : u.RIP ≠ site.pc := fun h => atSite (before.rip.symm.trans h)
      simp only [SiteTrace, hip, ite_false] at trace
      apply ih compose.2 (u := u) _ trace
      simpa only [nextEffect, atSite, ite_false] using before

theorem SiteTrace.normalized {P : RamState → Prop} {sites : List Site}
    (compose : Composable P sites Effect.start) {s t : RamState} (pre : P s)
    (trace : SiteTrace sites s t) : (foldEffect sites Effect.start s).Holds s t :=
  trace.fold compose pre (Effect.start_holds s)

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
