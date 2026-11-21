import P256.Proofs.Common.EffectCompose
import P256.Proofs.Sec1Serialize.Tail.Prepare.Effect
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Tag
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.Swap
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.Copy
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.StoreX
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.StoreY
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Prepare

open X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] prepareSwapEffect prepareCopyEffect prepareStoreXEffect
  prepareStoreYEffect prepareTagEffect prepareBranchEffect prepareEncodingEffect

@[x86_compose] theorem prepare_mem_beq_reg (a : BitVec 64) (n : Nat) (r : BitVec 5) :
    ((Component.mem a n) == Component.reg r) = false := rfl

@[x86_compose] theorem prepare_mem_beq_xmm (a : BitVec 64) (n : Nat) (r : BitVec 5) :
    ((Component.mem a n) == Component.xmm r) = false := rfl

macro "prepare_effect_local" e:Lean.Parser.Tactic.simpLemma : tactic => `(tactic| (
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro t t' h
    simp [$e, rspOf, h.read_reg, h.read_mem, h.read_xmm, h.read_gpr8, h.read_byteReg, h.gpr]
  · intro t
    simp [$e, Write.Full, Operand.Full]))

theorem prepareSwapEffect_local : Effect.Local prepareSwapEffect := by
  prepare_effect_local prepareSwapEffect

theorem prepareCopyEffect_local : Effect.Local prepareCopyEffect := by
  prepare_effect_local prepareCopyEffect

theorem prepareStoreXEffect_local : Effect.Local prepareStoreXEffect := by
  prepare_effect_local prepareStoreXEffect

theorem prepareStoreYEffect_local : Effect.Local prepareStoreYEffect := by
  prepare_effect_local prepareStoreYEffect

theorem prepareTagEffect_local : Effect.Local prepareTagEffect := by
  prepare_effect_local prepareTagEffect

theorem prepareBranchEffect_local : Effect.Local prepareBranchEffect := by
  prepare_effect_local prepareBranchEffect

theorem prepare_branch_holds {s t : RamState}
    (rip : t.RIP = 0x111047) (ha : AgreesExcept [.flags, .rip] s t) :
    (prepareBranchEffect s).Holds s t :=
  ⟨rip, trivial, ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, ha⟩

set_option maxHeartbeats 2400000 in
theorem prepare_compose {s a b c d e t : RamState}
    (swap : (prepareSwapEffect s).Holds s a)
    (branch : (prepareBranchEffect a).Holds a b)
    (copy : (prepareCopyEffect b).Holds b c)
    (storex : (prepareStoreXEffect c).Holds c d)
    (tag : (prepareTagEffect d).Holds d e)
    (storey : (prepareStoreYEffect e).Holds e t) :
    (prepareEncodingEffect s).Holds s t := by
  have l1 := prepareSwapEffect_local.seq prepareBranchEffect_local
  have l2 := l1.seq prepareCopyEffect_local
  have l3 := l2.seq prepareStoreXEffect_local
  have l4 := l3.seq prepareTagEffect_local
  have h1 := Effect.Holds.seq (e₁ := prepareSwapEffect) (e₂ := prepareBranchEffect)
    prepareBranchEffect_local (prepareSwapEffect_local.full s) swap branch
  have h2 := Effect.Holds.seq
    (e₁ := Effect.seq prepareSwapEffect prepareBranchEffect) (e₂ := prepareCopyEffect)
    prepareCopyEffect_local (l1.full s) h1 copy
  have h3 := Effect.Holds.seq
    (e₁ := Effect.seq (Effect.seq prepareSwapEffect prepareBranchEffect) prepareCopyEffect)
    (e₂ := prepareStoreXEffect) prepareStoreXEffect_local (l2.full s) h2 storex
  have h4 := Effect.Holds.seq
    (e₁ := Effect.seq (Effect.seq (Effect.seq prepareSwapEffect prepareBranchEffect)
      prepareCopyEffect) prepareStoreXEffect) (e₂ := prepareTagEffect)
    prepareTagEffect_local (l3.full s) h3 tag
  have h5 := Effect.Holds.seq
    (e₁ := Effect.seq (Effect.seq (Effect.seq (Effect.seq prepareSwapEffect prepareBranchEffect)
      prepareCopyEffect) prepareStoreXEffect) prepareTagEffect) (e₂ := prepareStoreYEffect)
    prepareStoreYEffect_local (l4.full s) h4 storey
  x86_norm [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at h5
  apply h5.weaken
  · x86_norm
  · x86_norm
  · intro i
    cases i <;> x86_norm
  · x86_norm

end P256.Proofs.Sec1Serialize.Prepare
