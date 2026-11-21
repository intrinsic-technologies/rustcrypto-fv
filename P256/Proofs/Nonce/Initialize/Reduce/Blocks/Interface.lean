import P256.Proofs.Nonce.Initialize.Prepare.Memory
import P256.Proofs.Nonce.Initialize.Reduce.Arithmetic
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.Field.Operations.Neg.SubLoad
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.Instructions.Sar.Triple
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure BlockPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ offset : Nat, offset + 8 ≤ 232 → offset % 8 = 0 →
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8
  avoids : ∀ offset len, offset + len ≤ 232 → ∀ a,
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a → ¬ InProgram a

theorem BlockPre.apart {s : RamState} {p : BitVec 64} (h : BlockPre p s)
    (offset len : Nat) (hs : offset + len ≤ 232)
    (codeOffset codeLen : Nat) (hc : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply h.avoids offset len hs _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset+j) (by omega)

theorem block_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress p : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = p) : BlockPre p s := by
  refine ⟨rip, fun offset bound aligned => Prepare.stack_writable8 pre stage (by omega) aligned, ?_⟩
  intro offset len bound a covered
  intro ha
  rw [HMAC.Finalize.stack_address (depth := 280) stage.rsp (by omega)] at covered
  exact pre.avoids _ (by simp) a (ScalarFrame.stack_contains pre.toCalleePre
    (by omega) (by omega) covered) (.inl ha)

theorem local_covers {s : RamState} {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ 232)
    (cover : (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem (stackPtr s) 232).Covers a := by
  obtain ⟨i, hi, rfl⟩ := cover
  exact ⟨offset + i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]⟩

theorem Stage.of_local [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {fuel : Nat} {cs : List Component}
    (pre : InitializePre initial boundary orderAddress) (stage : Stage initial s boundary)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (localWrites : ∀ c ∈ cs, ∀ a, c.Covers a → (Component.mem (stackPtr s) 232).Covers a)
    (rsp : .reg 4 ∉ cs) (df : .df ∉ cs) (mx : .mxcsr ∉ cs) (fc : .fcw ∉ cs) :
    Stage initial t boundary := by
  obtain ⟨n, hn⟩ := stage.execution
  refine ⟨stage.toFrameState.after_effect pre.toCalleePre (by decide) ready agrees ?_ rsp df mx fc,
    n + fuel, hn.trans run⟩
  intro c hc a ha
  have h := localWrites c hc a ha
  rw [stage.rsp] at h
  exact ⟨ScalarFrame.workRegion initial 2144, by simp,
    ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) h⟩

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
