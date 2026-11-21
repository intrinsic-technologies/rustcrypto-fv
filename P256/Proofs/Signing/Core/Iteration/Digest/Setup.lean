import P256.Proofs.Signing.Core.Iteration.Digest.State
import P256.Proofs.Signing.Core.Iteration.Digest.Prefix

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SecretKeyFromBytes.Scalar

structure Reading [Bindings] (s t : RamState) (state : Nonce.State) (nonce : Nat) : Prop extends
    NonceState s t state nonce where
  source : t.regValue .rdi = s.regValue .rdx
  count : t.regValue .rsi = 32
  destination : t.regValue .rdx = frameBase s + 1328
  limbs : t.regValue .rcx = 4
  bits : t.regValue .r8 = 256

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce : Nat} (pre : SignPre s boundary)
    (input : Candidate.Validated s t state nonce) (rip : t.RIP = 0x10cbed) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cc94 ∧ Reading s u state nonce := by
  obtain ⟨fuel,u,run,frame,effect⟩ := Prefix.run pre input.frame rip
  have memory (i : Nat) (live : (72 ≤ i ∧ i < 104) ∨ (272 ≤ i ∧ i < 304) ∨ (2160 ≤ i ∧ i < 2232)) :
      u.external[frameBase s + BitVec.ofNat 64 i]? = t.external[frameBase s + BitVec.ofNat 64 i]? := by
    apply word_writes_byte (Prefix.writes input.frame) effect.agrees (by omega)
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    constructor <;> omega
  have bytes (offset len : Nat) (lo : 272 ≤ offset) (hi : offset+len ≤ 304 ∨ (2160 ≤ offset ∧ offset+len ≤ 2232)) :
      ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hin
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memory _ (by omega)
  have args := NextNonce.arguments_copy input.arguments (fun i range => memory i (by omega))
  have gen := input.generator.copy (bytes 2160 72 (by decide) (.inr ⟨by decide,by decide⟩))
    ⟨input.generator.2.1.1,fun i hi =>
      (bytes 272 32 (by decide) (.inl (by decide)) i hi).trans (input.generator.2.1.2 i hi)⟩
  have scalar : Nat256At u (frameBase s+304) nonce :=
    ⟨input.scalar.1,fun i hi => (Prefix.copied pre input.frame frame effect i hi).trans (input.scalar.2 i hi)⟩
  have registers (reg : Syntax.Reg) (member : reg ∈ [.rbp,.r13,.r14,.r15]) :
      u.regValue reg = t.regValue reg := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact effect.agrees.read (n := 64) (r := 5) (by simp [Prefix.Block.effect,Effect.components])

    · exact effect.agrees.read (n := 64) (r := 13) (by simp [Prefix.Block.effect,Effect.components])
    · exact effect.agrees.read (n := 64) (r := 14) (by simp [Prefix.Block.effect,Effect.components])
    · exact effect.agrees.read (n := 64) (r := 15) (by simp [Prefix.Block.effect,Effect.components])
  have words := effect.writes
  rcases words with ⟨_,hc,hs,hn,hd,hb,_,_,_,_,_,_,_,_,_,_⟩
  have sp : rspOf t = frameBase s := input.frame.rsp
  change u.regValue .rdi = (Operand.mem (rspOf t+88) : Operand 64).read t at hs
  change u.regValue .rsi = (Operand.mem (rspOf t+96) : Operand 64).read t at hn
  rw [sp] at hs hn
  refine ⟨fuel,u,run,effect.rip,⟨⟨frame,args,gen,scalar,input.positive,input.canonical,
    (registers .rbp (by simp)).trans input.rbp,
    (registers .r13 (by simp)).trans input.r13,(registers .r14 (by simp)).trans input.r14,
    (registers .r15 (by simp)).trans input.r15⟩,
    hs.trans input.arguments.digest,hn.trans input.arguments.length,hd.trans input.r15,hc,hb⟩⟩

end P256.Proofs.Signing.Core.Iteration.Digest
