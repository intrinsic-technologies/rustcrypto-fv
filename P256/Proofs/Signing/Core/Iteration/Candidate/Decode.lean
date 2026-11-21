import P256.Proofs.Signing.Core.Iteration.Candidate.Copy
import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Generate.Scalar.Correct
import P256.Proofs.SignatureFromDer.Model
import P256.Proofs.Program.CopyBytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open NextNonce (arguments_copy)

structure Decoded [Bindings] (s t : RamState) (state : Nonce.State) (nonce : Nat) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  scalar : Nat256At t (frameBase s + 528) nonce
  flag : t.external[frameBase s + 560]? = some 1
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  rbp : t.regValue .rbp = frameBase s + 528
  rbx : t.regValue .rbx = frameBase s + 40
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328

theorem decode [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce : Nat} (pre : SignPre s boundary)
    (input : Core.Candidate s t state nonce) (rip : t.RIP = 0x10cad9) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cb11 ∧ Decoded s u state nonce := by
  obtain ⟨n, a, runA, frameA, effectA⟩ := Copy.run pre input.frame rip
  have siA : a.regValue .rsi = frameBase s + 104 :=
    effectA.writes.2.2.2.1.trans (congrArg (· + 104) input.frame.rsp)
  have diA : a.regValue .rdi = frameBase s + 528 := effectA.writes.2.2.1.trans input.rbp
  obtain ⟨v, runV, readyV, effectV⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frameA) 0xcb0c 0x63bf
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x12ed0 (by decide)) effectA.rip
  have effect : (callEffect (fun _ => 0x112ed0) 0x10cb11 a).Holds a v := effectV
  have cp := local_call_pre pre frameA readyV effect
    (inputBytes := 32) (outputBytes := 33) (reserve := 72)
    (inProgram_of_textOffset 0xcb11 (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inl (by decide)) siA diA
  have siV : v.regValue .rsi = frameBase s + 104 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans siA
  have diV : v.regValue .rdi = frameBase s + 528 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans diA
  have bytesV : (registerRegion v .rsi 32).HasBytes v.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 nonce) := by
    change (MemoryRegion.mk (v.regValue .rsi).toNat 32).HasBytes _ _
    rw [siV]
    apply hasBytes_copy input.bytes
    intro i hi
    exact (local_call_copy frameA effect (offset := 104) (len := 32) (by decide) i hi).trans
      (Copy.copied pre input.frame frameA effectA i hi)
  obtain ⟨u, result, value, flag, _⟩ := Generate.Scalar.from_repr_correct cp bytesV
  have decoded : Arith.uint (Standards.SECG.ECC.Encoding.natToOctets 32 nonce) = nonce := by
    change Standards.SECG.ECC.Encoding.octetsToNat _ = nonce
    rw [SignatureFromDer.octetsToNat_natToOctets, Nat.mod_eq_of_lt]
    have hn : Operations.domain.n < 256^32 := by decide +kernel
    exact Nat.lt_trans input.canonical hn
  have frameU := after_call pre frameA readyV effect result (by decide) (by decide) diA
  have preserve (offset len : Nat) (bound : offset + len ≤ 2280)
      (copyApart : offset + len ≤ 104 ∨ 136 ≤ offset)
      (resultApart : offset + len ≤ 528 ∨ 561 ≤ offset) :
      ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    refine (local_result_copy pre frameA effect result diA bound (by decide) resultApart i hi).trans ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply word_writes_byte (Copy.writes input.frame) effectA.agrees (by omega)
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    constructor <;> omega
  have args := arguments_copy input.arguments (fun offset range => by
    obtain ⟨lo, hi⟩ := range
    have h := preserve offset 1 (by omega) (.inl (by omega)) (.inl (by omega)) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h)
  have generator := input.generator.copy
    (preserve 2160 72 (by decide) (.inr (by decide)) (.inr (by decide)))
    ⟨input.generator.2.1.1, fun i hi =>
      (preserve 272 32 (by decide) (.inr (by decide)) (.inl (by decide)) i hi).trans
        (input.generator.2.1.2 i hi)⟩
  have registers (reg : Syntax.Reg) (member : reg ∈ [.rbp, .rbx, .r13, .r14, .r15]) :
      u.regValue reg = t.regValue reg := by
    refine (result.calleeSaved reg (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp)).trans ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact (effect.agrees.read (n := 64) (r := 5) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 5) (by simp [Copy.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 3) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 3) (by simp [Copy.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 13) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 13) (by simp [Copy.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 14) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 14) (by simp [Copy.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 15) (by simp [Copy.Block.effect, Effect.components]))
  obtain ⟨m, runU⟩ := result.execution
  refine ⟨n+1+m, u, (runA.trans runV).trans runU,
    result.rip.trans (callEffect_stack effect).1,
    ⟨frameU, args, generator, ?_, ?_, input.positive, input.canonical,
      (registers .rbp (by simp)).trans input.rbp,
      (registers .rbx (by simp)).trans input.rbx,
      (registers .r13 (by simp)).trans input.r13,
      (registers .r14 (by simp)).trans input.r14,
      (registers .r15 (by simp)).trans input.r15⟩⟩
  · simpa only [diV, decoded] using value
  · simpa only [diV, decoded, ite_eq_left input.canonical, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using flag

end P256.Proofs.Signing.Core.Iteration.Candidate
