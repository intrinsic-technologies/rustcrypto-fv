import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.First
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Second
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.State

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Absorb.ShortSlices

theorem Absorb.appendReduced {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool)
    (env : Environment fr (.seeded secret reduced))
    (live : Live (Absorb.loopAt second) fr a m state) (slots : Slots fr m)
    (cursor : Absorb.Cursor second fr a 16)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key (Absorb.taggedValue second state ++ secret)) :
    ∃ b n, Verify.Core.Reaches (Absorb.loopAt second) a m (digestAt second (.seeded secret reduced)) b n ∧
      Live (digestAt second (.seeded secret reduced)) fr b n state ∧ Slots fr n ∧
      UpdateV.HmacStateAt n (context fr second) state.key (message second (.seeded secret reduced) state) := by
  have run : Runs second := by cases second <;> first | exact runFirst | exact runSecond
  have sv : state.value.size = 32 := live.bytes.value.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, s, r⟩ := env.slices
  have ss : secret.size = 32 := s.1
  have sr : reduced.size = 32 := r.1
  let input := Absorb.taggedValue second state ++ secret
  have sz : input.size = 65 := by
    simp only [input, Absorb.taggedValue, ByteArray.size_append, sv, ss]
    rfl
  have mod₁ : input.size % 64 = used false := by rw [sz]; rfl
  obtain ⟨b, path, cursor', regs, r14, widths⟩ := run false env live slots cursor
    (ctx.used.trans (congrArg (BitVec.ofNat 8) mod₁))
  obtain ⟨live', slots', ctx'⟩ := afterIteration second false env live slots ctx mod₁ regs r14 widths
  have mod₂ : (input ++ reduced).size % 64 = used true := by rw [ByteArray.size_append, sz, sr]; rfl
  obtain ⟨c, path', _, regs', r14', widths'⟩ := run true env live' slots' cursor'
    (ctx'.used.trans (congrArg (BitVec.ofNat 8) mod₂))
  obtain ⟨live'', slots'', ctx''⟩ := afterIteration second true env live' slots' ctx' mod₂ regs' r14' widths'
  have label : target second true = digestAt second (.seeded secret reduced) := by cases second <;> rfl
  refine ⟨c, _, label ▸ path.trans path', label ▸ live'', slots'', ?_⟩
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true, ByteArray.append_empty, input, Absorb.taggedValue,
    ByteArray.append_assoc, message, seed] using ctx''

end K256.Proofs.Signing.Nonce.Initialize.Update
