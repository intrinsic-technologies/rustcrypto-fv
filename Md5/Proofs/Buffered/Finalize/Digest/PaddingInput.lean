import Md5.Proofs.Buffered.Finalize.Digest.Prepare
import Md5.Proofs.Buffered.Finalize.Digest.Prefix
import Md5.Proofs.Buffered.Finalize.Digest.Padding.Contracts

namespace Md5.Proofs.Buffered.Finalize.Digest

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_padding [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .digest boundary message s) :
    ∃ fuel t, Advances boundary fuel s t ∧ Padding.Input boundary message t ∧
      AgreesExcept (Kind.digest.changes s) s t := by
  obtain ⟨u, hu⟩ := prepare hp
  obtain ⟨fuel, t, ht, hr, hc, he⟩ := Prefix.run hu.ready hu.code hp.boundaryOutside hu.rip
  have hsp : stackPtr t = stackPtr u := he.agrees.read (n := 64) (r := 4) (by
    simp [Prefix.effect, Effect.components])
  have h12 : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) := by
    rw [he.agrees.read (n := 64) (r := 12) (by simp [Prefix.effect, Effect.components])]
    exact hu.position
  have h15 : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) := by
    rw [he.agrees.read (n := 64) (r := 15) (by simp [Prefix.effect, Effect.components])]
    exact hu.blocks
  have h14 : (Operand.reg 14 : Operand 64).read t =
      BitVec.ofNat 64 (63 - message.size % 64) := by
    change (Operand.reg 14 : Operand 64).read t = _
    rw [he.writes, hu.position]
    exact FinalizeReset.remainingBytes _ (by omega)
  have hem : t.external = u.external := he.agrees.external (by
    simp [Prefix.effect, Effect.components, Component.Covers])
  have hag : AgreesExcept (Kind.digest.changes s) s t := by
    have ha : AgreesExcept (Kind.digest.changes s) u t := he.agrees.mono (by
      intro c hm
      simp only [Prefix.effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      all_goals simp [Kind.changes, Kind.workRegisters])
    exact (hu.agrees.trans ha).mono (by simp)
  have hin : Padding.Input boundary message t := by
    refine ⟨⟨hu.storage.of_agrees he.agrees hsp, he.rip, ?_⟩, hr, hc,
      hp.boundaryOutside,
      (he.agrees.directionFlagClear (by simp [Prefix.effect, Effect.components]) ⟨hu.df⟩).df,
      h12, h14, h15, ?_, ?_⟩
    · rw [h12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hsp, hem]
      exact hu.tail
    · rw [hsp, hem]
      exact hu.buffer
  obtain ⟨n, ha⟩ := hu.advances
  exact ⟨n + fuel, t, ha.trans ht, hin, hag⟩

end Md5.Proofs.Buffered.Finalize.Digest
