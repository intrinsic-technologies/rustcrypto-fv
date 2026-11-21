import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.LoopStep
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.LoopFrame

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

theorem loop {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (outer : Bool) (env : Environment fr input)
    (live : Live (head second outer) fr a m state) (slots : second = true → Slots fr m)
    (idx : a[0] = ⟨64, 3⟩)
    (bytes : (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes m
      (UpdateV.keyPad state.key (if outer then 0x36 else 0)))
    (hash : outer = true → Compressed fr second m state.key) :
    ∃ b n, Verify.Core.Reaches (head second outer) a m (exitLabel second outer) b n ∧
      Live (exitLabel second outer) fr b n state ∧ (second = true → Slots fr n) ∧ b[13] = a[13] ∧
      (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes n
        (UpdateV.keyPad state.key (if outer then 0x5c else 0x36)) ∧
      (outer = true → Compressed fr second n state.key) := by
  have rsp : a[4] = ⟨64, sp fr⟩ := by
    have atoms := live.atoms
    cases second <;> cases outer <;> exact atoms.1
  have addr : padOrigin (sp fr) second + 8 = pad fr second := by
    cases second <;> simp only [padOrigin, pad, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc,
      BitVec.reduceAdd] <;> rfl
  let keep (i : Fin Reg.count) := i.val ≠ 0 ∧ i.val ≠ 19
  obtain ⟨b, n, reach, frame, preserved, final⟩ := UpdateV.runPadLoop outer (head second outer)
    (exitLabel second outer) keep (by decide) (sp := padOrigin (sp fr) second) (key := state.key) rsp idx
    (by rw [addr]; exact padWritable env second live.writes)
    (by rw [addr]; exact bytes) (fun hj stack counter wr => by
      obtain ⟨b, r, idx', untouched⟩ := padStep second outer hj stack counter wr
      exact ⟨b, r, idx', fun i h => untouched i h.1 h.2⟩)
  rw [addr] at frame final
  obtain ⟨after, saved, compressed⟩ := loopPost env second outer live slots hash frame
    (fun i h₀ h₁₉ => preserved i ⟨h₀,h₁₉⟩)
  exact ⟨b, n, reach, after, saved, preserved 13 (by decide), final, compressed⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
