import ChaCha20Poly1305.Proofs.Callee100a80.Defs
import ChaCha20Poly1305.Proofs.Callee100a80.Run.Shared
import ChaCha20Poly1305.Proofs.Callee100a80.Run.Setup
import ChaCha20Poly1305.Proofs.Callee100a80.Run.Bookkeeping
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Xor
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Tail

namespace ChaCha20Poly1305.Proofs.Callee100a80.Run

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.ChaCha20

section Composition

variable [Bindings] (boundary : ReturnBoundary)
  (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
  {s : RamState} {key : Vector UInt8 32} {counter : UInt32} {nonce : Vector UInt8 12}
  {input output : BitVec 64} {message : ByteArray}

include hb

                                                                              
theorem block_run {j : Nat} {t : RamState} (h : CallPre s key counter nonce input output message)
    (hh : Head s key counter nonce input output message j t) :
    ∃ fuel v, Advances boundary fuel t v ∧
      (if j + 1 < nblocks message.size then Head s key counter nonce input output message (j + 1) v
        else AtTail s key counter nonce input output message v) := by
  have hb' := hb_cut hb
  obtain ⟨f₁, t₁, a₁, hm⟩ := enter boundary hb h hh
  have hr₁ := hm.kept.frame.ready
  have hc₁ := hm.kept.frame.code
  obtain ⟨f₂, t₂, a₂, hr₂, hc₂, hip₂, hf₂, hw₂, -, hg₂⟩ :=
    Cuts.Rounds.mainLoop boundary hb' 9 (sp s) (words key counter nonce j) t₁ hr₁ hc₁ hm.rip
      hm.rframe hm.words hm.rounds (by decide)
  have hk₂ := kept_rounds boundary hb h hm.kept hg₂ hr₂ hc₂
  have hpre := feed_pre boundary hb h hk₂ hip₂ hf₂ hw₂
  obtain ⟨f₃, t₃, a₃, hr₃, hc₃, hpost⟩ :=
    Cuts.Xor.full_block boundary
      (by unfold Cuts.Xor.codeLo Cuts.Xor.codeHi; omega) hr₂ hc₂ hpre
  obtain ⟨f₄, v, a₄, hv⟩ := block_exit boundary hb h hk₂ hpost hr₃ hc₃
  exact ⟨f₁ + f₂ + f₃ + f₄, v, ((a₁.trans a₂).trans a₃).trans a₄, hv⟩

                                                      
theorem blocks_from (n : Nat) {j : Nat} {t : RamState}
    (h : CallPre s key counter nonce input output message)
    (hn : j + n = nblocks message.size)
    (hh : Head s key counter nonce input output message j t) :
    ∃ fuel v, Advances boundary fuel t v ∧ AtTail s key counter nonce input output message v := by
  induction n generalizing j t with
  | zero => exact absurd hh.lt (by omega)
  | succ n ih =>
    obtain ⟨f, u, a, hu⟩ := block_run boundary hb h hh
    split at hu
    · obtain ⟨g, v, a', hv⟩ := ih (j := j + 1) (by omega) hu
      exact ⟨f + g, v, a.trans a', hv⟩
    · exact ⟨f, u, a, hu⟩

                                                                                      
theorem accepted_run {t : RamState} (h : CallPre s key counter nonce input output message)
    (hacc : Accepted counter message.size) (hc : Checked s t counter output message.size) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u output message.size ∧
      u.RIP = 0x1014aa ∧ Status s u key counter nonce output message := by
  have hb' := hb_cut hb
  obtain ⟨f₁, t₁, a₁, h₁⟩ := setup boundary hb h hacc hc
  have htail : ∃ fuel v, Advances boundary fuel t₁ v ∧
      AtTail s key counter nonce input output message v := by
    split at h₁
    · exact ⟨0, t₁, (advances_zero _ _ _).mpr rfl, h₁⟩
    · exact blocks_from boundary hb (nblocks message.size) h (by omega) h₁
  obtain ⟨f₂, t₂, a₂, h₂⟩ := htail
  obtain ⟨f₃, u, a₃, hr, hcu, hg, hf⟩ :=
    Cuts.Tail.tail_run boundary hb' h₂.frame.ready h₂.frame.code h₂.cut
  obtain ⟨hfr, hst⟩ := tail_done boundary hb h hacc h₂ hg hr hcu hf
  exact ⟨f₁ + f₂ + f₃, u, (a₁.trans a₂).trans a₃, hfr, hf.rip, hst⟩

end Composition

end ChaCha20Poly1305.Proofs.Callee100a80.Run
