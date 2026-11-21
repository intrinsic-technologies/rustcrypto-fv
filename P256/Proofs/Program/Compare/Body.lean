import P256.Proofs.Program.Compare.Finish

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program.Compare.Ranges (memReadable_slice rangeApart_slice_right)

structure TailReady [Bindings] (initial s : RamState) : Prop extends BodyState initial s where
  rip : s.RIP = 0x11c8c9
  small : mainLength s < 8
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) (mainLength s)
  right : MemReadable s ((Operand.reg 2 : Operand 64).read s) (mainLength s)
  stackLeft : RangeApart (stackPtr initial - 64) 64
    ((Operand.reg 6 : Operand 64).read s) (mainLength s)
  stackRight : RangeApart (stackPtr initial - 64) 64
    ((Operand.reg 2 : Operand 64).read s) (mainLength s)
  equal_iff : BytesEqual s ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s) (mainLength s) ↔
    BytesEqual initial ((Operand.reg 7 : Operand 64).read initial)
      ((Operand.reg 6 : Operand 64).read initial) ((Operand.reg 2 : Operand 64).read initial).toNat

theorem prepare_tail [Bindings] {boundary : ReturnBoundary} {initial p s : RamState}
    (hp : CallPre initial) (hb : RegisterBoundary boundary s)
    (he : (Frame.prologueEffect initial).Holds initial p)
    (hs : BodyState initial s) (hf : AgreesExcept prefixChanges p s) (hprefix : PrefixEqual p s) :
    ∃ fuel t, Advances boundary fuel s t ∧ TailReady initial t := by
  obtain ⟨n, t, ha, hr, hc, het, _⟩ :=
    tail_prepare_program boundary s hs.ready hs.code hprefix.rip hb
  have hbody : BodyState initial t := hs.of_registers hr hc
    (het.agrees.mono (by simp [tailPrepareEffect, Effect.components, bodyChanges]))
  have hpt : AgreesExcept bodyChanges p t := (hf.trans het.agrees).mono
    (by simp [prefixChanges, tailPrepareEffect, Effect.components, bodyChanges])
  have hext : t.external = p.external := hpt.external (by simp [bodyChanges, Component.Covers])
  have h6s := het.agrees.read (n := 64) (r := 6)
    (by simp [tailPrepareEffect, Effect.components])
  have h2s := het.agrees.read (n := 64) (r := 2)
    (by simp [tailPrepareEffect, Effect.components])
  have h6t : (Operand.reg 6 : Operand 64).read t =
      (Operand.reg 6 : Operand 64).read p + BitVec.ofNat 64 (prefixLength p) := h6s.trans hprefix.left
  have h2t : (Operand.reg 2 : Operand 64).read t =
      (Operand.reg 2 : Operand 64).read p + BitVec.ofNat 64 (prefixLength p) := h2s.trans hprefix.right
  have hlen : mainLength s = mainLength p :=
    congrArg BitVec.toNat (hf.read (n := 64) (r := 1) (by decide))
  have hlent : mainLength t = mainLength p % 16 := (tail_prepare_length het).trans (congrArg (· % 16) hlen)
  obtain ⟨_, _, _, _, _, _, _, h1p, h2p, h6p, _⟩ := he.writes
  have hlenp : mainLength p = ((Operand.reg 2 : Operand 64).read initial).toNat :=
    congrArg BitVec.toNat h1p
  have hsplit : prefixLength p + mainLength p % 16 = mainLength p := by unfold prefixLength; omega
  have hpp := prefix_pre_of_prologue hp he
  refine ⟨n, t, ha, ⟨hbody, het.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hlent]
    rw [hlenp]
    exact hp.smallTail
  · rw [h6t, hlent]
    exact (memReadable_slice hpp.left (prefixLength p) (mainLength p % 16) (by omega)).of_external_eq hext
  · rw [h2t, hlent]
    exact (memReadable_slice hpp.right (prefixLength p) (mainLength p % 16) (by omega)).of_external_eq hext
  · rw [h6t, h6p, hlent]
    exact rangeApart_slice_right hp.stackLeft (prefixLength p) (mainLength p % 16)
      (by rw [← hlenp]; omega)
  · rw [h2t, h2p, hlent]
    exact rangeApart_slice_right hp.stackRight (prefixLength p) (mainLength p % 16)
      (by rw [← hlenp]; omega)
  · have hfull := prologue_equal_iff hp he
    have htail : BytesEqual p ((Operand.reg 6 : Operand 64).read p)
          ((Operand.reg 2 : Operand 64).read p) (mainLength p) ↔
        BytesEqual p ((Operand.reg 6 : Operand 64).read p + BitVec.ofNat 64 (prefixLength p))
          ((Operand.reg 2 : Operand 64).read p + BitVec.ofNat 64 (prefixLength p)) (mainLength p % 16) := by
      have happ := bytesEqual_append (s := p)
        (left := (Operand.reg 6 : Operand 64).read p)
        (right := (Operand.reg 2 : Operand 64).read p)
        (first := prefixLength p) (rest := mainLength p % 16)
      rw [hsplit] at happ
      exact happ.trans (by simp only [hprefix.equal, true_and])
    rw [h6t, h2t, hlent]
    simpa only [BytesEqual, hext] using htail.symm.trans hfull

theorem prepare_body [Bindings] (boundary : ReturnBoundary) (initial : RamState)
    (hp : CallPre initial) (hb : CallBoundary boundary initial) :
    ∃ fuel t, Advances boundary fuel initial t ∧ (BodyResult initial t ∨ TailReady initial t) := by
  obtain ⟨n, p, hap, hrp, hcp, hep⟩ := Frame.prologue boundary hp
    (fun ip hl hh he ↦ hb.1 (he ▸ inRoutine_inProgram ⟨hl, by omega⟩))
  have hpbody := BodyState.of_prologue hrp hcp hep
  obtain ⟨m, s, has, hrs, hcs, hfs, hout⟩ :=
    scan_prefix boundary p hrp hcp hb.register (prefix_pre_of_prologue hp hep)
  have hsbody := hpbody.of_registers hrs hcs
    (hfs.mono (by simp [prefixChanges, bodyChanges]))
  rcases hout with heq | ⟨hip, hne, hregs⟩
  · obtain ⟨k, t, hat, ht⟩ := prepare_tail hp hb.register hep hsbody hfs heq
    exact ⟨n + m + k, t, (hap.trans has).trans hat, Or.inr ht⟩
  · have hinput := fun he ↦ hne ((prologue_equal_iff hp hep).mpr he)
    obtain ⟨k, t, hat, ht⟩ := body_mismatch hsbody hb.register hip hregs hinput
    exact ⟨n + m + k, t, (hap.trans has).trans hat, Or.inl ht⟩

end P256.Proofs.Program.Compare
