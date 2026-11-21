import P256.Proofs.Program.Compare.Tail.EightPhase
import P256.Proofs.Program.Compare.Tail.FourPhase
import P256.Proofs.Program.Compare.Tail.TwoPhase
import P256.Proofs.Program.Compare.Tail.Composition

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem small_tail [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hip : s.RIP = 0x11cd30)
    (hlen : ((Operand.reg 1 : Operand 64).read s).toNat < 8)
    (hl : MemReadable s ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 1 : Operand 64).read s).toNat)
    (hright : MemReadable s ((Operand.reg 2 : Operand 64).read s)
      ((Operand.reg 1 : Operand 64).read s).toNat) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ stackPtr t = stackPtr s ∧
      t.external = s.external ∧ AgreesExcept changes s t ∧
      (t.RIP = 0x11ce9e ∨ t.RIP = 0x11ce0d) ∧
      ((Operand.reg 0 : Operand 32).read t = 0 ↔
        BytesEqual s ((Operand.reg 6 : Operand 64).read s)
          ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 1 : Operand 64).read s).toNat) := by
  let n := ((Operand.reg 1 : Operand 64).read s).toNat
  let n8 := (maskedLength s 24).toNat
  let n4 := (maskedLength s 4).toNat
  let n2 := (maskedLength s 2).toNat
  let n1 := byteLength s
  obtain ⟨hs, _, h4, h2⟩ := small_length_parts s (by omega)
  have hsum : n8 + n4 + n2 + n1 = n := hs
  have hz8 : maskedLength s 24 = 0 := by
    have hzero : ∀ i : Fin 8, (((BitVec.ofNat 64 i.val).setWidth 32) &&& 24).setWidth 64 = 0 := by decide +kernel
    simpa only [maskedLength, BitVec.ofNat_toNat, BitVec.setWidth_eq, Operand.setWidth_read_reg64] using hzero ⟨_, hlen⟩
  have hp8 : EightPhasePre s := ⟨hip, hz8, readable_prefix hl (by omega),
    readable_prefix hright (by omega)⟩
  obtain ⟨na, a, hsa, hra, hca, hfa, hoa⟩ := eight_phase boundary s hr hc hb hp8
  have hma := hfa.external (by simp [changes, Component.Covers])
  have hba := frame_boundary hfa hb
  rcases hoa with ⟨pa, halias⟩ | hfail
  · have hmore : n8 + (n4 + n2 + n1) = n := by omega
    have hreads := pa.readable (rest := n4 + n2 + n1) hma (hmore ▸ hl) (hmore ▸ hright)
    have heq8 : BytesEqual a ((Operand.reg 6 : Operand 64).read a)
        ((Operand.reg 2 : Operand 64).read a) (n4 + n2 + n1) ↔
        BytesEqual s ((Operand.reg 6 : Operand 64).read s)
          ((Operand.reg 2 : Operand 64).read s) n := by
      have he := phaseSuccess_slice (rest := n4 + n2 + n1) pa hma
      rwa [hmore] at he
    have hmask4 := maskedLength_congr pa.length 4
    have hp4 : FourPhasePre a := by
      refine ⟨pa.rip, halias, ?_, ?_, ?_⟩
      · rw [hmask4]
        exact h4
      · rw [hmask4]
        exact readable_prefix hreads.1 (by omega)
      · rw [hmask4]
        exact readable_prefix hreads.2 (by omega)
    obtain ⟨nb, b, hab, hrb, hcb, hfb, hob⟩ := four_phase boundary a hra hca hba hp4
    rw [hmask4] at hob
    have hmb := hfb.external (by simp [changes, Component.Covers])
    have hfab := frame_trans hfa hfb
    have hbb := frame_boundary hfab hb
    rcases hob with ⟨pb, hbalias⟩ | hfail
    · have hreads' := pb.readable (rest := n2 + n1) hmb
        (by simpa only [Nat.add_assoc] using hreads.1)
        (by simpa only [Nat.add_assoc] using hreads.2)
      have heq4 : BytesEqual b ((Operand.reg 6 : Operand 64).read b)
          ((Operand.reg 2 : Operand 64).read b) (n2 + n1) ↔
          BytesEqual a ((Operand.reg 6 : Operand 64).read a)
            ((Operand.reg 2 : Operand 64).read a) (n4 + n2 + n1) := by
        simpa only [Nat.add_assoc] using phaseSuccess_slice (rest := n2 + n1) pb hmb
      have hmask2 := maskedLength_congr (pb.length.trans pa.length) 2
      have hp2 : TwoPhasePre b := by
        refine ⟨pb.rip, hbalias, ?_, ?_, ?_⟩
        · rw [hmask2]
          exact h2
        · rw [hmask2]
          exact readable_prefix hreads'.1 (by omega)
        · rw [hmask2]
          exact readable_prefix hreads'.2 (by omega)
      obtain ⟨nc, c, hbc, hrc, hcc, hfc, hoc⟩ := two_phase boundary b hrb hcb hbb hp2
      rw [hmask2] at hoc
      have hmc := hfc.external (by simp [changes, Component.Covers])
      have hfabc := frame_trans hfab hfc
      have hbc' := frame_boundary hfabc hb
      rcases hoc with pc | hfail
      · have hreads'' := pc.readable (rest := n1) hmc hreads'.1 hreads'.2
        have heq2 := phaseSuccess_slice (rest := n1) pc hmc
        have hbyte := byteLength_congr (pc.length.trans (pb.length.trans pa.length))
        have hp1 : ByteTailPre c := by
          refine ⟨pc.rip, ?_, ?_⟩
          · rw [hbyte]
            exact hreads''.1
          · rw [hbyte]
            exact hreads''.2
        obtain ⟨nd, t, hct, hrt, hcode, _, hft, hipt, hret⟩ :=
          byte_tail_result boundary c hrc hcc hp1 hbc'
        have hframe : AgreesExcept changes s t :=
          frame_trans hfabc (hft.mono (by simp [byteChanges, changes]))
        rw [hbyte] at hret
        refine ⟨na + nb + nc + nd, t, ((hsa.trans hab).trans hbc).trans hct,
          hrt, hcode, hframe.read (n := 64) (by decide),
          hframe.external (by simp [changes, Component.Covers]), hframe, hipt, ?_⟩
        exact hret.trans (heq2.trans (heq4.trans heq8))
      · have hnot : ¬ BytesEqual s ((Operand.reg 6 : Operand 64).read s)
            ((Operand.reg 2 : Operand 64).read s) n := by
          intro heq
          have hh := heq4.mpr (heq8.mpr heq)
          exact hfail.2.2 (fun i hi ↦ hh i (by omega))
        exact ⟨na + nb + nc, c, (hsa.trans hab).trans hbc, hrc, hcc,
          hfabc.read (n := 64) (by decide),
          hfabc.external (by simp [changes, Component.Covers]), hfabc,
          Or.inl hfail.1, iff_of_false hfail.2.1 hnot⟩
    · have hnot : ¬ BytesEqual s ((Operand.reg 6 : Operand 64).read s)
          ((Operand.reg 2 : Operand 64).read s) n := by
        intro heq
        have hh := heq8.mpr heq
        exact hfail.2.2 (fun i hi ↦ hh i (by omega))
      exact ⟨na + nb, b, hsa.trans hab, hrb, hcb,
        hfab.read (n := 64) (by decide),
        hfab.external (by simp [changes, Component.Covers]), hfab,
        Or.inl hfail.1, iff_of_false hfail.2.1 hnot⟩
  · have hnot : ¬ BytesEqual s ((Operand.reg 6 : Operand 64).read s)
        ((Operand.reg 2 : Operand 64).read s) n := by
      intro heq
      exact hfail.2.2 (fun i hi ↦ heq i (by omega))
    exact ⟨na, a, hsa, hra, hca, hfa.read (n := 64) (by decide), hma, hfa,
      Or.inl hfail.1, iff_of_false hfail.2.1 hnot⟩

end P256.Proofs.Program.Compare.Tail
