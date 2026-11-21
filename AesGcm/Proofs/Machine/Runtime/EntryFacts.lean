import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

structure EntryFacts (m : FrameInfo) (fr : Activation) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) : Prop where
  rsp : args[4] = ⟨64, fr.rsp⟩
  df : args[22] = ⟨1, 0⟩
  rcx : args[1] = ⟨64, fr.rcx⟩
  rdx : args[2] = ⟨64, fr.rdx⟩
  rbx : args[3] = ⟨64, fr.rbx⟩
  rbp : args[5] = ⟨64, fr.rbp⟩
  rsi : args[6] = ⟨64, fr.rsi⟩
  rdi : args[7] = ⟨64, fr.rdi⟩
  r8 : args[8] = ⟨64, fr.r8⟩
  r9 : args[9] = ⟨64, fr.r9⟩
  r12 : args[12] = ⟨64, fr.r12⟩
  r13 : args[13] = ⟨64, fr.r13⟩
  r14 : args[14] = ⟨64, fr.r14⟩
  r15 : args[15] = ⟨64, fr.r15⟩
  mxcsr : args[39] = ⟨32, fr.mxcsr⟩
  ftw : args[50] = ⟨16, fr.ftw⟩
  fcw : args[51] = ⟨16, fr.fcw⟩
  slot : Readable mem fr.rsp 8
  ret : memLoad mem fr.rsp 64 = fr.ret
  retLow : fr.ret.toNat < 2 ^ 32
  window : 0 < m.window → Writable code mem (fr.rsp - BitVec.ofNat 64 m.window) m.window
  room : fr.low.toNat + m.window ≤ fr.rsp.toNat
  align : fr.rsp.toNat % 16 = 8
  callSlots : ∀ c ∈ m.callSlots, Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2
  callSlotsApart : m.callSlots ≠ [] → FrameInfo.slotsHigh m.callSlots + m.window ≤
    fr.rsp.toNat ∨ fr.rsp.toNat ≤ FrameInfo.slotsLow m.callSlots
  callSlotAtoms : Atom.All code args mem (m.callSlotAtoms m.callSlots fr)

theorem entryFacts_of_atoms {m : FrameInfo} {fr : Activation} {code : CodeMap}
    {args : Values Value Reg.count} {mem : Ram}
    (h : Atom.All code args mem (m.entryAtoms fr)) : EntryFacts m fr code args mem := by
  unfold FrameInfo.entryAtoms FrameInfo.frameAtoms FrameInfo.entryFrame at h
  rw [atoms_append, atoms_append, atoms_append] at h
  obtain ⟨⟨⟨⟨hrsp, hdf, hregs⟩, _⟩, hstack⟩, hslots⟩ := h
  simp only [FrameInfo.entryRegs, List.map_cons, List.map_nil, Atom.All, Atom.Holds] at hregs
  obtain ⟨h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15, h39, h50, h51, _⟩ := hregs
  unfold FrameInfo.stackAtoms at hstack
  rw [atoms_append, atoms_append] at hstack
  obtain ⟨⟨⟨hread, hret, hretLow, _⟩, hwindow⟩, halign, _⟩ := hstack
  have hw : (0 < m.window → Writable code mem
      (fr.rsp - BitVec.ofNat 64 m.window) m.window) ∧
      fr.low.toNat + m.window ≤ fr.rsp.toNat := by
    by_cases hz : m.window = 0
    · simp only [hz, ↓reduceIte, Atom.All, Atom.Holds] at hwindow
      exact ⟨fun hn => by omega, by simpa only [hz, Nat.add_zero] using hwindow.1⟩
    · simp only [hz, ↓reduceIte, Atom.All, Atom.Holds] at hwindow
      exact ⟨fun _ => hwindow.1, hwindow.2.1⟩
  have readSlots (cs : List (BitVec 64 × BitVec 64))
      (hs : Atom.All code args mem
        (cs.flatMap fun c => [.readable c.1 8, .mem c.1 64 c.2])) :
      ∀ c ∈ cs, Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2 := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.flatMap_cons, atoms_append, Atom.All, Atom.Holds] at hs
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hs.1.1, hs.1.2.1⟩
      · exact ih hs.2 x hx
  have hc : (∀ c ∈ m.callSlots, Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2) ∧
      (m.callSlots ≠ [] → FrameInfo.slotsHigh m.callSlots + m.window ≤ fr.rsp.toNat ∨
        fr.rsp.toNat ≤ FrameInfo.slotsLow m.callSlots) := by
    cases he : m.callSlots with
    | nil => simp
    | cons c cs =>
      have hs := hslots
      simp only [FrameInfo.callSlotAtoms, he, atoms_append, Atom.All, Atom.Holds] at hs
      exact ⟨readSlots _ hs.1, fun _ => hs.2.1⟩
  exact ⟨hrsp, hdf, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hread, hret, hretLow, hw.1, hw.2, halign, hc.1, hc.2, hslots⟩

end AesGcm.Proofs.Machine.Runtime
