import K256.Proofs.ParseSignature.Fill.Memory
import K256.Proofs.ParseSignature.Fill.Return

namespace K256.Proofs.ParseSignature.Fill

open Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private theorem jumpReaches {code : CodeMap} {start finish : Location Value Ram Label signature}
    (hj : program.runBlock (dialect code) start = .jump finish) :
    (program.sem (dialect code)).Reaches ⟨start, []⟩ ⟨finish, []⟩ := by
  apply Semantics.Reaches.single
  change program.step (dialect code) ⟨start, []⟩ = .next ⟨finish, []⟩
  simp only [Program.step, hj, Transfer.next]

private theorem stackStore {code : CodeMap} {fr : Activation} (h : MemoryPre code fr)
    {m : Ram} {off : Nat} (hoff : 8 ≤ off ∧ off ≤ 80)
    (hf : RamWriteFrame fr.original m (fillWrites fr)) (v : BitVec 64) :
    RamWriteFrame fr.original (memStore m (fr.rsp - BitVec.ofNat 64 off) v) (fillWrites fr) :=
  hf.memStore v ⟨stackWindow fr, List.mem_cons_self .., h.stackInWindow hoff⟩

private theorem returnSlotOutside {code : CodeMap} {fr : Activation} (h : MemoryPre code fr) :
    Outside (fillWrites fr) fr.rsp 8 := by
  have retLow := h.retReadable.low
  have room := h.stackRoom
  refine ⟨by omega, ?_⟩
  intro region hregion
  simp only [fillWrites, List.mem_cons, List.not_mem_nil, or_false] at hregion
  rcases hregion with rfl | rfl
  · right
    have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
    simp only [stackWindow, buffer, sp80]
    omega
  · have sep := h.outputStack.2 _ (List.mem_cons_self ..)
    change fr.rdx.toNat + 32 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdx.toNat at sep
    change fr.rsp.toNat + 8 ≤ fr.rdx.toNat ∨ fr.rdx.toNat + 32 ≤ fr.rsp.toNat
    omega

private theorem readOtherStackWord (sp : BitVec 64) (m : Ram) (v : BitVec 64)
    (off target : BitVec 64) (apart : 8 ≤ (off - target).toNat ∧ 8 ≤ (target - off).toNat) :
    memLoad (memStore m (sp - off) v) (sp - target) 64 = memLoad m (sp - target) 64 := by
  apply memLoad_memStore_of_rangeApart
  apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _)
  rwa [show (0 : BitVec 64) - target - (0 - off) = off - target by bv_omega,
    show (0 : BitVec 64) - off - (0 - target) = target - off by bv_omega]

private theorem readStoredWord (m : Ram) (addr : BitVec 64) (v : BitVec 64) :
    memLoad (memStore m addr v) addr 64 = v :=
  memLoad_memStore_same m addr v (by decide) (by decide)

theorem setupFill {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Registers)
    (entry : Atom.All code args fr.original (Fn127d70.frameInfo.entryAtoms fr))
    (hn : fr.rsi = 32) (hk : fr.rcx = 4) (hwid : fr.r8 = 256) (hmem : MemoryPre code fr) :
    ∃ a : Registers, ∃ m : Ram,
      (program.sem (dialect code)).Reaches
        ⟨⟨.l127d70, args, fr.original⟩, []⟩ ⟨⟨.l127e2e, a, m⟩, []⟩ ∧
      RamWriteFrame fr.original m (fillWrites fr) ∧ FillSavedStack fr m ∧
      a[3] = ⟨64, 256⟩ ∧ a[4] = ⟨64, fr.rsp - 72⟩ ∧ a[5] = ⟨64, 32⟩ ∧
      a[12] = ⟨64, fr.rdi + 32⟩ ∧ a[13] = ⟨64, 32⟩ ∧ a[14] = ⟨64, fr.rdx⟩ ∧
      a[15] = ⟨64, 0⟩ ∧ a[22] = ⟨1, 0⟩ ∧ a[39] = ⟨32, fr.mxcsr⟩ ∧
      a[50] = ⟨16, fr.ftw⟩ ∧ a[51] = ⟨16, fr.fcw⟩ ∧
      a[8].width = 64 ∧ a[9].width = 64 := by
  change Atom.All code args fr.original (Fn127d70.frameAt .l127d70 fr) at entry
  simp only [Fn127d70.frameAt, Fn127d70.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, r1, r2, r3, r5, r6, r7, r8, r9, r12, r13, r14, r15, r39, r50, r51,
    _, retValue, _⟩ := entry
  rw [hn] at r6
  rw [hk] at r1
  rw [hwid] at r8
  obtain ⟨a1, hb1, sp1, dst1, keep1⟩ := entryBlock hcode sp r1 r8 hmem.stackWritable
  let m1 := saveRegisters fr.original fr.rsp args
  have fm1 : RamWriteFrame fr.original m1 (fillWrites fr) := by
    dsimp only [m1, saveRegisters]
    exact stackStore hmem (off := 48) (by decide)
      (stackStore hmem (off := 40) (by decide)
      (stackStore hmem (off := 32) (by decide)
      (stackStore hmem (off := 24) (by decide)
      (stackStore hmem (off := 16) (by decide)
      (stackStore hmem (off := 8) (by decide) (RamWriteFrame.refl _ _) _) _) _) _) _) _
  have ws2 : StoreOk code m1 (fr.rsp - 64) 8 0x127d94 5 :=
    storeOk_of_codeRange (off := 3) (hmem.stackWord (d := 64) (by decide) fm1)
      (fun x hx => hcode x (code_l127d91 x hx)) (by decide)
  obtain ⟨a2, hb2, bx2, left2, keep2⟩ := setupCountBlock sp1
    ((keep1 1 (by decide) (by decide)).trans r1)
    ((keep1 6 (by decide) (by decide)).trans r6)
    ((keep1 8 (by decide) (by decide)).trans r8) ws2
  let m2 := memStore m1 (fr.rsp - 64) (4 : BitVec 64)
  have fm2 : RamWriteFrame fr.original m2 (fillWrites fr) :=
    stackStore hmem (off := 64) (by decide) fm1 _
  have readCount : LoadOk m2 (fr.rsp - 64) 8 :=
    let hr := (hmem.stackWord (d := 64) (by decide) fm2).readable
    ⟨hr.low, hr.present⟩
  have countValue : memLoad m2 (fr.rsp - 64) 64 = 4 :=
    readStoredWord _ _ _
  have sp2 := (keep2 4 (by decide) (by decide)).trans sp1
  obtain ⟨a3, hb3, bp3, keep3⟩ := setupLimbCountBlock (code := code) sp2 left2 readCount countValue
  have fromEntry (r : Nat) (bound : r < Reg.count)
      (h1 : r ∈ [1, 6, 7, 8, 9, 22, 39, 50, 51])
      (h2 : r ∈ [4, 6, 7, 8, 9, 14, 22, 39, 50, 51])
      (h3 : r ∈ [3, 4, 6, 7, 8, 9, 13, 14, 22, 39, 50, 51]) :
      a3[r] = args[r] :=
    (keep3 r h3 bound).trans ((keep2 r h2 bound).trans (keep1 r h1 bound))
  have hn3 := (fromEntry 6 (by decide) (by decide) (by decide) (by decide)).trans r6
  obtain ⟨a4, hb4, count4, src4, index4, keep4⟩ := setupLoopBlock (code := code) (m := m2) hn3 bp3
  have src3 := (fromEntry 7 (by decide) (by decide) (by decide) (by decide)).trans r7
  rw [get64 src3] at src4
  have preserved (r : Nat) (bound : r < Reg.count)
      (h1 : r ∈ [1, 6, 7, 8, 9, 22, 39, 50, 51])
      (h2 : r ∈ [4, 6, 7, 8, 9, 14, 22, 39, 50, 51])
      (h3 : r ∈ [3, 4, 6, 7, 8, 9, 13, 14, 22, 39, 50, 51])
      (h4 : r ∈ [3, 4, 8, 9, 13, 14, 22, 39, 50, 51]) :
      a4[r] = args[r] :=
    (keep4 r h4 bound).trans (fromEntry r bound h1 h2 h3)
  have sp4 := (keep4 4 (by decide) (by decide)).trans ((keep3 4 (by decide) (by decide)).trans sp2)
  have bx4 := (keep4 3 (by decide) (by decide)).trans ((keep3 3 (by decide) (by decide)).trans bx2)
  have left4 := (keep4 13 (by decide) (by decide)).trans ((keep3 13 (by decide) (by decide)).trans left2)
  have dst4 := (keep4 14 (by decide) (by decide)).trans ((keep3 14 (by decide) (by decide)).trans
    ((keep2 14 (by decide) (by decide)).trans dst1))
  have dst4 := dst4.trans (congrArg (fun v : BitVec 64 => (⟨64, v⟩ : Value)) (get64 r2))
  have hsaved : FillSavedStack fr m2 := by
    have slot (off : Nat) (hoff : 8 ≤ off ∧ off ≤ 208) :
        Readable m2 (fr.rsp - BitVec.ofNat 64 off) 8 :=
      (hmem.stackWord hoff fm2).readable
    refine ⟨⟨slot 48 (by decide), ?_⟩, ⟨slot 40 (by decide), ?_⟩, ⟨slot 32 (by decide), ?_⟩,
      ⟨slot 24 (by decide), ?_⟩, ⟨slot 16 (by decide), ?_⟩, ⟨slot 8 (by decide), ?_⟩,
      ⟨hmem.retReadable.of_frame fm2, (fm2.memLoad_eq (returnSlotOutside hmem)).trans retValue⟩⟩
    all_goals simp (disch := decide) only [m2, m1, saveRegisters, readOtherStackWord, readStoredWord]
    · exact get64 r3
    · exact get64 r12
    · exact get64 r13
    · exact get64 r14
    · exact get64 r15
    · exact get64 r5
  refine ⟨a4, m2, ?_, fm2, hsaved, bx4, sp4, count4, src4, left4, dst4, index4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (jumpReaches hb1).trans ((jumpReaches hb2).trans ((jumpReaches hb3).trans (jumpReaches hb4)))
  · exact (preserved 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans df
  · exact (preserved 39 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r39
  · exact (preserved 50 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r50
  · exact (preserved 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r51
  · exact congrArg Value.width
      ((preserved 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r8)
  · exact congrArg Value.width
      ((preserved 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r9)

end K256.Proofs.ParseSignature.Fill
