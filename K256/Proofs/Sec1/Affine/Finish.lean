import K256.Proofs.Sec1.Affine.Return
import K256.Proofs.Sec1.Affine.Identity
import K256.Proofs.Sec1.Affine.Output
import K256.Proofs.Sec1.Affine.Dispatch

namespace K256.Proofs.Sec1.Affine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Spec.Program K256.Proofs.Sec1.LIR

private theorem finishWrite {code : CodeMap} {args next : Vector Value 53} {mem after : Ram}
    {fr : Activation} (before : Atom.All code args mem (Fn121480.frameAt .l121599 fr))
    (kept : ∀ i : Fin Reg.count, i.val ∈ [3,4,13,22,39,50,51] → next[i] = args[i])
    (writes : RamWriteFrame mem after [⟨fr.rdi.toNat, 89⟩])
    (apart : fr.rdi.toNat + 89 ≤ (fr.rsp - 40).toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.runBlock (dialect code) ⟨.l121599, next, after⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = after ∧
      Atom.All code out.values after (Fn121480.doneAt fr) ∧ out.values[0] = ⟨64, fr.rdi⟩ := by
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at before
  obtain ⟨rsp, df, ptr, r13, mx, ft, fc, bx, r12, r14, r15, bp, retRead, retVal, low, win, room, align, _⟩ := before
  change fr.low.toNat + 1192 ≤ fr.rsp.toNat at room
  have addr (k : Nat) (hk : k ≤ 40) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have kn : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, kn]; omega), kn]
  have lowTop := retRead.low
  have outside (k : Nat) (hk : k ≤ 40) :
      Outside [⟨fr.rdi.toNat, 89⟩] (fr.rsp - BitVec.ofNat 64 k) 8 := by
    have base : (fr.rsp - 40).toNat = fr.rsp.toNat - 40 := addr 40 (by decide)
    have ak := addr k hk
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 89 ≤ _
    omega
  have same (k : Nat) (hk : k ≤ 40) :
      memLoad after (fr.rsp - BitVec.ofNat 64 k) 64 = memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 :=
    writes.memLoad_eq (outside k hk)
  have retSame : memLoad after fr.rsp 64 = memLoad mem fr.rsp 64 := by
    have h := same 0 (by decide)
    change memLoad after (fr.rsp - 0) 64 = memLoad mem (fr.rsp - 0) 64 at h
    rwa [show fr.rsp - 0 = fr.rsp by bv_omega] at h
  have atoms : Atom.All code next after (Fn121480.frameAt .l121599 fr) := by
    simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds]
    exact ⟨(kept 4 (by decide)).trans rsp, (kept 22 (by decide)).trans df,
      (kept 3 (by decide)).trans ptr, (kept 13 (by decide)).trans r13,
      (kept 39 (by decide)).trans mx, (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
      (same 40 (by decide)).trans bx, (same 32 (by decide)).trans r12, (same 24 (by decide)).trans r14,
      (same 16 (by decide)).trans r15, (same 8 (by decide)).trans bp, retRead.of_frame writes,
      retSame.trans retVal, low, win.of_frame writes, room, align, trivial⟩
  obtain ⟨out, run, tag, store, doneAtoms, value, _⟩ := returnAffine fr next after atoms
  exact ⟨out, run, tag, store, doneAtoms, value⟩

theorem finishCoordinates {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Vector Value 53) (mem : Ram)
    (before : Atom.All code args mem (Fn121480.frameAt .l121599 fr))
    (writable : Writable code mem fr.rdi 89)
    (apart : fr.rdi.toNat + 89 ≤ (fr.rsp - 40).toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l121502, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn121480.doneAt fr) ∧
      out.values[0] = ⟨64, fr.rdi⟩ ∧ RamWriteFrame mem out.store [⟨fr.rdi.toNat, 89⟩] ∧
      memLoad out.store (fr.rdi + 88) 8 = memLoad mem (fr.rsp - 136 + 88) 8 ∧
      (memLoad mem (fr.rsp - 136 + 88) 8 = 1 → ∀ p, Parser.PublicKeyAt mem (fr.rsp - 136) p →
        Parser.PublicKeyAt out.store fr.rdi p) := by
  have atoms := before
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, _, ptr, _, _, _, _, _, _, _, _, _, _, _, _, win, _, _, _⟩ := atoms
  have read : Readable mem (fr.rsp - 136) 89 := win.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨next, select, kept⟩ := selectBlock hcode args mem _ _ (congrArg (Value.get 64) rsp)
    (congrArg (Value.get 64) ptr) read writable
  have writes := selected_frame mem (fr.rsp - 136) fr.rdi writable.readable.low
  obtain ⟨out, ret, tag, store, doneAtoms, value⟩ := finishWrite before kept writes apart
  refine ⟨out, .next (next := ⟨⟨.l121599, next, selectedPoint mem (fr.rsp - 136) fr.rdi⟩, []⟩) ?_ (.done ?_), tag, store ▸ doneAtoms, value, store ▸ writes, ?_, ?_⟩
  · simp only [Program.step, select, Transfer.next]
    rfl
  · simp only [Program.step, ret, Transfer.next]
  · rw [store]
    exact selected_valid _ _ _
  · intro valid p key
    rw [store]
    exact selected_publicKey writable.readable.low valid key

theorem finishIdentity {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Vector Value 53) (mem : Ram)
    (before : Atom.All code args mem (Fn121480.frameAt .l121599 fr))
    (zero : (args[1].get 64).setWidth 32 = 0)
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2)
    (writable : Writable code mem fr.rdi 89) (rodata : 0x203400 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 88 ≤ 0x2033a8)
    (apart : fr.rdi.toNat + 89 ≤ (fr.rsp - 40).toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l1214d0, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn121480.doneAt fr) ∧
      out.values[0] = ⟨64, fr.rdi⟩ ∧ RamWriteFrame mem out.store [⟨fr.rdi.toNat, 89⟩] ∧
      WordsAt out.store fr.rdi 64 identityWords ∧ memLoad out.store (fr.rdi + 88) 8 = 1 := by
  let yes := args.set 19 (.ofBool true)
  have atoms := before
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at atoms
  have jump := dispatchIdentity (code := code) args mem zero
  have ptr : yes[3].get 64 = fr.rdi := by
    simp only [yes, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.get 64) atoms.2.2.1
  have df : yes[22].get 1 = 0 := by
    simp only [yes, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.get 1) atoms.2.1
  obtain ⟨next, after, write, words, flag, frame, kept⟩ :=
    writeIdentity hcode yes mem fr.rdi loaded ptr df writable rodata
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,4,13,22,39,50,51]) : next[i] = args[i] := by
    have h : i.val ∉ [1,6,7] ∧ i.val ≠ 19 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rw [kept i h.1]
    simp only [yes, Fin.getElem_fin, Vector.getElem_set, Ne.symm h.2, ↓reduceIte]
  obtain ⟨out, ret, tag, store, doneAtoms, value⟩ := finishWrite before keep frame apart
  refine ⟨out, .next (next := ⟨⟨.l1214d8,yes,mem⟩,[]⟩) ?_
    (.next (next := ⟨⟨.l121599,next,after⟩,[]⟩) ?_ (.done ?_)),
    tag, store ▸ doneAtoms, value, store ▸ frame, store ▸ words, store ▸ flag⟩
  · simp only [Program.step, jump, Transfer.next]; rfl
  · simp only [Program.step, write, Transfer.next]
  · simp only [Program.step, ret, Transfer.next]

end K256.Proofs.Sec1.Affine
