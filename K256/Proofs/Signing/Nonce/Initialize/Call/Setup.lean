import K256.Proofs.Signing.Nonce.Initialize.Update.State
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

def updateActivation (fr : Activation) (a : Verify.Core.Registers) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := fr.rsp - 288, ret := 0x10132a, rdi := fr.rsp - 272,
    rsi := fr.rsp - 176, rdx := 3, rcx := a[1].get 64, r8 := a[8].get 64,
    r9 := a[9].get 64, rbx := fr.rdx, rbp := a[5].get 64, r12 := fr.rsp - 80,
    r13 := a[13].get 64, r14 := fr.rdi, r15 := fr.rsp + 616 }

abbrev seedInput (d : Nat) (digest : ByteArray) := Input.seeded (Encoding.natToOctets 32 d)
  (Encoding.natToOctets 32 (Nat.mod (Encoding.octetsToNat digest) Secp256k1.domain.n))

abbrev startState : State := ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩

private def seedMemory (m : Ram) (sp : BitVec 64) : Ram :=
  let m := memStore m (sp - 248) (0 : BitVec 64)
  let m := memStore m (sp - 256) (0 : BitVec 64)
  let m := memStore m (sp - 264) (0 : BitVec 64)
  let m := memStore m (sp - 272) (0 : BitVec 64)
  let m := memStore m (sp - 240) (0x0101010101010101 : BitVec 64)
  let m := memStore m (sp - 232) (0x0101010101010101 : BitVec 64)
  let m := memStore m (sp - 224) (0x0101010101010101 : BitVec 64)
  let m := memStore m (sp - 216) (0x0101010101010101 : BitVec 64)
  let m := memStore m (sp - 176) (sp + 32 : BitVec 64)
  let m := memStore m (sp - 168) (32 : BitVec 64)
  let m := memStore m (sp - 160) (sp - 80 : BitVec 64)
  let m := memStore m (sp - 152) (32 : BitVec 64)
  let m := memStore m (sp - 144) (1 : BitVec 64)
  let m := memStore m (sp - 136) (0 : BitVec 64)
  memStore m (sp - 288) (0x10132a : BitVec 64)

private theorem repeatedBytes {m : Ram} {addr : BitVec 64} {v : BitVec 64} {byte : UInt8}
    (words : WordsAt m addr 64 (Vector.replicate 4 v))
    (readable : Readable m addr 32)
    (pattern : ∀ j : Fin 32, storedByte v (j.val % 8) = byte) :
    (⟨addr.toNat, 32⟩ : MemoryRegion).HasBytes m ⟨Array.replicate 32 byte⟩ := by
  let bytes : ByteArray := ⟨Array.replicate 32 byte⟩
  have size : bytes.size = 32 := by simp [bytes, ByteArray.size]
  change (⟨addr.toNat, 32⟩ : MemoryRegion).HasBytes m bytes
  rw [← size]
  apply words.hasBytes readable size
  intro j hj hw
  simp only [Vector.getElem_replicate, Nat.reduceDiv, pattern ⟨j, by omega⟩]
  change (Array.replicate 32 byte)[j] = byte
  exact Array.getElem_replicate _

private theorem initialBytes {m : Ram} {sp : BitVec 64}
    (depth : 2208 ≤ sp.toNat) (win : Writable Extracted.programImage (seedMemory m sp) (sp - 2208) 2208) :
    StateAt (seedMemory m sp) (sp - 272) startState := by
  have words (d : Nat) (v : BitVec 64)
      (side : d = 272 ∧ v = 0 ∨ d = 240 ∧ v = 0x0101010101010101) :
      WordsAt (seedMemory m sp) (sp - BitVec.ofNat 64 d) 64 (Vector.replicate 4 v) := by
    intro i hi
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
    all_goals rcases side with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp only [wordAddr, Vector.getElem_replicate, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset]
      unfold seedMemory
      segment_words []
  have second : (sp - 272).toNat + 32 = (sp - 240).toNat := by
    simp only [BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow]
    omega
  constructor
  · exact repeatedBytes (words 272 0 (.inl ⟨rfl, rfl⟩)) (by slot_state region) (by decide +kernel)
  · rw [second]
    exact repeatedBytes (words 240 _ (.inr ⟨rfl, rfl⟩)) (by slot_state region) (by decide +kernel)

private theorem keepBytesAbove {m n : Ram} {r : MemoryRegion} {start : Nat} {bytes : ByteArray}
    (frame : RamWriteFrame m n [r]) (upper : start + 32 ≤ 2^64) (above : r.start + r.size ≤ start)
    (src : (⟨start, 32⟩ : MemoryRegion).HasBytes m bytes) :
    (⟨start, 32⟩ : MemoryRegion).HasBytes n bytes := by
  refine ⟨src.1, fun i => ?_⟩
  have size : bytes.size = 32 := src.1
  have hi := i.isLt
  have addr : (BitVec.ofNat 64 (start + i.val)).toNat = start + i.val := Nat.mod_eq_of_lt (by omega)
  apply (frame.outside _ ?_).trans (src.2 i)
  simp only [Outside, List.mem_singleton, forall_eq, addr]
  omega

local macro "seed_bounds" : tactic => `(tactic|
  (simp only [Activation.region, BitVec.toNat_sub, BitVec.toNat_add,
    BitVec.reduceToNat, Nat.reducePow] at *; omega))

set_option maxRecDepth 3000 in
theorem setup {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {d : Nat} {digest : ByteArray}
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (dst : fr.rdi = fr.rsp + 712) (secretPtr : fr.rsi = fr.rsp + 32)
    (digestPtr : fr.rcx = fr.rsp + 376)
    (secretLen : fr.rdx = 32) (digestLen : fr.r8 = 32) (extraPtr : fr.r9 = 1)
    (extraLen : memLoad fr.original (fr.rsp + 8) 64 = 0)
    (orderPtr : memLoad fr.original (fr.rsp + 16) 64 = fr.rsp + 616)
    (secret : (⟨fr.rsi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original (Encoding.natToOctets 32 d))
    (ready : Prepared fr a m digest) :
    ∃ b n, let child := updateActivation fr a n
      program.runBlock (dialect Extracted.programImage) ⟨.l101295, a, m⟩ =
        .call ⟨.l103f30, b, n⟩ (Verify.resumeAt .l10132a 0x10132a) ∧
      Atom.All Extracted.programImage b n (Fn103f30.frameAt .l103f30 child) ∧
      RamWriteFrame m n [⟨(fr.rsp - 288).toNat, 160⟩] ∧
      (seedInput d digest).At child ∧ StateAt n child.rdi startState := by
  have _ := image
  have _ := digestPtr
  have _ := digestLen
  have _ := orderPtr
  have _ := dst
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, bx, r14, mx, ft, fc, extraSlot, _, secretSlot, _, _, _, _, _, _, _, _, _, _, win, room, align,
    read1, val1, read2, val2, separate, _⟩ := atoms
  have upper := window.of_frame ready.writes
  have bottom : fr.low.toNat = fr.rsp.toNat - 2208 := by rw [low, BitVec.toNat_sub_of_le depth]; rfl
  have extra : memLoad m (fr.rsp + 8) 64 = 0 := by
    refine (ready.writes.memLoad_eq ?_).trans extraLen
    simp only [Outside, List.mem_singleton, forall_eq]
    seed_bounds
  have gSp : a[4].get 64 = fr.rsp - 280 := congrArg (Value.get 64) sp
  have gLen : a[3].get 64 = 32 := (congrArg (Value.get 64) bx).trans secretLen
  have gPtr : a[12].get 64 = fr.rsp - 80 := congrArg (Value.get 64) ready.seedPtr
  let n := seedMemory m fr.rsp
  have step : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l101295, a, m⟩ =
      .call ⟨.l103f30, b, n⟩ (Verify.resumeAt .l10132a 0x10132a) ∧
      Atom.All Extracted.programImage b n
        ((Fn103f30.frameAt .l103f30 (updateActivation fr a n)).take 17) := by
    refine ⟨?_, ?run, ?regs⟩
    case run =>
      cfg_eval
      simp only [gSp, gLen, gPtr, Lift.reduceAddOffset]
      segment_words [extraSlot, secretSlot, extraPtr, secretPtr, extra]
      simp (disch := slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l101295 x hx))) only [ite_eq_left]
      rfl
    case regs =>
      have pack (v : Value) (w : v.width = 64) : v = ⟨64, v.get 64⟩ := by
        cases v
        cases w
        rfl
      simp only [Fn103f30.frameAt, Fn103f30.frameAtG4, List.take_succ_cons, List.take_zero,
        Atom.All, Atom.Holds, updateActivation]
      exact ⟨rfl, df, pack _ (ready.widths 1 (by decide)), rfl, bx, pack _ ready.bpWidth,
        rfl, rfl, pack _ (ready.widths 8 (by decide)), pack _ (ready.widths 9 (by decide)),
        ready.seedPtr, pack _ ready.r13Width, r14, ready.orderPtr, mx, ft, fc, trivial⟩
  obtain ⟨b, run, regs⟩ := step
  have wf : RamWriteFrame m n [⟨(fr.rsp - 288).toNat, 160⟩] := by
    dsimp only [n, seedMemory]
    slot_state region
  have win' := win.of_frame wf
  have got {ptr : BitVec 64} (lo : 0x203dd0 ≤ ptr.toNat) (hi : ptr.toNat + 8 ≤ 0x203e18) :
      Outside [⟨(fr.rsp - 288).toNat, 160⟩] ptr 8 := by
    simp only [Outside, List.mem_singleton, forall_eq]
    seed_bounds
  refine ⟨b, n, run, ?_, wf, ?_, initialBytes depth win'⟩
  · let atoms := Fn103f30.frameAt .l103f30 (updateActivation fr a n)
    change Atom.All _ _ _ atoms
    rw [← List.take_append_drop 17 atoms, Atom.all_append]
    refine ⟨regs, ?_⟩
    change Readable n (fr.rsp - 288) 8 ∧ _
    refine ⟨win'.readable.sub (by seed_bounds) (by seed_bounds),
      memLoad_memStore_same _ _ _ (by decide) (by decide), by change (0x10132a#64).toNat < 2^32; decide,
      ?_, ?_, ?_, read1.of_frame wf, (wf.memLoad_eq (got (by decide) (by decide))).trans val1,
      read2.of_frame wf, (wf.memLoad_eq (got (by decide) (by decide))).trans val2, ?_, trivial⟩
    · change Writable _ n (fr.rsp - 288 - 1920) 1920
      rw [show fr.rsp - 288 - 1920 = fr.rsp - 2208 by bv_omega]
      exact win'.sub (Nat.le_refl _) (by omega)
    · change fr.low.toNat + 1920 ≤ (fr.rsp - 288).toNat
      seed_bounds
    · change (fr.rsp - 288).toNat % 16 = 8
      seed_bounds
    · change 0x204598 ≤ (fr.rsp - 288).toNat ∨ (fr.rsp - 288).toNat ≤ 0x203dd0
      seed_bounds
  · simp only [Input.At, updateActivation, Lift.reduceAddOffset]
    refine ⟨trivial, trivial, trivial, by seed_bounds, win'.readable.sub (by seed_bounds) (by seed_bounds),
      ?secretAddr, ?secretSize, ?hashAddr, ?hashSize, ?extraAddr, ?extraSize, ?_, ?_⟩
    case secretAddr | secretSize | hashAddr | hashSize | extraAddr | extraSize =>
      dsimp only [n, seedMemory]
      segment_words []
    · have input := secret
      rw [secretPtr] at input
      apply keepBytesAbove wf (by seed_bounds) (by seed_bounds)
      exact keepBytesAbove ready.writes (by seed_bounds) (by seed_bounds) input
    · exact keepBytesAbove wf (by seed_bounds) (by seed_bounds) ready.reduced

end K256.Proofs.Signing.Nonce.Initialize
