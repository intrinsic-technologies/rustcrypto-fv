import K256.Proofs.Generate.Generator.Multiply.Prepare.State

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

structure PeerCoreEntry (fr : Activation) (a : Registers) (d : Nat) (peer : Projective) : Prop where
  atoms : Atom.All Extracted.programImage a fr.original (Fn11c880.frameAt .l11c880 fr)
  loaded : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  low : fr.low = fr.rsp - 0xed8
  room : 0xed8 ≤ fr.rsp.toNat
  high : fr.rsp.toNat + 0x17e0 ≤ 2^32
  pairPtr : fr.rsi = fr.rsp + 0xc8
  tablePtr : fr.rcx = fr.rsp + 0x1060
  digitPtr : fr.r9 = fr.rsp + 0x80
  outputPtr : fr.rdi = fr.rsp + 0x160
  pairCount : fr.rdx = 1
  tableCount : fr.r8 = 1
  digitCount : memLoad fr.original (fr.rsp + 8) 64 = 1
  countRead : Readable fr.original (fr.rsp + 8) 8
  pairRead : Readable fr.original fr.rsi 152
  tableWrite : Writable Extracted.programImage fr.original fr.rcx 1920
  digitWrite : Writable Extracted.programImage fr.original fr.r9 66
  outputWrite : Writable Extracted.programImage fr.original fr.rdi 120
  valid : peer.valid
  stored : peer.Stored fr.original fr.rsi
  scalar : WordsAt fr.original (fr.rsi + 120) 64 (scalarWords d)

theorem PeerCoreEntry.loaded_of_frame {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (entry : PeerCoreEntry fr initial d peer) (frame : RamWriteFrame fr.original m (coreWrites fr)) :
    ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2 := by
  intro v hv
  have apart {a : BitVec 64} {n : Nat} (w : Writable Extracted.programImage fr.original a n) :
      v.1.toNat + 1 ≤ a.toNat ∨ a.toNat + n ≤ v.1.toNat := by
    apply Classical.byContradiction
    intro h
    apply w.notCode v hv (v.1.toNat - a.toNat) (by omega)
    rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply (frame.outside v.1 ?_).trans (entry.loaded v hv)
  refine ⟨by have := v.1.isLt; omega,?_⟩
  intro r hr
  simp only [coreWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · have atoms := entry.atoms
    simp only [Fn11c880.frameAt,Fn11c880.frameAtG1,Atom.All,Atom.Holds] at atoms
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,stack,_⟩ := atoms
    have hn : (fr.rsp - 3800).toNat = fr.rsp.toNat - 3800 :=
      BitVec.toNat_sub_of_le (by change 3800 ≤ fr.rsp.toNat; exact entry.room)
    have h := apart stack
    simp only [Activation.region,entry.low,hn] at h ⊢
    have := entry.room
    omega
  · exact apart entry.digitWrite
  · exact apart entry.tableWrite
  · exact apart entry.outputWrite

theorem PeerCoreEntry.stackOffset {fr : Activation} {a : Registers} {d : Nat} {peer : Projective}
    (h : PeerCoreEntry fr a d peer) (k : BitVec 64) (bound : k.toNat ≤ 0xed8) :
    (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans bound h.room))

theorem PeerCoreEntry.aboveStack {fr : Activation} {a : Registers} {d : Nat} {peer : Projective}
    (h : PeerCoreEntry fr a d peer) (k : BitVec 64) (bound : k.toNat ≤ 0x17e0) :
    (fr.rsp + k).toNat = fr.rsp.toNat + k.toNat :=
  BitVec.toNat_add_of_lt (by have := h.high; omega)

abbrev peerFirstBase (d : Nat) (peer : Projective) := Curve.signedBase (firstComponent d) peer.value
abbrev peerSecondBase (d : Nat) (peer : Projective) := Curve.signedBase (secondComponent d) (Curve.endomorphism peer.value)

structure PeerPrepared (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d748 fr)
  widths : ParseSignature.ArgumentWidths a
  savedWidths : SavedWidths a
  frame : RamWriteFrame fr.original m (coreWrites fr)
  firstTable : TableAt m fr.rcx (peerFirstBase d peer)
  secondTable : TableAt m (fr.rcx + 960) (peerSecondBase d peer)
  firstDigits : WordsAt m fr.r9 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val)
  secondDigits : WordsAt m (fr.r9 + 33) 8
    (Vector.ofFn fun i : Fin 33 => Radix.byte (secondComponent d).natAbs i.val)
  accumulator : ∃ p : Projective, p.valid ∧ p.Stored m (fr.rsp - 0xb90) ∧
    p.value = Curve.signedWindow (peerFirstBase d peer) (peerSecondBase d peer) 0
      (Curve.radixRemaining (firstComponent d).natAbs 32) (Curve.radixRemaining (secondComponent d).natAbs 32)
  locals :
    let sp := fr.rsp - 0xcb8
    ∀ kv ∈ ([(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),(0x248,fr.rdi),(0xcc0,1)] :
      List (BitVec 64 × BitVec 64)), memLoad m (sp + kv.1) 64 = kv.2


namespace Prepare

structure PeerBasesReady (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop
    extends State .l11cf0d fr a m, Magnitudes fr m d where
  extra : Locals fr m [(0x8,0),(0x60,66),(0x68,152),(0x88,152),(0xc0,0),(0xd8,fr.rcx)]
  firstBaseStored : ∃ p : Projective, p.valid ∧ p.Stored m (sp fr + 0x328) ∧ p.value = peerFirstBase d peer
  endomorphismStored : ∃ p : Projective, p.valid ∧ p.Stored m (sp fr + 0x2b0) ∧ p.value = Curve.endomorphism peer.value
  sign : memLoad m (sp fr + 0x48) 8 = if secondComponent d < 0 then 1 else 0
  mask4 : a[3] = ⟨64,0x3ffffffffffffc⟩
  mask52 : a[12] = ⟨64,0xfffffffffffff⟩
  mask48 : a[14] = ⟨64,0xffffffffffff⟩
  basePtr : a[5] = ⟨64,sp fr + 0x328⟩
  workPtr : a[15] = ⟨64,sp fr + 0x1d0⟩

structure PeerTables (fr : Activation) (m : Ram) (d : Nat) (peer : Projective) : Prop where
  firstTable : TableAt m fr.rcx (peerFirstBase d peer)
  secondTable : TableAt m (fr.rcx + 960) (peerSecondBase d peer)

structure PeerTablesReady (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop
    extends State .l11d546 fr a m, Magnitudes fr m d, PeerTables fr m d peer where
  extra : Locals fr m [(0x60,66),(0x88,152),(0xc0,0)]
  index : a[14] = ⟨64,0⟩
  tablePtr : a[5] = ⟨64,fr.rcx⟩
  firstDigitPtr : a[12] = ⟨64,sp fr + 0x128⟩
  secondDigitPtr : a[15] = ⟨64,sp fr + 0x1d0⟩

structure PeerDigitsReady (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop
    extends State .l11d620 fr a m, PeerTables fr m d peer where
  digitCount : memLoad m (sp fr + 0x60) 64 = 66
  firstDigits : WordsAt m fr.r9 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val)
  secondDigits : WordsAt m (fr.r9 + 33) 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (secondComponent d).natAbs i.val)

end Prepare


def peerWindow (d : Nat) (peer : Projective) :=
  Curve.signedWindow (peerFirstBase d peer) (peerSecondBase d peer) 32
    (firstComponent d).natAbs (secondComponent d).natAbs

def PeerCoreResult (fr : Activation) (d : Nat) (peer : Projective) (out : Output Value Ram Reg.count) : Prop :=
  out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn11c880.doneAt fr) ∧
    (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → out.values[i].width = 64) ∧
    RamWriteFrame fr.original out.store (coreWrites fr) ∧
    Affine.ProjectiveAt out.store fr.rdi (peerWindow d peer)

end K256.Proofs.Generate.Generator.Multiply
