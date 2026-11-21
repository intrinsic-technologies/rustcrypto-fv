import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Multiply.Coordinates
import K256.Proofs.Generate.LIR.Fn11c880.Frame
import K256.Proofs.Generate.Curve

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev Registers := Values Value Reg.count

noncomputable abbrev Reaches (l : Label) (a : Registers) (m : Ram)
    (l' : Label) (a' : Registers) (m' : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨l, a, m⟩, []⟩ ⟨⟨l', a', m'⟩, []⟩

def SavedWidths (a : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64

abbrev scalarWords (d : Nat) := Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))

def coreWrites (fr : Activation) : List MemoryRegion :=
  [fr.region, ⟨fr.r9.toNat, 66⟩, ⟨fr.rcx.toNat, 1920⟩, ⟨fr.rdi.toNat, 120⟩]

structure CoreEntry (fr : Activation) (a : Registers) (d : Nat) : Prop where
  atoms : Atom.All Extracted.programImage a fr.original (Fn11c880.frameAt .l11c880 fr)
  loaded : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  low : fr.low = fr.rsp - 0xed8
  room : 0xed8 ≤ fr.rsp.toNat
  high : fr.rsp.toNat + 6320 ≤ 2^32
  pairPtr : fr.rsi = fr.rsp + 0xf10
  tablePtr : fr.rcx = fr.rsp + 0xfa8
  digitPtr : fr.r9 = fr.rsp + 16
  outputPtr : fr.rdi = fr.rsp + 6200
  pairCount : fr.rdx = 1
  tableCount : fr.r8 = 1
  digitCount : memLoad fr.original (fr.rsp + 8) 64 = 1
  countRead : Readable fr.original (fr.rsp + 8) 8
  pairRead : Readable fr.original fr.rsi 152
  tableWrite : Writable Extracted.programImage fr.original fr.rcx 1920
  digitWrite : Writable Extracted.programImage fr.original fr.r9 66
  outputWrite : Writable Extracted.programImage fr.original fr.rdi 120
  generator : ∀ i : Fin 15, memLoad fr.original (wordAddr fr.rsi 64 i.val) 64 =
    memLoad fr.original (wordAddr 0x202bc8 64 i.val) 64
  scalar : WordsAt fr.original (fr.rsi + 120) 64 (scalarWords d)

theorem CoreEntry.loaded_of_frame {fr : Activation} {initial : Registers} {d : Nat} {m : Ram}
    (entry : CoreEntry fr initial d) (frame : RamWriteFrame fr.original m (coreWrites fr)) :
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

structure SplitState (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11c9e7 fr)
  widths : ParseSignature.ArgumentWidths a
  savedWidths : SavedWidths a
  frame : RamWriteFrame fr.original m [fr.region]
  first : WordsAt m (fr.rsp - 0xcb8 + 0x1d0) 64 (scalarWords (Generate.Curve.splitFirst d))
  second : WordsAt m (fr.rsp - 0xcb8 + 0x418) 64 (scalarWords (Generate.Curve.splitSecond d))
  locals :
    let sp := fr.rsp - 0xcb8
    ∀ kv ∈ ([(0x8,0),(0x38,fr.rsi),(0x60,66),(0x68,152),(0x88,152),(0xb0,fr.rsi),
      (0xc0,0),(0xd8,fr.rcx),(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),
      (0x248,fr.rdi)] : List (BitVec 64 × BitVec 64)),
      memLoad m (sp + kv.1) 64 = kv.2
  savedR15 : a[15] = ⟨64, fr.rsp - 0xcb8 + 0x1d0⟩

end K256.Proofs.Generate.Generator.Multiply
