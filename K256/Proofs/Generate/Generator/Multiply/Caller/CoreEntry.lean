import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.LIR.Fn10ee80.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters

abbrev localSp (fr : Activation) := fr.rsp - 5960

def coreActivation (fr : Activation) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := localSp fr - 8, ret := 0x10f12f,
    low := fr.low, rbx := fr.rdi, r12 := localSp fr + 8, r13 := 0x12a820,
    r14 := localSp fr + 3848, r15 := localSp fr + 4000,
    rsi := localSp fr + 3848, rdx := 1, rcx := localSp fr + 4000,
    r8 := 1, r9 := localSp fr + 8 }

private theorem stackRegion {fr : Activation} (room : 9768 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 9768) : fr.region = ⟨(fr.rsp - 9768).toNat,9768⟩ := by
  simp only [Activation.region, low]
  congr 1
  rw [BitVec.toNat_sub_of_le (by change 9768 ≤ fr.rsp.toNat; exact room)]
  change _ - (_ - 9768) = 9768
  omega

theorem callerImage {fr : Activation} {m : Ram} (room : 9768 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 9768) (stack : Writable Extracted.programImage fr.original (fr.rsp - 9768) 9768)
    (frame : RamWriteFrame fr.original m [fr.region])
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2) :
    ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2 := by
  rw [stackRegion room low] at frame
  exact Affine.Invert.Core.stackImage stack frame image

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
theorem makeCoreEntry {fr : Activation} {a b : Registers} {m : Ram} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ v ∈ Extracted.programImage, fr.original[v.1]? = some v.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32) (dst : fr.rdi = fr.rsp + 232)
    (dest : Writable Extracted.programImage fr.original fr.rdi 120)
    (frame : RamWriteFrame fr.original m [fr.region])
    (regs : Atom.All Extracted.programImage b m
      [ .gpr 4 (localSp fr - 8), .reg 22 ⟨1,0⟩, .gpr 1 (localSp fr + 4000), .gpr 2 1,
        .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 6 (localSp fr + 3848), .gpr 7 fr.rdi,
        .gpr 8 1, .gpr 9 (localSp fr + 8), .gpr 12 (localSp fr + 8), .gpr 13 0x12a820,
        .gpr 14 (localSp fr + 3848), .gpr 15 (localSp fr + 4000), .reg 39 ⟨32,fr.mxcsr⟩,
        .reg 50 ⟨16,fr.ftw⟩, .reg 51 ⟨16,fr.fcw⟩ ])
    (tag : memLoad m (localSp fr - 8) 64 = 0x10f12f) (count : memLoad m (localSp fr) 64 = 1)
    (generator : ∀ i : Fin 15, memLoad m (wordAddr (localSp fr + 3848) 64 i.val) 64 =
      memLoad m (wordAddr 0x202bc8 64 i.val) 64)
    (scalar : WordsAt m (localSp fr + 3968) 64 (scalarWords d)) :
    CoreEntry (coreActivation fr m) b d := by
  simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,stack,_,align,_,_,_,_,apart,_⟩ := atoms
  have loaded := callerImage room low stack frame image
  have w := stack.of_frame frame
  have slot {k : BitVec 64} {n : Nat} (fit : (k - (0 - 9768)).toNat + n ≤ 9768) :
      Writable Extracted.programImage m (fr.rsp + k) n :=
    w.of_offsets rfl (addr_sub fr.rsp 9768) fit
  have access {x : BitVec 64} {k : BitVec 64} {n : Nat}
      (eq : x = fr.rsp + k) (fit : (k - (0 - 9768)).toNat + n ≤ 9768) :
      Writable Extracted.programImage m x n := eq ▸ slot fit
  have spNat : (localSp fr - 8).toNat = fr.rsp.toNat - 5968 := by
    rw [show localSp fr - 8 = fr.rsp - 5968 by unfold localSp; bv_omega]
    apply BitVec.toNat_sub_of_le
    change 5968 ≤ fr.rsp.toNat
    omega
  have lowNat : fr.low.toNat = fr.rsp.toNat - 9768 := by
    rw [low, BitVec.toNat_sub_of_le (by change 9768 ≤ fr.rsp.toNat; exact room)]
    rfl
  have slots := Fn11c880.callSlots_loaded (sections := Extracted.programSections)
    (by simp [Extracted.programSections, rodataSection]) loaded
  obtain ⟨g1,v1⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨g2,v2⟩ := slots (0x203e20,0x100a20) (by decide)
  have plus : localSp fr - 8 + 8 = localSp fr := by bv_omega
  refine ⟨?_,loaded,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,?_,?_,?_,?_,?_,dest.of_frame frame,generator,?_⟩
  · simp only [Fn11c880.frameAt, Fn11c880.frameAtG1, coreActivation, Atom.All, Atom.Holds] at regs ⊢
    obtain ⟨r4,df,r1,r2,r3,r5,r6,r7,r8,r9,r12,r13,r14,r15,mx,ft,fc,_⟩ := regs
    refine ⟨r4,df,r1,r2,r3,r5,r6,r7,r8,r9,r12,r13,r14,r15,mx,ft,fc,
      (access (k := 0 - 5968) (by unfold localSp; bv_omega) (by decide)).readable,tag,by decide,
      access (k := 0 - 9768) (by unfold localSp; bv_omega) (by decide),?_,?_,g1,v1,g2,v2,?_,trivial⟩
    all_goals omega
  · change fr.low = localSp fr - 8 - 3800
    rw [low]; unfold localSp; bv_omega
  · change 3800 ≤ (localSp fr - 8).toNat; omega
  · change (localSp fr - 8).toNat + 6320 ≤ _; omega
  · change localSp fr + 3848 = localSp fr - 8 + 3856; bv_omega
  · change localSp fr + 4000 = localSp fr - 8 + 4008; bv_omega
  · change localSp fr + 8 = localSp fr - 8 + 16; bv_omega
  · change fr.rdi = localSp fr - 8 + 6200; rw [dst]; unfold localSp; bv_omega
  · exact plus ▸ count
  · exact (access (k := 0 - 5960) (by change localSp fr - 8 + 8 = _; unfold localSp; bv_omega) (by decide)).readable
  · exact (access (k := 0 - 2112) (by change localSp fr + 3848 = _; unfold localSp; bv_omega) (by decide)).readable
  · exact access (k := 0 - 1960) (by change localSp fr + 4000 = _; unfold localSp; bv_omega) (by decide)
  · exact access (k := 0 - 5952) (by change localSp fr + 8 = _; unfold localSp; bv_omega) (by decide)
  · change WordsAt m (localSp fr + 3848 + 120) 64 _
    exact (show localSp fr + 3848 + 120 = localSp fr + 3968 by bv_omega) ▸ scalar

end K256.Proofs.Generate.Generator.Multiply.Caller
