import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.ProductFlags
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.LIR.Fn11b510.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def reductionActivation (fr : Activation) (b : Registers) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := fr.rsp - 192, ret := 0x109be7, rdi := fr.rdi,
    rsi := fr.rsp - 112, rdx := 0, rcx := b[1].get 64, r8 := b[8].get 64, r9 := b[9].get 64,
    rbx := b[3].get 64, rbp := b[5].get 64, r12 := b[12].get 64, r13 := b[13].get 64,
    r14 := fr.rdi, r15 := b[15].get 64 }

def mulStack (fr : Activation) : MemoryRegion := ⟨fr.rsp.toNat - 321, 321⟩

structure StagedProduct (fr : Activation) (b : Registers) (old m : Ram)
    (w : Vector (BitVec 64) 8) : Prop where
  entry : Atom.All Extracted.programImage b m (Fn11b510.frameAt .l11b510 (reductionActivation fr b m))
  frame : RamWriteFrame old m [mulStack fr]
  saved : ∀ (k r : Nat), (k,r) ∈ [(48,3),(40,12),(32,13),(24,14),(16,15),(8,5)] →
    memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r
  words : WordsAt m (fr.rsp - 112) 64 w

set_option maxHeartbeats 5600000 in
set_option maxRecDepth 8192 in
theorem stageMul {fr : Activation} {a : Registers} {m : Ram} {x y : Nat}
    (atoms : Atom.All Extracted.programImage a m (Fn1099c0.frameAt .l1099c0 fr))
    (rx : Readable m fr.rsi 32) (ry : Readable m fr.rdx 32)
    (apart : ∀ src ∈ [fr.rsi, fr.rdx], src.toNat + 32 ≤ fr.rsp.toNat - 321 ∨
        fr.rsp.toNat + 8 ≤ src.toNat)
    (wx : WordsAt m fr.rsi 64 (scalarWords x)) (wy : WordsAt m fr.rdx 64 (scalarWords y)) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l1099c0, a, m⟩ =
        .call ⟨.l11b510, b, n⟩ (Generator.callFrame .l109be7 0x109be7) ∧
      StagedProduct fr b m n (productWords (scalarWords x) (scalarWords y)) := by
  generalize hxw : scalarWords x = av at wx ⊢
  generalize hyw : scalarWords y = bv at wy ⊢
  simp only [Fn1099c0.frameAt, Fn1099c0.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, stack, low, align, _⟩ := atoms
  have ax := apart fr.rsi (by simp)
  have ay := apart fr.rdx (by simp)
  have high := retRead.low
  have g4 : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have g1 : a[1].get 64 = fr.rcx := congrArg (Value.get 64) cx
  have g2 : a[2].get 64 = fr.rdx := congrArg (Value.get 64) dx
  have g3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have g5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have g6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have g7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have g8 : a[8].get 64 = fr.r8 := congrArg (Value.get 64) r8
  have g9 : a[9].get 64 = fr.r9 := congrArg (Value.get 64) r9
  have g12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have g13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have g14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have g15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have wx0 : memLoad m (fr.rsi) 64 = av[0] := by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using wx 0 (by decide)
  have wx1 : memLoad m (fr.rsi + 8) 64 = av[1] := wx 1 (by decide)
  have wx2 : memLoad m (fr.rsi + 16) 64 = av[2] := wx 2 (by decide)
  have wx3 : memLoad m (fr.rsi + 24) 64 = av[3] := wx 3 (by decide)
  have wy0 : memLoad m (fr.rdx) 64 = bv[0] := by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using wy 0 (by decide)
  have wy1 : memLoad m (fr.rdx + 8) 64 = bv[1] := wy 1 (by decide)
  have wy2 : memLoad m (fr.rdx + 16) 64 = bv[2] := wy 2 (by decide)
  have wy3 : memLoad m (fr.rdx + 24) 64 = bv[3] := wy 3 (by decide)
  refine ⟨?nextRegs, ?nextStore, ?runStage, ?postStage⟩
  case runStage =>
    arithmetic_segment using code_l1099c0 [g4, g1, g2, g3, g5, g6, g7, g8, g9, g12, g13, g14, g15, wx0, wx1, wx2, wx3, wy0, wy1, wy2, wy3, Lift.reduceSubOffset, Lift.reduceAddOffset,
      Lift.reduceSubNeg, Lift.reduceAddNeg, BitVec.reduceAdd, BitVec.reduceSub]
  case postStage =>
    constructor
    case entry =>
      simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, Atom.All, Atom.Holds, reductionActivation]
      refine ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, di, rfl, rfl, rfl, rfl, rfl, rfl,
        mx, ftw, fcw, ?_, ?_, by decide, ?_, ?_, ?_, trivial⟩
      · slot_state region
      · refine_norm []
      · slot_state region
      all_goals rw [BitVec.toNat_sub_of_le (by change 192 ≤ fr.rsp.toNat; omega)]
      · change fr.low.toNat + 129 ≤ fr.rsp.toNat - 192
        omega
      · change (fr.rsp.toNat - 192) % 16 = 8
        omega
    case frame =>
      unfold mulStack
      slot_state region
    case saved =>
      intro k r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with h|h|h|h|h|h <;> obtain ⟨rfl,rfl⟩ := h <;> refine_norm [] <;> rfl
    case words =>
      rw [← ProductSchedule.machineProduct_eq]
      intro i hi
      have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, Lift.reduceAddOffset]
        refine_norm [wx0,wx1,wx2,wx3,wy0,wy1,wy2,wy3]
        match_product_words

end K256.Proofs.Generate.Generator.Multiply.Split
