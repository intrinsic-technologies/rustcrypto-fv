import K256.Proofs.Common.Tactic
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.LIR.Fn109e60.Frame
import K256.Proofs.Generate.Sampling.Predicate

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem scalarReturn (fr : Activation) (a : Vector Value Reg.count) (m : Ram)
    (frame : Atom.All Extracted.programImage a m (Fn109e60.frameAt .l109f32 fr))
    (dst : Writable Extracted.programImage m fr.rdi 33)
    (dstApart : Outside [ParseSignature.callStack fr] fr.rdi 33)
    (widths : ParseSignature.ArgumentWidths a)
    (w : Nat → BitVec 64) (flag : BitVec 8)
    (rax : a[0].get 8 = flag)
    (r13 : a[13] = ⟨64, w 0⟩) (r12 : a[12] = ⟨64, w 1⟩)
    (r15 : a[15] = ⟨64, w 2⟩) (r14 : a[14] = ⟨64, w 3⟩) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109f32, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn109e60.doneAt fr) ∧
      RamWriteFrame m out.store [⟨fr.rdi.toNat, 33⟩] ∧ ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 64 (Vector.ofFn fun i : Fin 4 => w i.val) ∧
      memLoad out.store (fr.rdi + 32) 8 = flag := by
  simp only [Fn109e60.frameAt, Fn109e60.frameAtG0, Atom.All, Atom.Holds] at frame
  obtain ⟨sp, df, bx, bp, mx, ftw, fcw, s3, s12, s13, s14, s15, hr, ret, low, stack, room, _, _⟩ := frame
  have spBits : a[4].get 64 = fr.rsp - 56 := congrArg (Value.get 64) sp
  have diBits : a[3].get 64 = fr.rdi := congrArg (Value.get 64) bx
  have al : (a[0].get 64).setWidth 8 = flag :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans rax
  let finalMem := memStore (memStore (memStore (memStore (memStore m fr.rdi (w 0))
    (fr.rdi + 8) (w 1)) (fr.rdi + 16) (w 2)) (fr.rdi + 24) (w 3)) (fr.rdi + 32) flag
  have dstLow := dst.readable.low
  have finalFrame : RamWriteFrame m finalMem [⟨fr.rdi.toNat, 33⟩] := by
    dsimp only [finalMem]
    slot_state region
  have stackSlot (off : BitVec 64) (small : off.toNat ≤ 40) :
      memLoad finalMem (fr.rsp - off) 64 =
        memLoad m (fr.rsp - off) 64 := by
    apply finalFrame.memLoad_eq
    have haddr : (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    have hrLow := hr.low
    have sep := dstApart.2 _ (List.mem_singleton_self _)
    change fr.rdi.toNat + 33 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at sep
    refine ⟨?_, ?_⟩
    · rw [haddr]; omega
    · intro r hrmem
      rcases List.mem_singleton.mp hrmem with rfl
      change _ ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 33 ≤ _
      rw [haddr]
      change fr.rsp.toNat - off.toNat + 8 ≤ _ ∨ _
      omega
  have finalRet : memLoad finalMem fr.rsp 64 = fr.ret := by
    have saved := stackSlot 0 (by decide)
    rw [show fr.rsp - 0 = fr.rsp by bv_omega] at saved
    exact saved.trans ret
  have incl := fun x hx => Common.fnCode_subset_programImage x (code_l109f32 x hx)
  dsimp only [finalMem] at stackSlot finalRet
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?frame_, ?width, ?words, ?flag⟩
  case run =>
    simp only [Program.step]
    cfg_eval
    simp only [spBits, diBits, r13, r12, r15, r14, Value.get_mk_setWidth, BitVec.setWidth_eq, al]
    simp only [show fr.rsp - 56 + 16 = fr.rsp - 40 by bv_omega,
      show fr.rsp - 56 + 24 = fr.rsp - 32 by bv_omega,
      show fr.rsp - 56 + 32 = fr.rsp - 24 by bv_omega,
      show fr.rsp - 56 + 40 = fr.rsp - 16 by bv_omega,
      show fr.rsp - 56 + 48 = fr.rsp - 8 by bv_omega,
      BitVec.sub_add_cancel, show fr.rsp - 56 + 64 = fr.rsp + 8 by bv_omega,
      stackSlot 40 (by decide), stackSlot 32 (by decide), stackSlot 24 (by decide),
      stackSlot 16 (by decide), stackSlot 8 (by decide), finalRet, low, s3, s12, s13, s14, s15,
      and_true]
    simp (disch := slot_guard using incl) only [ite_eq_left]
    rfl
  case tag => rfl
  case done_ =>
    exact ⟨rfl, df, rfl, bp, rfl, rfl, rfl, rfl, mx, ftw, fcw, trivial⟩
  case frame_ => exact finalFrame
  case width =>
    intro ⟨i, hi⟩ ha
    have hw := widths ⟨i, hi⟩ ha
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw
  case words =>
    change WordsAt finalMem fr.rdi 64 _
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp (disch := first | store_disch | decide) only [finalMem, wordAddr, Nat.reduceDiv,
        Nat.reduceMul, BitVec.add_zero, memLoad_memStore_of_rangeApart,
        memLoad_memStore_same, Vector.getElem_ofFn] <;>
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case flag => exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Generate.Generator.Sample
