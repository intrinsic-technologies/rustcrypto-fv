import K256.Proofs.Signing.Nonce.Initialize.State
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Common.WordCopy
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

private def copyState (m : Ram) (sp : BitVec 64) : Ram :=
  let n := memStore m (sp + 776) (memLoad m (sp - 216) 64)
  let n := memStore n (sp + 768) (memLoad m (sp - 224) 64)
  let n := memStore n (sp + 760) (memLoad m (sp - 232) 64)
  let n := memStore n (sp + 752) (memLoad m (sp - 240) 64)
  let n := memStore n (sp + 744) (memLoad m (sp - 248) 64)
  let n := memStore n (sp + 736) (memLoad m (sp - 256) 64)
  let n := memStore n (sp + 728) (memLoad m (sp - 264) 64)
  let n := memStore n (sp + 720) (memLoad m (sp - 272) 64)
  memStore n (sp + 712) (sp + 616)

set_option maxRecDepth 2400 in
private theorem stateBytes {m : Ram} {sp : BitVec 64} {state : State}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32)
    (readable : Readable (copyState m sp) sp 784) (src : StateAt m (sp - 272) state) :
    (⟨(sp + 712).toNat + 8, 32⟩ : MemoryRegion).HasBytes (copyState m sp) state.key ∧
      (⟨(sp + 712).toNat + 40, 32⟩ : MemoryRegion).HasBytes (copyState m sp) state.value := by
  have offset (k : Nat) (hk : k ≤ 784) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2^64),
      Nat.mod_eq_of_lt (by omega : sp.toNat + k < 2^64)]
  have copy {payload : ByteArray} (start dest : Nat) (side : (start = 272 ∧ dest = 720) ∨
      (start = 240 ∧ dest = 752))
      (source : (⟨(sp - BitVec.ofNat 64 start).toNat, 32⟩ : MemoryRegion).HasBytes m payload) :
      (⟨(sp + BitVec.ofNat 64 dest).toNat, 32⟩ : MemoryRegion).HasBytes (copyState m sp) payload := by
    have size : payload.size = 32 := source.1
    rw [← size]
    apply Common.hasBytes_of_word_copy (n := 4) source size
    · apply readable.sub <;> rw [offset dest (by omega)] <;> omega
    · intro i hi
      obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
      all_goals rcases side with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Lift.reduceAddOffset]
        unfold copyState
        segment_words []
  have ptr : (sp + 712).toNat = sp.toNat + 712 := offset 712 (by decide)
  have ptrK : (sp + 720).toNat = sp.toNat + 720 := offset 720 (by decide)
  have ptrV : (sp + 752).toNat = sp.toNat + 752 := offset 752 (by decide)
  have valueStart : (sp - 240).toNat = (sp - 272).toNat + 32 := by
    simp only [BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow]
    omega
  obtain ⟨key, value⟩ := src
  rw [← valueStart] at value
  rw [show (sp + 712).toNat + 8 = (sp + 720).toNat by omega,
    show (sp + 712).toNat + 40 = (sp + 752).toNat by omega]
  exact ⟨copy 272 720 (.inl ⟨rfl, rfl⟩) key, copy 240 752 (.inr ⟨rfl, rfl⟩) value⟩

set_option maxRecDepth 3000 in
set_option maxHeartbeats 700000 in
theorem returnPath {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {state : State}
    (dst : fr.rdi = fr.rsp + 712)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (depth : 2208 ≤ fr.rsp.toNat) (limit : fr.rsp.toNat + 784 < 2^32)
    (ready : Updated fr a m state) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10132a, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn100ea0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 72⟩] ∧
      memLoad out.store fr.rdi 64 = fr.rsp + 616 ∧
      (⟨fr.rdi.toNat + 8, 32⟩ : MemoryRegion).HasBytes out.store state.key ∧
      (⟨fr.rdi.toNat + 40, 32⟩ : MemoryRegion).HasBytes out.store state.value := by
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨stackReg, df, _, dstReg, mx, ft, fc, _, _, _, _, _, _, _, _,
    bx, r12, r13, r14, r15, bp, retRead, ret, retLow, stack, _⟩ := atoms
  have upper := window.of_frame ready.writes
  have sp : a[4].get 64 = fr.rsp - 280 := congrArg (Value.get 64) stackReg
  have di : a[14].get 64 = fr.rsp + 712 := (congrArg (Value.get 64) dstReg).trans dst
  have q : a[15].get 64 = fr.rsp + 616 := congrArg (Value.get 64) ready.orderPtr
  have transition : ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10132a, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = copyState m fr.rsp ∧
      Atom.All Extracted.programImage out.values out.store (Fn100ea0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values := by
    refine ⟨?_, .done ?run, ?tag, ?memory, ?regs, ?widths⟩
    case run =>
      unfold Program.step
      cfg_eval
      simp only [sp, di, q, Lift.reduceAddOffset, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.sub_add_cancel]
      segment_words [bx, r12, r13, r14, r15, bp, ret, retLow, and_true]
      simp (disch := slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l10132a x hx))) only [ite_eq_left]
      rfl
    case tag => rfl
    case memory => rfl
    case regs => exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ft, fc, trivial⟩
    case widths =>
      rintro ⟨i, hi⟩ member
      have w := ready.widths ⟨i, hi⟩ member
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
  obtain ⟨out, run, tag, mem, regs, widths⟩ := transition
  refine ⟨out, run, tag, regs, widths, ?_⟩
  rw [mem, dst]
  have wf : RamWriteFrame m (copyState m fr.rsp) [⟨(fr.rsp + 712).toNat, 72⟩] := by
    dsimp only [copyState]
    slot_state region
  have total : RamWriteFrame fr.original (copyState m fr.rsp) [fr.region, ⟨(fr.rsp + 712).toNat, 72⟩] := by
    refine ((RamWriteFrame.refl fr.original _).trans ready.writes ?_).trans wf ?_
    · intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  exact ⟨total, memLoad_memStore_same _ _ _ (by decide) (by decide),
    stateBytes depth limit (upper.readable.of_frame wf) ready.bytes⟩

end K256.Proofs.Signing.Nonce.Initialize
