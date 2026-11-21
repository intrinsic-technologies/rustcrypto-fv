import K256.Proofs.Verify.Core.Lincomb.Loop.Initialize.Measure.Arguments
import K256.Proofs.Verify.Core.Lincomb.Loop.Initialize.Measure.Prefix
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Verify.Core.Lincomb.Loop.State
import K256.Proofs.Verify.Core.Lincomb.Loop.Length

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

abbrev headerMaximum (m : Ram) (dataPtr : BitVec 64) :=
  max (max (max (memLoad m (dataPtr + 0x780) 64).toNat
    (memLoad m (dataPtr + 0x890) 64).toNat) (memLoad m (dataPtr + 0x1120) 64).toNat)
    (memLoad m (dataPtr + 0x1230) 64).toNat

theorem measureFresh {a : Registers} {m : Ram} {sp dst iterator dataPtr : BitVec 64}
    (entry : RoutineEntry a m sp 0x478)
    (di : a[7].get 64 = dst) (si : a[6].get 64 = iterator)
    (first : memLoad m iterator 64 = dataPtr)
    (last : memLoad m (iterator + 8) 64 = dataPtr + 0x1340)
    (unset : memLoad m (iterator + 16) 64 = 0 ∧ memLoad m (iterator + 64) 64 = 0)
    (nonzero : dataPtr ≠ 0)
    (iterRead : Readable m iterator 112) (tableRead : Readable m dataPtr 0x1340)
    (iterApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] iterator 112)
    (dataApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] dataPtr 0x1340) :
    ∃ b n, Reaches .l1100a0 a m .l1101de b n ∧ SavedFrame a m sp dst b n ∧
      (b[0].get 64).toNat = headerMaximum m dataPtr ∧ b[13].get 64 = 0 ∧
      b[14].get 64 = dataPtr ∧ b[5] = ⟨64, dataPtr + 0x1340⟩ ∧
      b[15].get 64 = iterator ∧ memLoad n (baseSp sp) 64 = 0 := by
  obtain ⟨b, n, initialRoute, saved, front, nextTable, tableEnd, iter, rbx, r12, back, last', unset'⟩ :=
    freshPrefix entry di si first last unset iterRead iterApart
  obtain ⟨c, t, d, u, prepare, call, args⟩ :=
    lengthArguments entry saved front nextTable tableEnd iter rbx r12 back last' unset' nonzero
      tableRead dataApart
  let child := baseSp sp - 8
  have room := entry.room
  have low := entry.returnSlot.low
  have pos : child.toNat = sp.toNat - 0x1e0 := by
    change (sp - 0x1d8 - 8).toNat = _
    rw [BitVec.sub_sub]
    exact Recode.subNat (by change 0x1e0 ≤ sp.toNat; omega)
  have callerFrame := args.saved.frame
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : d[i] = a[i] := by
    have ne : 4 ≠ i.val := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    simpa only [Fin.getElem_fin, Vector.getElem_set_ne _ _ ne] using args.saved.control i hi
  have childEntry : RoutineEntry d u child 8 := by
    refine ⟨args.rsp, ?_, (control 22 (by decide)).trans entry.df, ?_, ?_, ?_, ?_, by omega,
      ?_, ?_, ?_, Recode.imageFromFrame entry callerFrame⟩
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact args.rbx
      · exact congrArg Value.width args.tableEnd
      · exact args.r12
      · exact congrArg Value.width args.front
      · exact congrArg Value.width args.nextTable
      · exact congrArg Value.width args.iter
    · exact (congrArg Value.width (control 39 (by decide))).trans entry.mxcsr
    · exact (congrArg Value.width (control 50 (by decide))).trans entry.ftw
    · exact (congrArg Value.width (control 51 (by decide))).trans entry.fcw
    · rw [pos]
      have := entry.aligned
      omega
    · rw [show child - BitVec.ofNat 64 8 = sp - 0x1e8 by dsimp only [child, baseSp]; bv_omega]
      exact (Recode.stackSlot entry (by decide) (by decide)).of_frame callerFrame
    · rw [show child = sp - 0x1e0 by dsimp only [child, baseSp]; bv_omega]
      exact ((Recode.stackSlot entry (by decide) (by decide)).of_frame callerFrame).readable
    · change (memLoad u (baseSp sp - 8) 64).toNat < _
      rw [args.tag]
      decide
  have iterPos : (baseSp sp + 0x58).toNat = sp.toNat - 0x180 := by
    rw [show baseSp sp + 0x58 = sp - 0x180 by unfold baseSp; bv_omega]
    exact Recode.subNat (by change 0x180 ≤ sp.toNat; omega)
  have readLocal : Readable u (baseSp sp + 0x58) 112 := by
    rw [show baseSp sp + 0x58 = sp - 0x180 by unfold baseSp; bv_omega]
    exact ((Recode.stackSlot entry (by decide) (by decide)).of_frame callerFrame).readable
  have outsideLocal : Outside [scratch child 8] (baseSp sp + 0x58) 112 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by simp only [scratch]; omega)
  have outsideTable : Outside [scratch sp 0x478] dataPtr 0x1340 :=
    ⟨dataApart.1, fun r hr => dataApart.2 r (by obtain rfl := List.mem_singleton.mp hr; exact .head _)⟩
  have outsideChild : Outside [scratch child 8] dataPtr 0x1340 := by
    refine ⟨outsideTable.1, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    rcases outsideTable.2 _ (.head _) with h | h
    · exact Or.inl (by simp only [scratch] at h ⊢; omega)
    · exact Or.inr (by simp only [scratch] at h ⊢; omega)
  obtain ⟨out, exec, post, maximum⟩ := maximumLength childEntry args.di args.si nonzero readLocal
    (tableRead.of_frame callerFrame) outsideLocal outsideChild args.first
    (by rw [BitVec.add_assoc]; exact args.last)
    (by rw [BitVec.add_assoc]; exact args.table)
    (by rw [BitVec.add_assoc]; exact args.digits)
    (by rw [BitVec.add_assoc]; exact args.index)
    (by rw [BitVec.add_assoc]; exact args.limit)
    (by rw [BitVec.add_assoc]; exact args.unset)
  have tag := post.tag
  change out.tag = some ⟨64, memLoad u (baseSp sp - 8) 64⟩ at tag
  rw [args.tag] at tag
  have preserve (off : BitVec 64) (bound : off.toNat ≤ 0x1d8) :
      memLoad out.store (sp - off) 64 = memLoad u (sp - off) 64 := by
    apply post.frame.memLoad_eq
    have addr := Recode.subNat (show off.toNat ≤ sp.toNat by omega)
    refine ⟨by change (sp - off).toNat + 8 ≤ 2^64; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by simp only [scratch]; omega)
  have headers (off : BitVec 64) (fits : off.toNat + 8 ≤ 0x1340) :
      memLoad u (dataPtr + off) 64 = memLoad m (dataPtr + off) 64 := by
    have addr : (dataPtr + off).toNat = dataPtr.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := tableRead.low; omega)]
    apply callerFrame.memLoad_eq
    exact Generate.Generator.Affine.outside_subregion outsideTable (by omega)
      (by change (dataPtr + off).toNat + 8 ≤ _; omega)
  rw [headers 0x780 (by decide), headers 0x890 (by decide), headers 0x1120 (by decide),
    headers 0x1230 (by decide)] at maximum
  refine ⟨out.values, out.store, initialRoute.trans (prepare.trans (reachesCall call exec tag)), ?_,
    maximum, congrArg (Value.get 64) ((post.saved 13 (by decide)).trans args.front),
    congrArg (Value.get 64) ((post.saved 14 (by decide)).trans args.nextTable),
    (post.saved 5 (by decide)).trans args.tableEnd,
    congrArg (Value.get 64) ((post.saved 15 (by decide)).trans args.iter),
    (preserve 0x1d8 (by decide)).trans args.back⟩
  refine ⟨?_, ?_, (preserve _ (by decide)).trans args.saved.rbx,
    (preserve _ (by decide)).trans args.saved.r12, (preserve _ (by decide)).trans args.saved.r13,
    (preserve _ (by decide)).trans args.saved.r14, (preserve _ (by decide)).trans args.saved.r15,
    (preserve _ (by decide)).trans args.saved.rbp, ?_, ?_⟩
  · simpa only [child, BitVec.sub_add_cancel] using post.rsp
  · have addr : baseSp sp + 0xd0 = sp - 0x108 := by unfold baseSp; bv_omega
    rw [addr]
    exact (preserve _ (by decide)).trans (by simpa only [addr] using args.saved.dest)
  · intro i hi
    exact (post.saved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (control i hi)
  · apply callerFrame.trans post.frame
    intro r hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    exact Recode.scratchContains (child := child) (size := 8) (sp := sp) (depth := 0x478) (by omega) (by omega) (by omega) r hr

end K256.Proofs.Verify.Core.Lincomb.Loop
