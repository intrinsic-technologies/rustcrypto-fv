import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Negate
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.State
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Stores
import K256.Proofs.Verify.Core.Serializer.Memory
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Prepare.Bases.Negate (storeFour)

def negateWrites (base : BitVec 64) (off : Nat) : List MemoryRegion :=
  [scratch base 56, ⟨base.toNat + 56,32⟩, ⟨base.toNat + off,32⟩]

theorem negateWritesWithin {sp : BitVec 64} {off : Nat}
    (room : 1368 ≤ sp.toNat) (fits : off + 32 ≤ 696) :
    RegionsWithin (negateWrites (frameSp sp) off) [scratch sp 1368] := by
  have base : (frameSp sp).toNat = sp.toNat - 696 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  intro r hr
  simp only [negateWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  refine ⟨_,.head _,?_⟩
  rcases hr with rfl|rfl|rfl <;> dsimp only [scratch] <;> omega

theorem SavedFrame.preserve {a b c : Registers} {n o : Ram} {sp tables : BitVec 64}
    (s : SavedFrame a sp tables b n) (rsp : c[4] = ⟨64,frameSp sp⟩)
    (keep : KeptForMagnitude b c) (saved : ∀ off : BitVec 64, 8 ≤ off.toNat → off.toNat ≤ 48 →
      memLoad o (sp - off) 64 = memLoad n (sp - off) 64) : SavedFrame a sp tables c o := by
  have member (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15] ∨ i.val ∈ [22,39,50,51]) :
      i.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega
  exact ⟨rsp,(keep 3 (by decide)).trans s.tableBase,
    fun i h => (congrArg Value.width (keep i (member i (.inl h)))).trans (s.widths i h),
    fun i h => (keep i (member i (.inr h))).trans (s.control i h),
    (saved 48 (by decide) (by decide)).trans s.rbx, (saved 40 (by decide) (by decide)).trans s.r12,
    (saved 32 (by decide) (by decide)).trans s.r13, (saved 24 (by decide) (by decide)).trans s.r14,
    (saved 16 (by decide) (by decide)).trans s.r15, (saved 8 (by decide) (by decide)).trans s.rbp⟩

theorem negateStaged {a b c : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {x off : Nat} {site resume : Label} {ret : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (s : SplitFrame a m sp src tables digits b n)
    (lo : 88 ≤ off) (hi : off + 32 ≤ 0x288) (small : ret.toNat < 2^32)
    (bound : x < domain.n)
    (widths : ParseSignature.ArgumentWidths c) (keep : KeptForMagnitude b c)
    (rsp : c[4] = ⟨64,frameSp sp - 8⟩)
    (di : c[7].get 64 = frameSp sp + BitVec.ofNat 64 off) (si : c[6].get 64 = frameSp sp + 56)
    (dx : c[2].get 64 = 0x2021a0)
    (call : program.runBlock (dialect Extracted.programImage) ⟨site,b,n⟩ =
      .call ⟨.l110b80,c,memStore (storeFour n (frameSp sp + 56) (scalarWords x)) (frameSp sp - 8) ret⟩
        (callResume resume ret)) :
    ∃ d o, Reaches site b n resume d o ∧ d[4] = ⟨64,frameSp sp⟩ ∧
      KeptForMagnitude b d ∧ ParseSignature.ArgumentWidths d ∧
      RamWriteFrame n o (negateWrites (frameSp sp) off) ∧
      WordsAt o (frameSp sp + BitVec.ofNat 64 off) 64 (scalarWords (if x = 0 then 0 else domain.n - x)) := by
  let base := frameSp sp
  let stage := storeFour n (base + 56) (scalarWords x)
  let pushed := memStore stage (base - 8) ret
  let dst := base + BitVec.ofNat 64 off
  let rs := negateWrites base off
  have room := entry.room
  have limit := entry.returnSlot.low
  have bn : base.toNat = sp.toNat - 696 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have pn : (base - 8).toNat = base.toNat - 8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ base.toNat; omega))
  have sn : (base + 56).toNat = base.toNat + 56 := by rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by change base.toNat + 56 < 2^64; omega)]; rfl
  have dn : dst.toNat = base.toNat + off := by
    simp only [dst,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega),Nat.mod_eq_of_lt (by omega)]
  have st : RamWriteFrame n stage rs :=
    Serializer.storeWords_frame _ (.refl ..) ⟨_,.tail _ (.head _),by dsimp only; omega,
      by dsimp only; omega,by omega⟩
  have pushedFrame : RamWriteFrame n pushed rs :=
    st.memStore ret ⟨_,.head _,by change base.toNat - 56 ≤ _; omega,
      by change _ ≤ base.toNat - 56 + 56; omega, by change (base-8).toNat + 8 ≤ _; omega⟩
  have bot : (sp - (1368 : BitVec 64)).toNat = sp.toNat - 1368 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have whole : RamWriteFrame m pushed [scratch sp 0x558] :=
    s.frame.trans pushedFrame (negateWritesWithin room (by omega))
  have win : Writable Extracted.programImage pushed (sp - 1368) 1368 := entry.stack.of_frame whole
  have tag : memLoad pushed (base-8) 64 = ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have dkeep (i : Fin Reg.count) (h : i.val ∈ [22,39,50,51]) : c[i] = a[i] :=
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans (s.control i h)
  have atoms : RoutineEntry c pushed (base-8) 48 := by
    refine ⟨rsp,?_,(dkeep 22 (by decide)).trans entry.df,
      (congrArg Value.width (dkeep 39 (by decide))).trans entry.mxcsr,
      (congrArg Value.width (dkeep 50 (by decide))).trans entry.ftw,
      (congrArg Value.width (dkeep 51 (by decide))).trans entry.fcw,?_,by omega,?_,?_,tag ▸ small,
      Recode.imageFromFrame entry whole⟩
    · intro i h
      exact (congrArg Value.width (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega))).trans (s.widths i h)
    · have := entry.aligned
      omega
    · have step : (base-8-BitVec.ofNat 64 48).toNat = (base-8).toNat - 48 :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 48 ≤ (base-8).toNat; omega))
      apply win.sub <;> omega
    · apply win.readable.sub <;> omega
  have raw : WordsAt stage (base + 56) 64 (scalarWords x) :=
    Serializer.storeWords_wordsAt n (base+56) (scalarWords x) (by omega)
  have input : WordsAt pushed (base + 56) 64 (scalarWords x) :=
    raw.write_apart _ ret (RangeApart.of_toNat (by change (base-8).toNat + 8 ≤ _; omega)
      (by change (base+56).toNat + 32 ≤ _; omega) (.inl (by change (base-8).toNat + 8 ≤ _; omega)))
  obtain ⟨out,run,post,words,args⟩ := negateScalar (src := base+56) (dst := dst) atoms widths di si
    (win.readable.sub (by omega) (by omega)) (win.sub (by omega) (by omega))
    (by omega) (by omega) (.inr (by omega)) dx bound input
  refine ⟨_,_,reachesCall call run (post.tag.trans (congrArg (fun r => some (Value.mk 64 r)) tag)),
    post.rsp.trans (by rw [BitVec.sub_add_cancel]), fun i h => (post.saved i h).trans (keep i h),
    args,pushedFrame.trans post.frame ?_,words⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,.head _,by dsimp only [scratch]; omega,by dsimp only [scratch]; omega⟩
  · exact ⟨_,.tail _ (.tail _ (.head _)), by dsimp only; omega, by dsimp only; omega⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
