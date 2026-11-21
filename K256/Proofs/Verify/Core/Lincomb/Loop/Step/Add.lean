import K256.Proofs.Verify.Core.Lincomb.Loop.Add
import K256.Proofs.Verify.Core.Lincomb.Loop.Column
import K256.Proofs.Verify.Core.Lincomb.Loop.Packed
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR Standards.SECG.ECC
open Generate.Generator.Multiply (Projective)

private theorem packedCall {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (widths : ParseSignature.ArgumentWidths a)
    (slot : Writable Extracted.programImage m (sp-8) 8) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l110300,a,m⟩ =
      .call ⟨.l10a410,c,memStore m (sp-8) (0x110305 : BitVec 64)⟩ (callResume .l110305 0x110305) ∧
      c[4] = ⟨64,sp-8⟩ ∧ ParseSignature.ArgumentWidths c ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,6,7,12,13,14,15,22,39,50,51] → c[i] = a[i] := by
  have guard : StoreOk Extracted.programImage m (sp-8) 8 0x110300 5 := ParseSignature.storeOk_of_codeRange (off := 0) (len := 5) slot
    (fun v hv => Common.fnCode_subset_programImage v (code_l110300 v hv)) (by decide)
  refine ⟨?_,?run,?stack,?width,?keep⟩
  case run =>
    cfg_eval [rsp,guard]
    rfl
  case stack => rfl
  case width =>
    rintro ⟨i,hi⟩ h
    have w := widths ⟨i,hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact w
  case keep =>
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

local macro "reg_mem" : tactic => `(tactic|
  (simp only [List.mem_cons,List.not_mem_nil,or_false] at *; omega))

theorem packedAdd {a b packedRegs : Registers} {m n packedRam : Ram} {sp dst table : BitVec 64}
    {k : Nat} {value : Curve.Point} {j : Fin 4} {cur q : Projective}
    (entry : RoutineEntry a m sp 0x478) (state : Column a m sp dst table k value b n)
    (cursor : Cursor sp table j (j.val%2+1) b n) (packed : Packed (baseSp sp) q b packedRegs n packedRam)
    (left : cur.Stored n (baseSp sp + 0x130)) (r15 : b[15].width = 64) :
    ∃ c store, Reaches .l110300 packedRegs packedRam .l110305 c store ∧
      c[4] = ⟨64,baseSp sp⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → c[i] = b[i]) ∧
      (cur.add q).Stored store (baseSp sp+0x130) ∧
      RamWriteFrame n store (digitWrites (baseSp sp) ++
        [scratch (baseSp sp) 544, ⟨(baseSp sp+0x130).toNat,120⟩]) := by
  let s := baseSp sp
  let cs := s-8
  let push := memStore packedRam cs (0x110305 : BitVec 64)
  have room := entry.room
  have low := entry.returnSlot.low
  have align := entry.aligned
  have sn : s.toNat = sp.toNat-472 := Recode.subNat (by change 472 ≤ sp.toNat; omega)
  have cn : cs.toNat = s.toNat-8 := Recode.subNat (by change 8 ≤ s.toNat; omega)
  have bot : (sp-BitVec.ofNat 64 0x478).toNat = sp.toNat-1144 :=
    Recode.subNat (by exact room)
  have child : (cs-BitVec.ofNat 64 0x218).toNat = cs.toNat-536 :=
    Recode.subNat (by change 536 ≤ cs.toNat; omega)
  have off {i : Nat} (h : i ≤ 472) : (s + BitVec.ofNat 64 i).toNat = s.toNat+i :=
    toNat_add_ofNat _ _ (by omega)
  have src : (s+0x58).toNat = s.toNat+88 := off (by decide)
  have tmp : (s+0xe0).toNat = s.toNat+224 := off (by decide)
  have dest : (s+0x130).toNat = s.toNat+304 := off (by decide)
  have wide := (entry.stack.of_frame state.frame).of_frame packed.frame
  have slot : Writable Extracted.programImage packedRam cs 8 := wide.sub (by omega) (by omega)
  obtain ⟨c,call,rsp,args,keep⟩ := packedCall (sp := s)
    (congrArg (Value.get 64) ((packed.keep 4 (by decide)).trans state.rsp)) packed.arguments slot
  have kept (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) : c[i] = b[i] :=
    (keep i (by reg_mem)).trans (packed.keep i (by reg_mem))
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) :=
    (kept i (by reg_mem)).trans (state.control i hi)
  have saved (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : c[i].width = 64 := by
    rw [kept i (by reg_mem)]
    rcases i with ⟨i,ih⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    exact congrArg Value.width cursor.count
    exact congrArg Value.width state.last
    exact congrArg Value.width cursor.component
    exact congrArg Value.width cursor.base
    exact congrArg Value.width cursor.next
    exact r15
  have pf : RamWriteFrame packedRam push [scratch s 544] := (RamWriteFrame.refl ..).memStore _
    ⟨_,.head _,by change s.toNat-544 ≤ cs.toNat ∧ cs.toNat+8 ≤ s.toNat-544+544 ∧ cs.toNat+8 ≤ 2^64; omega⟩
  have whole := (state.frame.trans packed.frame (by
    intro r hr
    refine ⟨_,.head _,?_⟩
    simp only [digitWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [scratch] <;> first | rw [src]; omega | rw [tmp]; omega)).trans pf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,.head _,by dsimp only [scratch]; omega⟩)
  have tag : memLoad push cs 64 = 0x110305 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have stack := wide.of_frame pf
  have ent : RoutineEntry c push cs 0x218 := ⟨rsp,saved,(control 22 (by decide)).trans entry.df,
    (congrArg Value.width (control 39 (by decide))).trans entry.mxcsr,
    (congrArg Value.width (control 50 (by decide))).trans entry.ftw,
    (congrArg Value.width (control 51 (by decide))).trans entry.fcw,by omega,by omega,
    stack.sub (by omega) (by omega),slot.readable.of_frame pf,by rw [tag]; decide,
    Recode.imageFromFrame entry whole⟩
  have away : Outside (digitWrites s) (s+0x130) 120 := by
    refine ⟨by omega,fun r hr => ?_⟩
    simp only [digitWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only <;> omega
  have safe {x : BitVec 64} (lo : s.toNat ≤ x.toNat) (hi : x.toNat+120 ≤ 2^64) :
      Outside [scratch s 544] x 120 :=
    ⟨hi, fun r hr => List.mem_singleton.mp hr ▸ Or.inr (by change s.toNat-544+544 ≤ x.toNat; omega)⟩
  obtain ⟨out,run,ret,stored,_⟩ := add (dst := s+0x130) (src := s+0x58) ent args
    (congrArg (Value.get 64) ((keep 7 (by decide)).trans packed.dst))
    (congrArg (Value.get 64) ((keep 6 (by decide)).trans packed.src))
    (stack.readable.sub (by omega) (by omega)) (stack.sub (by omega) (by omega))
    (by omega) (by omega) (Or.inr (by omega))
    ((left.of_frame packed.frame away).of_frame pf (safe (x := s+0x130) (by omega) (by omega)))
    (packed.point.of_frame pf (safe (x := s+0x58) (by omega) (by omega)))
  refine ⟨_,_,reachesCall call run (ret.tag.trans (congrArg (fun t => some (Value.mk 64 t)) tag)),
    ret.rsp.trans (by rw [show cs+8 = s from BitVec.sub_add_cancel ..]),fun i hi => (ret.saved i hi).trans (kept i hi),
    stored,?_⟩
  let regions := digitWrites s ++ [scratch s 544, ⟨(s+0x130).toNat,120⟩]
  have first : RamWriteFrame n packedRam regions := (RamWriteFrame.refl n regions).trans packed.frame
    (fun r hr => ⟨r,List.mem_append_left _ hr,Nat.le_refl _,Nat.le_refl _⟩)
  apply (first.trans pf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_append_right _ (.head _),Nat.le_refl _,Nat.le_refl _⟩)).trans ret.frame
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_append_right _ (.head _),by dsimp only [scratch]; omega⟩
  · exact ⟨_,List.mem_append_right _ (.tail _ (.head _)),Nat.le_refl _,Nat.le_refl _⟩

end K256.Proofs.Verify.Core.Lincomb.Loop
