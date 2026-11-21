import K256.Proofs.Signing.Nonce.Fill.Memory
import K256.Proofs.Signing.Nonce.Initialize.Update
import K256.Proofs.Verify.LIR.Fn100a40
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

private def emptyChild (fr : Activation) (a : Registers) (n : Ram) : Activation :=
  {fr with
    rsp := fr.rsp - 240, original := n, ret := 0x100afb,
    rdi := fr.rdi + 8, rsi := 8, rdx := 0, rcx := a[1].get 64,
    r8 := a[8].get 64, r9 := a[9].get 64, rbx := a[3].get 64,
    rbp := a[5].get 64, r12 := a[12].get 64, r13 := a[13].get 64,
    r14 := a[14].get 64, r15 := a[15].get 64}

private abbrev pushed (fr : Activation) (m : Ram) :=
  memStore m (fr.rsp - 240) (0x100afb : BitVec 64)

private def updateRegions (fr : Activation) : List MemoryRegion :=
  [⟨fr.low.toNat,(sp fr).toNat - fr.low.toNat⟩,⟨(fr.rdi+8).toNat,64⟩]

private theorem pushFrame {fr : Activation} {m : Ram} (env : Environment fr) :
    RamWriteFrame m (pushed fr m) [⟨(fr.rsp-240).toNat,8⟩] := by
  apply (RamWriteFrame.refl _ _).memStore
  refine ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _,?_⟩
  have := env.limit
  rw [env.subNat 240 (by decide)]
  omega

private theorem childArgs {fr : Activation} {a : Registers} {m : Ram} {s : State}
    (env : Environment fr) (g : Generated fr s a m) :
    let n := pushed fr m
    let child := emptyChild fr a n
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l100aef,a,m⟩ =
        .call ⟨.l103f30,b,n⟩ (Verify.resumeAt .l100afb 0x100afb) ∧
      Atom.All Extracted.programImage b n (Fn103f30.frameAt .l103f30 child) := by
  dsimp only
  have stack := g.toFrame.stack
  have atoms := g.atoms
  simp only [Fn100a40.frameAt,Fn100a40.frameAtG1,Atom.All,Atom.Holds] at atoms
  obtain ⟨rsp,df,mx,ft,fc,_,_,_,_,_,_,_,_,_,_,_,_,_,_,align,rd0,val0,_,_,rd2,val2,_,_,gap,_⟩ := atoms
  have ptr : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have dep := env.depth
  have lim := env.limit
  have sub := env.subNat
  have bottom := sub 2160 (by decide)
  have childAddr := sub 240 (by decide)
  have wf := pushFrame (m := m) env
  have pack (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) :
      a[i] = ⟨64,a[i].get 64⟩ := by
    have h := g.widths i hi
    generalize a[i] = v at *
    cases v
    cases h
    rfl
  have wr : Writable Extracted.programImage m (fr.rsp - 240) 8 := by
    apply stack.sub <;> simp only [bottom,childAddr,BitVec.reduceToNat] <;> omega
  have stored : StoreOk Extracted.programImage m (fr.rsp - 240) 8 0x100af6 5 := by
    slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l100aef x hx))
  have rs : sp fr - 8 = fr.rsp - 240 := by unfold sp; bv_omega
  have ctx : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l100aef,a,m⟩ =
        .call ⟨.l103f30,b,pushed fr m⟩ (Verify.resumeAt .l100afb 0x100afb) ∧
      Atom.All Extracted.programImage b (pushed fr m)
        ((Fn103f30.frameAt .l103f30 (emptyChild fr a (pushed fr m))).take 17) := by
    refine ⟨?_,?step,?args⟩
    case step =>
      cfg_eval
      simp only [ptr,rs]
      simp (disch := slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l100aef x hx))) only [ite_eq_left]
      rfl
    case args =>
      simp only [Fn103f30.frameAt,Fn103f30.frameAtG4,List.take_succ_cons,List.take_zero,
        Atom.All,Atom.Holds,emptyChild]
      exact ⟨rfl,df,pack 1 (by decide),rfl,pack 3 (by decide),pack 5 (by decide),rfl,
        g.rdi,pack 8 (by decide),pack 9 (by decide),pack 12 (by decide),pack 13 (by decide),
        pack 14 (by decide),pack 15 (by decide),mx,ft,fc,trivial⟩
  obtain ⟨b,run,regs⟩ := ctx
  refine ⟨b,run,?_⟩
  let atoms' := Fn103f30.frameAt .l103f30 (emptyChild fr a (pushed fr m))
  change Atom.All _ _ _ atoms'
  rw [← List.take_append_drop 17 atoms',Atom.all_append]
  refine ⟨regs,?_⟩
  have keep (q : BitVec 64) (hq : 0x203dd0 ≤ q.toNat ∧ q.toNat ≤ 0x203e20) :
      memLoad (pushed fr m) q 64 = memLoad m q 64 := by
    apply wf.memLoad_eq
    change 0x204698 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at gap
    simp only [Outside,List.mem_singleton,forall_eq,childAddr,BitVec.reduceToNat,Nat.reduceDiv]
    omega
  change Readable _ (fr.rsp - 240) 8 ∧ _
  refine ⟨wr.readable.of_frame wf,memLoad_memStore_same _ _ _ (by decide) (by decide),
    by change (0x100afb : BitVec 64).toNat < 2^32; decide,?_,?_,?_,rd0.of_frame wf,(keep _ (by decide)).trans val0,rd2.of_frame wf,
    (keep _ (by decide)).trans val2,?_,trivial⟩
  · change Writable _ _ (fr.rsp - 240 - 1920) 1920
    rw [show fr.rsp - 240 - 1920 = fr.rsp - 2160 by bv_omega]
    exact (stack.of_frame wf).sub (Nat.le_refl _) (by omega)
  · change fr.low.toNat + 1920 ≤ (fr.rsp - 240).toNat
    rw [env.low,bottom,childAddr]; change fr.rsp.toNat - 2160 + 1920 ≤ fr.rsp.toNat - 240; omega
  · change (fr.rsp - 240).toNat % 16 = 8
    change fr.rsp.toNat % 16 = 8 at align
    rw [childAddr]; change (fr.rsp.toNat - 240) % 16 = 8; omega
  · change 0x204598 ≤ (fr.rsp - 240).toNat ∨ (fr.rsp - 240).toNat ≤ 0x203dd0
    change 0x204698 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at gap
    simp only [childAddr, BitVec.reduceToNat]; omega

theorem advance {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (g : Generated fr state a m) :
    ∃ b n, Reaches .l100aef a m .l100afb b n ∧ Updated fr state b n := by
  let n := pushed fr m
  let child := emptyChild fr a n
  obtain ⟨b,push,entry⟩ := childArgs env g
  have pushedFrame := pushFrame (m := m) env
  have dep := env.depth
  have lim := env.limit
  have bottom : fr.low.toNat = fr.rsp.toNat - 2160 := by rw [env.low,env.subNat 2160 (by decide)]; rfl
  have sp' : (sp fr).toNat = fr.rsp.toNat - 232 := env.subNat 232 (by decide)
  have cs : (fr.rsp - 240).toNat = fr.rsp.toNat - 240 := env.subNat 240 (by decide)
  have dp : fr.rsi.toNat = fr.rsp.toNat + 392 := env.dst ▸ env.addNat 392 (by decide)
  have gp : (fr.rdi+8).toNat = fr.rsp.toNat + 704 := by
    rw [show fr.rdi + 8 = fr.rsp + 704 by rw [env.gen]; bv_omega]
    exact env.addNat 704 (by decide)
  have contained : RegionsWithin (updateRegions fr) (regions fr) := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · exact ⟨fr.region,List.mem_cons_self,Nat.le_refl _,
        by change fr.low.toNat + ((sp fr).toNat - fr.low.toNat) ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat); omega⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_,by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Nat.le_refl _,Nat.le_refl _⟩
  have staged : RamWriteFrame m n (updateRegions fr) := (RamWriteFrame.refl _ _).trans pushedFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_,?_⟩ <;>
      simp only [bottom,sp',cs] <;> omega)
  have image := g.toFrame.imageAfter env (g.writes.trans staged contained)
  have initState : StateAt n child.rdi (Drbg.updateValue state) := by
    apply stateAfter pushedFrame _ g.stateAt
    simp only [Outside,List.mem_singleton,forall_eq,gp,cs]; omega
  have stateWritable : Writable Extracted.programImage n child.rdi 64 := by
    apply ((env.window.of_frame g.writes).of_frame staged).sub <;>
      change _ ≤ _ <;> dsimp only [child,emptyChild] <;> omega
  have floor : child.low = child.rsp - 1920 := by
    change fr.low = fr.rsp - 240 - 1920
    rw [env.low]; bv_omega
  have csp : child.rsp.toNat = fr.rsp.toNat - 240 := cs
  have cdi : child.rdi.toNat = fr.rsp.toNat + 704 := gp
  obtain ⟨out,run,tag,done_,widths,writes,bytes⟩ :=
    Initialize.update (input := .empty) entry image (by change 1920 ≤ child.rsp.toNat; omega)
      floor (by change child.rsp.toNat + 8 < 2^32; omega)
      (by change child.rdi.toNat + 64 < 2^32; omega) (Or.inr (by change child.rsp.toNat + 8 ≤ child.rdi.toNat; omega))
      stateWritable rfl initState
  have total : RamWriteFrame m out.store (updateRegions fr) := staged.trans writes (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · refine ⟨_,List.mem_cons_self,Nat.le_refl _,?_⟩
      change fr.low.toNat + ((fr.rsp - 240).toNat - fr.low.toNat) ≤ fr.low.toNat + ((sp fr).toNat - fr.low.toNat)
      omega
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩)
  have keep (k : BitVec 64) (w : Nat) (hk : k.toNat ≤ 232) (hw : w ≤ 64) :
      memLoad out.store (fr.rsp-k) w = memLoad m (fr.rsp-k) w := by
    apply total.memLoad_eq
    have pos := env.subNat k (by omega)
    refine ⟨by omega,fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · right; change fr.low.toNat + ((sp fr).toNat - fr.low.toNat) ≤ _; omega
    · obtain rfl := List.mem_singleton.mp h
      left; change _ ≤ (fr.rdi+8).toNat; omega
  have atoms := g.atoms
  obtain ⟨_,df,mx,ft,fc,_⟩ := atoms
  simp only [Fn103f30.doneAt,Atom.All,Atom.Holds,emptyChild] at done_
  obtain ⟨rsp,dir,bx,bp,r12,r13,r14,r15,x,t,y,_⟩ := done_
  have newSp : out.values[4] = ⟨64,sp fr⟩ := rsp.trans (congrArg (Value.mk 64)
    (show fr.rsp - 240 + 8 = sp fr by unfold sp; bv_omega))
  refine ⟨out.values,out.store,Verify.reachesOfCall push run tag,⟨g.toFrame.afterCall env total contained
    ?_ newSp ?_ ?_,?_,?_⟩⟩
  · intro k w hk
    rcases hk with ⟨rfl,h⟩ | ⟨rfl,rfl⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      exact keep k 64 (by omega) (by decide)
    · exact keep 176 32 (by decide) (by decide)
  · rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact dir.trans df.symm
    · exact x.trans mx.symm
    · exact t.trans ft.symm
    · exact y.trans fc.symm
  · rintro ⟨i,hi⟩ h
    simp only [Activation.entryNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact widths 1 (by decide) | exact widths 2 (by decide) | exact widths 6 (by decide) |
        exact widths 7 (by decide) | exact widths 8 (by decide) | exact widths 9 (by decide) | exact congrArg Value.width bx | exact congrArg Value.width bp |
        exact congrArg Value.width r12 | exact congrArg Value.width r13 | exact congrArg Value.width r14 |
        exact congrArg Value.width r15 | exact congrArg Value.width rsp
  · rw [Drbg.retry_eq]
    exact bytes
  · apply UpdateV.Finalize.bytesAfter total _ g.bytes
    refine ⟨by omega,fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · right; change fr.low.toNat + ((sp fr).toNat - fr.low.toNat) ≤ _; omega
    · obtain rfl := List.mem_singleton.mp h
      left; change _ ≤ (fr.rdi+8).toNat; omega

end K256.Proofs.Signing.Nonce.Fill
