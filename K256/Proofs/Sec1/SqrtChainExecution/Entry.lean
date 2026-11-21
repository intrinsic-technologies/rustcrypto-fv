import K256.Proofs.Sec1.SqrtChainExecution.Stages

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field
open K256.Proofs.Sec1.Sqrt

private theorem limbs_eta (a : Limbs) : #v[a[0],a[1],a[2],a[3],a[4]] = a := by
  apply Vector.ext
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 1500000 in
theorem enter {code : CodeMap} {fr : Activation} {a : Limbs} {args : Values Value Reg.count}
    (g : Geometry code fr) (frame : Atom.All code args fr.original (LIR.Fn115950.frameAt .l115950 fr))
    (input : WordsAt fr.original fr.rsi 64 a) (rd : Readable fr.original fr.rsi 40)
    (wr : Writable code fr.original fr.rdi 41) :
    ∃ b m, Parser.Reaches code .l115950 args fr.original productPC[0] b m ∧
      ProductState code fr a 0 b m := by
  let old : Limbs := Vector.ofFn fun i => memLoad fr.original (wordAddr fr.rdi 64 i.val) 64
  have oldAt : WordsAt fr.original fr.rdi 64 old := by
    intro i hi
    simp only [old, Vector.getElem_ofFn]
  let next : Block Entry.Op Entry.Label Entry.signature 1 13 := .terminate (.ret #v[0])
  let p : Entry.EntryParams := ⟨fr.rdi,fr.rsp-440,a[0],a[1],a[2],a[3],a[4],
    old[0],old[1],old[2],old[3],old[4],a,old⟩
  let entry : LIR.lifted.Location := ⟨.l115950,args,fr.original⟩
  have rel : (Entry.layout next).Rel code (fr,fr.rdi) (Entry.entryLocation next p) entry := by
    refine ⟨rfl, ⟨p,rfl,rfl,(Atom.all_append _ _).2 ⟨frame,?_⟩⟩,RamWriteFrame.refl _ _⟩
    have dst := frame.2.2.2.2.2.2.2.1
    change args[7] = ⟨64,fr.rdi⟩ at dst
    refine ⟨dst,dst,rfl,rfl,?_,rd,?_,wr,g.sourceStack,g.destStack,g.destCode,g.sourceCode,g.stackCode,trivial⟩
    · exact (limbs_eta a).symm ▸ input
    · exact (limbs_eta old).symm ▸ oldAt
  obtain ⟨⟨lab,b,m⟩, reaches, after⟩ := Entry.firstSquare next (stack := []) p rel
  obtain ⟨hl,⟨q,hq,hstore,atoms⟩,written⟩ := after
  change lab = .l1159a4 at hl
  subst lab
  change Atom.All code b m (LIR.Fn115950.frameAt .l1159a4 fr ++ (Entry.core next).atoms .afterSquare fr.rdi fr q) at atoms
  obtain ⟨hf,rest⟩ := (Atom.all_append _ _).1 atoms
  change Atom.All code b m ([.fact (fr.rdi = fr.rdi), .gpr 0 q.rax, .words (fr.rsp - 400) 64 q.st.w] ++
    Entry.sqrtBase fr.rdi fr q.out q.sp #v[q.a0,q.a1,q.a2,q.a3,q.a4] #v[q.o0,q.o1,q.o2,q.o3,q.o4]) at rest
  obtain ⟨_,_,sq,_,_,source,sourceRead,_,destWrite,_⟩ := rest
  change (⟨#v[a[0],a[1],a[2],a[3],a[4]],squareWords #v[a[0],a[1],a[2],a[3],a[4]]⟩ : Entry.Store) = q.st at hstore
  have qwords := congrArg Entry.Store.w hstore
  change squareWords #v[a[0],a[1],a[2],a[3],a[4]] = q.st.w at qwords
  have qw : squareWords a = q.st.w := (congrArg squareWords (limbs_eta a)).symm.trans qwords
  change WordsAt m (fr.rsp - 400) 64 q.st.w at sq
  have squared : WordsAt m (fr.rsp - 400) 64 (squareWords a) := Eq.mp (congrArg (WordsAt m (fr.rsp - 400) 64) qw.symm) sq
  change #v[fr.rsp-440+40, fr.rdi, fr.rsp-440, a[0], a[1], a[2], a[3], a[4],
    old[0],old[1],old[2],old[3],old[4]] =
    #v[q.rax,q.out,q.sp,q.a0,q.a1,q.a2,q.a3,q.a4,q.o0,q.o1,q.o2,q.o3,q.o4] at hq
  have sourceEq : #v[q.a0,q.a1,q.a2,q.a3,q.a4] = a :=
    (congrArg (fun v : Vector Word 13 => #v[v[3],v[4],v[5],v[6],v[7]]) hq).symm.trans (limbs_eta a)
  have wide : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,41⟩] := by
    apply (RamWriteFrame.refl _ _).trans written
    intro r hr
    change r ∈ [fr.region, ⟨fr.rdi.toNat,40⟩] at hr
    rcases List.mem_cons.mp hr with rfl | ht
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · obtain rfl := List.mem_singleton.mp ht
      exact ⟨⟨fr.rdi.toNat,41⟩, by simp, Nat.le_refl _, Nat.le_succ _⟩
  refine ⟨b,m,reaches,⟨hf,trivial,?_,(fun h => False.elim ((by decide : ¬ (0:Nat) ∈ [7,8,9]) h)),?_,sourceRead,destWrite,?_,wide⟩⟩
  · change WordsAt m (fr.rsp - 400) 64 (chainWord squareWords mulWords a 1)
    rw [(chainWord_first squareWords mulWords a).2]
    exact squared
  · exact sourceEq ▸ source
  · intro i hi
    obtain ⟨i,hi'⟩ := i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    obtain ⟨_,_,h3,h5,h12,h13,h14,h15,_⟩ := hf
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact congrArg Value.width h3 | exact congrArg Value.width h5 |
        exact congrArg Value.width h12 | exact congrArg Value.width h13 |
        exact congrArg Value.width h14 | exact congrArg Value.width h15

end K256.Proofs.Sec1.SqrtChainExecution
