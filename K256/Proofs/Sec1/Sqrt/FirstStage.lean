import K256.Proofs.Sec1.Sqrt.FirstProduct
import K256.Proofs.Sec1.SqrtChainExecution.ProductResume

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution

set_option maxHeartbeats 1000000 in
theorem firstProductCall {code : CodeMap} {fr : Activation} {a : Limbs}
    {args : Values Value Reg.count} {m : Ram} (geom : Geometry code fr)
    (s : ProductState code fr a 0 args m) :
    Ahead LIR.lifted code (fun l => CallTo (lifted := LIR.lifted) (fun child frame =>
      ProductCall code fr a 0 child 0x115e4d ∧ frame = Wrapper.callFrame .l115e4d 0x115e4d)
      (LIR.lifted.program.runBlock (dialect code) l)) ⟨.l1159a4, args, m⟩ := by
  let base := fr.rsp - 440
  let v := words a 1
  have hf := s.frame
  change Atom.All code args m (LIR.Fn115950.frameAt .l1159a4 fr) at hf
  obtain ⟨rsp, df, bx, _, _, _, _, _, mx, ftw, fcw, o, reg3, reg12, reg13, reg14, reg15, reg5,
    rd, ret, low, wr, room, al, _⟩ := hf
  change args[4] = ⟨64, base⟩ at rsp
  change args[3] = ⟨64, fr.rsi⟩ at bx
  change args[22] = ⟨1,0⟩ at df
  change args[39] = ⟨32, fr.mxcsr⟩ at mx
  change args[50] = ⟨16, fr.ftw⟩ at ftw
  change args[51] = ⟨16, fr.fcw⟩ at fcw
  change Readable m fr.rsp 8 at rd
  change Writable code m (fr.rsp - 552) 552 at wr
  change fr.low.toNat + 552 ≤ fr.rsp.toNat at room
  change fr.rsp.toNat % 16 = 8 at al
  have bound := rd.low
  have hb : base.toNat = fr.rsp.toNat - 440 := BitVec.toNat_sub_of_le (by change 440 ≤ fr.rsp.toNat; omega)
  have hb8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ base.toNat; omega)
  have hb112 : base - 112 = fr.rsp - 552 := by dsimp only [base]; rw [BitVec.sub_sub]; rfl
  have hnat : (fr.rsp - 552).toNat = fr.rsp.toNat - 552 :=
    BitVec.toNat_sub_of_le (by change 552 ≤ fr.rsp.toNat; omega)
  have hs : Writable code m (base - 8) 440 :=
    wr.sub (by rw [hb8, hb, hnat]; omega) (by rw [hb8, hb, hnat]; omega)
  have hcode := geom.stackCode
  have hsource := geom.sourceStack
  have h40 : base + 40 = fr.rsp - 400 := by dsimp only [base]; bv_omega
  have hbWords : WordsAt m (base + 40) 64 v := by rw [h40]; exact s.squared
  have h2 := (chainWord_step squareWords mulWords a 0).1
  change words a 2 = mulWords (words a 0) v at h2
  have hzero : words a 0 = a := (chainWord_first squareWords mulWords a).1
  rw [hzero] at h2
  have hx := firstMultiply (a := a) (b := v) (sp := base) (input := fr.rsi) (args := args)
    (by rw [rsp]; exact BitVec.setWidth_eq _) (by rw [bx]; exact BitVec.setWidth_eq _)
    hs s.sourceRead (by omega) (by omega) (by omega) (by omega) s.source hbWords
  obtain ⟨before, hjump, hx⟩ := hx
  refine ⟨before, hjump, ?_⟩
  cases he : LIR.lifted.program.runBlock (dialect code) before with
  | jump _ | returned _ | stuck => rw [he] at hx; exact hx.elim
  | call child frame =>
    rw [he] at hx
    change FirstCall m args base a v child frame at hx
    change CallTo (lifted := LIR.lifted) _ (LIR.lifted.program.runBlock (dialect code) before)
    rw [he]
    refine ⟨?_, hx.continuation⟩
    obtain ⟨w1,w2,w3,w5,w8,w9,w12,w13,w14,w15⟩ := hx.updatedWidths
    obtain ⟨hdf,hmx,hftw,hfcw⟩ := hx.saved
    have regWidth : ∀ i : Fin Reg.count, i.val ∈ LiftedSquare.volatile ++ [3,5,12,13,14,15,39,50,51] →
        (child.arguments[i.val]'i.isLt).width = (Reg.ofIndex i.val).width := by
      intro i hi
      have mx' := congrArg Value.width (hmx.trans mx)
      have ftw' := congrArg Value.width (hftw.trans ftw)
      have fcw' := congrArg Value.width (hfcw.trans fcw)
      rcases i with ⟨r,hr⟩
      change r ∈ [1,2,8,9,3,5,12,13,14,15,39,50,51] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact w1
      · exact w2
      · exact w8
      · exact w9
      · exact w3
      · exact w5
      · exact w12
      · exact w13
      · exact w14
      · exact w15
      · exact mx'
      · exact ftw'
      · exact fcw'
    have slot (k : Word) (hk : k.toNat ≤ 56) :
        memLoad child.store (fr.rsp-k) 64 = memLoad m (fr.rsp-k) 64 := by
      apply hx.writes.memLoad_eq
      have hn := BitVec.toNat_sub_of_le (x := fr.rsp) (y := k) (by rw [BitVec.le_def]; omega)
      refine ⟨?_,?_⟩
      · change (fr.rsp - k).toNat + 8 ≤ 2^64; omega
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        right
        change (base - 8).toNat + 368 ≤ (fr.rsp-k).toNat
        omega
    have work : Writable code m (fr.rsp - 552) 192 := wr.sub (Nat.le_refl _) (by omega)
    rw [← hb112] at work
    have hret : memLoad child.store fr.rsp 64 = memLoad m fr.rsp 64 := by
      simpa only [show fr.rsp - (0 : Word) = fr.rsp by bv_omega] using slot 0 (by decide)
    have stored (r : Value) (y : Word) (width : r.width = 64) (eqn : r.get 64 = y) :
        r = ⟨64,y⟩ := by
      obtain ⟨n,b⟩ := r
      change n = 64 at width
      subst n
      change b.setWidth 64 = y at eqn
      rw [BitVec.setWidth_eq] at eqn
      rw [eqn]
    have keep (j : Nat) (hj : j < Reg.count) (hne : 4 ≠ j) :
        (callerArgs child base)[j] = (squareArguments child hx.callee)[j] :=
      Vector.getElem_set_ne (by decide : 4 < Reg.count) hj hne
    refine ⟨?_, ?_, ?_, fun ne => (ne rfl).elim, fun ne => (ne rfl).elim, ?_,
      s.sourceRead.of_frame hx.writes, s.destWrite.of_frame hx.writes, ?_⟩
    · change LiftedSquare.Entry code child base 0x115e4d (words a 2)
      rw [h2]
      exact ⟨hx.callee, hx.rsp, hx.rsi, hx.rdi, hdf.trans df, regWidth,
        work.of_frame hx.writes,
        hx.returnSlot, by decide, by omega, by omega, by omega, hx.words⟩
    · change Atom.All code (callerArgs child base) child.store (LIR.Fn115950.frameAt .l115e4d fr)
      refine ⟨?_, ?_, ?_, ?_, ?_, (slot 56 (by decide)).trans o, (slot 48 (by decide)).trans reg3,
        (slot 40 (by decide)).trans reg12, (slot 32 (by decide)).trans reg13,
        (slot 24 (by decide)).trans reg14, (slot 16 (by decide)).trans reg15,
        (slot 8 (by decide)).trans reg5, rd.of_frame hx.writes, hret.trans ret, low,
        wr.of_frame hx.writes, room, al, trivial⟩
      · exact Vector.getElem_set_self ..
      · exact (keep 22 (by decide) (by decide)).trans (hdf.trans df)
      · exact (keep 39 (by decide) (by decide)).trans (hmx.trans mx)
      · exact (keep 50 (by decide) (by decide)).trans (hftw.trans ftw)
      · exact (keep 51 (by decide) (by decide)).trans (hfcw.trans fcw)
    · obtain ⟨a0,a1,a2,a3,a4⟩ := hx.inputSaved
      obtain ⟨p0,p1,p2,p3,p4⟩ := hx.outputSaved
      have hreg5 := stored _ _ w5 hx.rbp
      have hreg13 := stored _ _ w13 hx.r13
      have hreg12 := stored _ _ w12 hx.r12
      rw [← h2] at p0 p1 p2 p3 p4 hreg5 hreg13 hreg12
      exact ⟨a0,a1,a2,a3,a4,p0,p1,p2,p3,p4,hreg5,hreg13,hreg12,trivial⟩
    · apply WordsAt.of_frame s.source hx.writes (by decide)
      have sr := s.sourceRead.low
      refine ⟨?_,?_⟩
      · change fr.rsi.toNat + 40 ≤ 2^64; omega
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        change fr.rsi.toNat + 40 ≤ (base - 8).toNat ∨ (base - 8).toNat + 368 ≤ fr.rsi.toNat
        omega
    · apply s.writes.trans hx.writes
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩
      · change fr.low.toNat ≤ (base-8).toNat; omega
      · change (base-8).toNat + 368 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat); omega


theorem firstStage {code : CodeMap} {fr : Activation} {a : Limbs} (geom : Geometry code fr) :
    MultiplyStage code fr a 0 := by
  intro args mem h
  obtain ⟨⟨lab,before,input⟩,jump,raw⟩ := firstProductCall geom h
  change CallTo (lifted := LIR.lifted) _ (LIR.program.runBlock (dialect code) ⟨lab,before,input⟩) at raw
  cases he : LIR.program.runBlock (dialect code) ⟨lab,before,input⟩ with
  | jump _ | returned _ | stuck => rw [he] at raw; exact raw.elim
  | call child frame =>
    rw [he] at raw
    obtain ⟨call, rfl⟩ := raw
    obtain ⟨out, m, reach, post⟩ := productResume geom (by decide : counted 0 = false) he call
    exact ⟨out, m, (jump.reaches []).trans reach, post⟩

end K256.Proofs.Sec1.Sqrt
