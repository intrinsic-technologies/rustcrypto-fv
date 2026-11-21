import K256.Proofs.Ecdh.Multiply.Split.Entry
import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Blocks
import K256.Proofs.Ecdh.Multiply.Split.Arguments

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1 Caller

private theorem image {fr : Activation} {a : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (e : PeerCoreEntry fr a d peer) (frame : RamWriteFrame fr.original m [fr.region]) :
    ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2 := by
  apply e.loaded_of_frame
  apply (RamWriteFrame.refl _ _).trans frame
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_,List.mem_cons_self ..,Nat.le_refl _,Nat.le_refl _⟩

private def layout (k : Site) : Label → Activation → List Atom := match k with
  | .addFirst | .addSecond => Fn1109b0.frameAt
  | .roundFirst | .roundSecond => Fn11b8f0.frameAt
  | _ => Fn1099c0.frameAt

private def result (k : Site) : Nat → Nat → Nat := match k with
  | .roundFirst | .roundSecond => Curve.mulShift384
  | .addFirst | .addSecond => fun x y => (x+y) % domain.n
  | _ => fun x y => (x*y) % domain.n

private def order (k : Site) := match k with
  | .addFirst | .addSecond => true
  | _ => false

private theorem routine (add : AddExecution) (mul : MulExecution) (round : RoundExecution) (k : Site) :
    ScalarRoutine k.callee (layout k) Fn1109b0.doneAt k.window (order k) (result k) := by
  cases k <;> first | exact add | exact mul | exact round

private theorem resultValue (k : Site) (d : Nat) : result k (k.x d) (k.y d) = k.value d := by
  cases k with
  | addFirst => exact Nat.add_mod_mod ..
  | addSecond => simp only [result, Site.x, Site.y, Site.value, Curve.splitSecond,Nat.mod_add_mod,Nat.add_mod_mod]
  | _ => rfl

private theorem layoutReady (k : Site) {fr : Activation} {a p b : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (e : PeerCoreEntry fr a d peer) (whole : RamWriteFrame fr.original m [fr.region])
    (regs : CallRegisters (k.child fr p) b) (tag : memLoad m (sp fr - 8) 64 = k.ret) :
    Atom.All Extracted.programImage b m (layout k k.callee (k.child fr p)) := by
  have access := peerStackAccess e whole
  have := e.room
  have := peerSpNat e
  have := peerPushNat e
  have := peerLowNat e
  have := k.bounds
  have align := access.align
  have aligned : (sp fr - 8).toNat % 16 = 8 := by omega
  have low : fr.low.toNat + k.window ≤ (sp fr - 8).toNat := by omega
  have rd : Readable m (sp fr - 8) 8 := (peerStackBelowWrite e access (off := 8) (by decide)).readable
  have w := peerStackBelowWrite e access (off := 8+k.window) (by omega)
  have bot : sp fr - 8 - BitVec.ofNat 64 k.window = sp fr - BitVec.ofNat 64 (8+k.window) := by
    rw [BitVec.ofNat_add]; bv_omega
  have sw : Writable Extracted.programImage m (sp fr - 8 - BitVec.ofNat 64 k.window) k.window := by
    rw [bot]
    exact w.sub (Nat.le_refl _) (by omega)
  have small : k.ret.toNat < 2^32 := by cases k <;> decide
  obtain ⟨rsp,df,cx,dx,bx,bp,si,di,r8,r9,r12,r13,r14,r15,mx,ft,fc⟩ := regs
  cases k <;> exact ⟨rsp,df,cx,dx,bx,bp,si,di,r8,r9,r12,r13,r14,r15,mx,ft,fc,
    rd,tag,small,sw,low,aligned,trivial⟩

private structure Returned (k : Site) (fr : Activation) (b : Registers) (m : Ram) (d : Nat) : Prop where
  regs : ∃ p, k.returned fr p b m
  widths : ParseSignature.ArgumentWidths b
  frame : RamWriteFrame fr.original m [fr.region]
  locals : LocalsAt fr m
  scalars : ScalarsAt fr m (k.after d)

private theorem runSite (add : AddExecution) (mul : MulExecution) (round : RoundExecution) (k : Site)
    {fr : Activation} {a p b c : Registers} {d : Nat} {peer : Projective} {m n : Ram} (e : PeerCoreEntry fr a d peer)
    (bound : d < domain.n) (regs : CallRegisters (k.child fr p) c)
    (call : program.runBlock (dialect Extracted.programImage) ⟨k.pc,b,m⟩ =
      .call ⟨k.callee,c,n⟩ (callFrame k.resume k.ret))
    (tag : memLoad n (sp fr-8) 64 = k.ret) (whole : RamWriteFrame fr.original n [fr.region])
    (locals : LocalsAt fr n) (before : ScalarsAt fr n (k.before d)) :
    ∃ b' m', Reaches k.pc b m k.resume b' m' ∧ Returned k fr b' m' d := by
  have loaded := image e whole
  obtain ⟨x,y⟩ := peerOperands k e whole loaded before p
  have bounds := boundedInputs k bound
  have orderArg : order k = true → (k.child fr p).rcx = 0x2021a0 := by
    cases k <;> first | exact fun _ => rfl | intro h; contradiction
  have dest := k.dest_eq fr p
  have write := peerSlotWrite e (peerStackAccess e whole) k.bounds.1
  have := peerSpNat e
  have := peerPushNat e
  have := peerSlotNat e k.dest (by have := k.bounds; omega)
  have := e.room
  have high : (sp fr - 8).toNat + 8 ≤ (slot fr k.dest).toNat := by omega
  obtain ⟨out,exec,ret,doneAt,widths,words,foot⟩ :=
    routine add mul round k (fr := k.child fr p) (a := c) (m := n) (x := k.x d) (y := k.y d)
      (layoutReady k e whole regs tag) loaded orderArg bounds.1 bounds.2 x.read y.read
      (dest ▸ write) (dest ▸ high) (by
        intro src hs
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl|rfl
        · exact ⟨x.stack,dest ▸ x.dest⟩
        · exact ⟨y.stack,dest ▸ y.dest⟩) x.words y.words
  rw [dest, resultValue] at words
  rw [dest] at foot
  have calleeFrame := (RamWriteFrame.refl n (k.writes fr)).trans foot (k.peerCalleeWithin e)
  exact ⟨out.values,out.store,Sample.reachesAfterSampleCall call exec ret [],
    ⟨p,doneAt⟩,widths,whole.trans calleeFrame (k.peerWithin e),k.peerKeepLocals e calleeFrame locals,
    k.produced (k.peerTransfer e calleeFrame before) words⟩

private theorem resumeSite (add : AddExecution) (mul : MulExecution) (round : RoundExecution)
    (k : Site) (later : k ≠ .roundFirst) {fr : Activation} {a b : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (e : PeerCoreEntry fr a d peer) (bound : d < domain.n) (prev : Returned k.prev fr b m d) :
    ∃ b' m', Reaches k.pc b m k.resume b' m' ∧ Returned k fr b' m' d := by
  obtain ⟨p,regs⟩ := prev.regs
  have push := k.peerPushFrame e m
  obtain ⟨c,call,child⟩ := callBlock k later regs prev.widths
    (peerStackBelowWrite e (peerStackAccess e prev.frame) (off := 8) (by decide))
  have old : ScalarsAt fr m (k.before d) := by
    cases k <;> first | exact False.elim (later rfl) | exact prev.scalars
  exact runSite add mul round k e bound child call
    (by rw [memLoad_memStore_same] <;> decide)
    (prev.frame.trans push (k.peerWithin e)) (k.peerKeepLocals e push prev.locals) (k.peerTransfer e push old)

private theorem frameRead {fr : Activation} {m : Ram} {q : BitVec 64}
    (frame : RamWriteFrame fr.original m [fr.region])
    (low : fr.low.toNat ≤ fr.rsp.toNat) (room : q.toNat + 8 ≤ 2^64)
    (away : q.toNat + 8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ q.toNat) :
    memLoad m q 64 = memLoad fr.original q 64 := by
  apply frame.memLoad_eq (a := q) (k := 64)
  refine ⟨room,?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  change q.toNat + 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ q.toNat
  omega

private theorem returnAtoms {code : CodeMap} {fr : Activation} {a b : Registers} {m : Ram}
    (original : Atom.All code a fr.original (Fn11c880.frameAt .l11c880 fr))
    (frame : RamWriteFrame fr.original m [fr.region]) (locals : LocalsAt fr m)
    (room : 3800 ≤ fr.rsp.toNat) (high : fr.rsp.toNat + 6112 ≤ 2^32)
    (start : fr.low.toNat = fr.rsp.toNat - 3800)
    (rs : b[4] = ⟨64,sp fr⟩) (df : b[22] = ⟨1,0⟩) (mx : b[39] = ⟨32,fr.mxcsr⟩)
    (ft : b[50] = ⟨16,fr.ftw⟩) (fc : b[51] = ⟨16,fr.fcw⟩) :
    Atom.All code b m (Fn11c880.frameAt .l11c9e7 fr) := by
  simp only [Fn11c880.frameAt,Fn11c880.frameAtG1,Atom.All,Atom.Holds] at original
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rdRet,ret,small,win,low,align,rd₁,v₁,rd₂,v₂,sep,_⟩ := original
  have lowSp : fr.low.toNat ≤ fr.rsp.toNat := by rw [start]; exact Nat.sub_le ..
  have ret' := (frameRead (q := fr.rsp) frame lowSp (by omega) (Or.inr (Nat.le_refl _))).trans ret
  have got (q : BitVec 64) (lo : 0x203de0 ≤ q.toNat) (hi : q.toNat ≤ 0x203e20) :=
    frameRead (q := q) frame lowSp (by omega) (by rw [start]; omega)
  have saved (k v : BitVec 64) (h : (0xcb8 - k,v) ∈ savedSlots fr) :
      memLoad m (fr.rsp - k) 64 = v := by
    have word := locals (0xcb8-k,v) (List.mem_append_right (Caller.locals fr) h)
    change memLoad m (sp fr + (0xcb8-k)) 64 = v at word
    rwa [show sp fr + (0xcb8-k) = fr.rsp-k by unfold sp; bv_omega] at word
  simp only [Fn11c880.frameAt,Fn11c880.frameAtG1,Atom.All,Atom.Holds]
  refine ⟨rs,df,mx,ft,fc,?_,?_,?_,?_,?_,?_,rdRet.of_frame frame,
    ret',small,win.of_frame frame,low,align,rd₁.of_frame frame,(got 0x203de0 (by decide) (by decide)).trans v₁,
    rd₂.of_frame frame,(got 0x203e20 (by decide) (by decide)).trans v₂,sep,trivial⟩
  · exact saved 48 fr.rbx (by simp [savedSlots])
  · exact saved 40 fr.r12 (by simp [savedSlots])
  · exact saved 32 fr.r13 (by simp [savedSlots])
  · exact saved 24 fr.r14 (by simp [savedSlots])
  · exact saved 16 fr.r15 (by simp [savedSlots])
  · exact saved 8 fr.rbp (by simp [savedSlots])

private theorem finish {fr : Activation} {a b : Registers} {d : Nat} {peer : Projective} {m : Ram} (e : PeerCoreEntry fr a d peer)
    (out : Returned .addFirst fr b m d) : SplitState fr b m d := by
  obtain ⟨p,rs,df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := out.regs
  have stack : b[4] = ⟨64,sp fr⟩ := by
    change b[4] = ⟨64,sp fr - 8 + 8⟩ at rs
    simpa only [BitVec.sub_add_cancel] using rs
  refine ⟨returnAtoms e.atoms out.frame out.locals e.room e.high (peerLowNat e) stack df mx ft fc,out.widths,?widths,out.frame,out.scalars (0x1d0,Curve.splitFirst d) (List.mem_cons_self ..),
    out.scalars (0x418,Curve.splitSecond d) (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    fun kv hk => out.locals _ (List.mem_append_left _ hk),r15⟩
  case widths =>
    rintro ⟨i,hi⟩ hm
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg Value.width bx | exact congrArg Value.width bp | exact congrArg Value.width r12
      | exact congrArg Value.width r13 | exact congrArg Value.width r14 | exact congrArg Value.width r15

theorem peerCalls (addCall : AddExecution) (mulCall : MulExecution) (roundCall : RoundExecution)
    {fr : Activation} {a b : Registers} {m : Ram} {d : Nat} {peer : Projective} (entry : PeerCoreEntry fr a d peer)
    (bound : d < domain.n)
    (atoms : Atom.All Extracted.programImage b m (Fn11c880.frameAt .l11c8d2 fr))
    (count : b[6] = ⟨64, 1⟩) (frame : RamWriteFrame fr.original m [fr.region]) :
    ∃ c m', Reaches .l11c8d2 b m .l11c9e7 c m' ∧ SplitState fr c m' d := by
  obtain ⟨b₁,m₁,c,n,path,call,regs,tag,written,locals⟩ := peerEnterFirstCall entry atoms count frame
  obtain ⟨b₂,m₂,h₂,s₂⟩ := runSite addCall mulCall roundCall .roundFirst entry bound regs call tag
    written locals (by intro kv h; cases h)
  obtain ⟨b₃,m₃,h₃,s₃⟩ := resumeSite addCall mulCall roundCall .mulFirst (by decide) entry bound s₂
  obtain ⟨b₄,m₄,h₄,s₄⟩ := resumeSite addCall mulCall roundCall .roundSecond (by decide) entry bound s₃
  obtain ⟨b₅,m₅,h₅,s₅⟩ := resumeSite addCall mulCall roundCall .mulSecond (by decide) entry bound s₄
  obtain ⟨b₆,m₆,h₆,s₆⟩ := resumeSite addCall mulCall roundCall .addSecond (by decide) entry bound s₅
  obtain ⟨b₇,m₇,h₇,s₇⟩ := resumeSite addCall mulCall roundCall .mulLambda (by decide) entry bound s₆
  obtain ⟨b₈,m₈,h₈,s₈⟩ := resumeSite addCall mulCall roundCall .addFirst (by decide) entry bound s₇
  exact ⟨b₈,m₈,path.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))),finish entry s₈⟩

end K256.Proofs.Generate.Generator.Multiply.Split
