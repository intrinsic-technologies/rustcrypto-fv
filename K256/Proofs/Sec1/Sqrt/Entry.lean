import K256.Proofs.Sec1.LIR.Fn115950.Frame
import K256.Proofs.Sec1.LIR.Fn127d50.Frame
import K256.Proofs.Sec1.Square.Contract
import K256.Proofs.Sec1.Tactic.Core
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Sec1.Sqrt.Entry
open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Common.Field

structure Store where
  inp : Limbs
  w : Limbs

inductive Op : Nat → Type where
  | square : Op 1
  | lowByte : Op 1
  | setW : Op 5
  | setIn : Op 5
  | add (k : Word) : Op 1

def eval : {n : Nat} → Op n → Values Word n → Store → Option (Word × Store)
  | _, .square, v, s => some (v[0], { s with w := squareWords s.inp })
  | _, .lowByte, v, s => some ((v[0].setWidth 8).setWidth 64, s)
  | _, .setW, v, s => some (0, { s with w := #v[v[0], v[1], v[2], v[3], v[4]] })
  | _, .setIn, v, s => some (0, { s with inp := #v[v[0], v[1], v[2], v[3], v[4]] })
  | _, .add k, v, s => some (v[0] + k, s)

def dialect : Dialect Op Word Store where
  eval := eval
  truth := (· != 0)

inductive Label where
  | sq | byte | entry | afterSquare

def signature : Label → Nat
  | .sq => 1
  | .byte => 6
  | .entry => 12
  | .afterSquare => 13

def program (next : Block Op Label signature 1 13) : Program Op Label signature 1 where
  blocks
    | .sq => .letOp .square #v[%0] (.terminate (.ret #v[%0]))
    | .byte => .letOp .lowByte #v[%0] (.letOp .setW #v[%1, %2, %3, %4, %5] (.terminate (.ret #v[%6])))
    | .entry => .letOp .setIn #v[%2, %3, %4, %5, %6]
        (.letOp (.add 0x28) #v[%1]
          (.terminate (.call ⟨.sq, #v[%13]⟩
            ⟨.afterSquare, #v[%0, %1, %2, %3, %4, %5, %6, %7, %8, %9, %10, %11], rfl, none⟩)))
    | .afterSquare => next

structure SquareParams where
  x : Word
  st : Store

structure ByteParams where
  x : Word
  o0 : Word
  o1 : Word
  o2 : Word
  o3 : Word
  o4 : Word
  st : Store

structure EntryParams where
  out : Word
  sp : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  o0 : Word
  o1 : Word
  o2 : Word
  o3 : Word
  o4 : Word
  st : Store

structure ResumeParams where
  rax : Word
  out : Word
  sp : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  o0 : Word
  o1 : Word
  o2 : Word
  o3 : Word
  o4 : Word
  st : Store

def Params : Label → Type
  | .sq => SquareParams
  | .byte => ByteParams
  | .entry => EntryParams
  | .afterSquare => ResumeParams

structure Result where
  rax : Word
  st : Store

@[refine_layout] def frameAtG0 : K256.Proofs.Sec1.LIR.Label.G0 → Activation → List Atom
  | .l1145f0 => K256.Proofs.Sec1.LIR.Fn1145f0.frameAtG0 .l1145f0
  | l => K256.Proofs.Sec1.LIR.Fn115950.frameAtG0 l

@[refine_layout] def frameAt : K256.Proofs.Sec1.LIR.Label → Activation → List Atom
  | .g0 l => frameAtG0 l
  | .g1 l => K256.Proofs.Sec1.LIR.Fn115950.frameAtG1 l
  | .g9 l => K256.Proofs.Sec1.LIR.Fn127d50.frameAtG9 l
  | _ => fun _ => []

@[refine_layout] def sqrtBase (c : Word) (fr : Activation) (out sp : Word) (a o : Limbs) : List Atom :=
  [.fact (out = c), .fact (sp = fr.rsp - 0x1b8), .words fr.rsi 64 a, .readable fr.rsi 40,
    .words fr.rdi 64 o, .writable fr.rdi 41,
    .fact (fr.rsi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat),
    .fact (fr.rdi.toNat + 41 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
    .fact (fr.rdi.toNat + 41 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rdi.toNat),
    .fact (fr.rsi.toNat + 40 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsi.toNat),
    .fact (fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.low.toNat)]

open K256.Proofs.Sec1.LIR in
def core (next : Block Op Label signature 1 13) : LayoutCore (program next) dialect lifted Word where
  start
    | .sq => .g0 .l1145f0
    | .byte => .g9 .l127d50
    | .entry => .g0 .l115950
    | .afterSquare => .g0 .l1159a4
  Params := Params
  args
    | .sq => fun p => #v[p.x]
    | .byte => fun p => #v[p.x, p.o0, p.o1, p.o2, p.o3, p.o4]
    | .entry => fun p => #v[p.out, p.sp, p.a0, p.a1, p.a2, p.a3, p.a4, p.o0, p.o1, p.o2, p.o3, p.o4]
    | .afterSquare => fun p => #v[p.rax, p.out, p.sp, p.a0, p.a1, p.a2, p.a3, p.a4, p.o0, p.o1, p.o2, p.o3, p.o4]
  store
    | .sq => fun p => p.st
    | .byte => fun p => p.st
    | .entry => fun p => p.st
    | .afterSquare => fun p => p.st
  atoms
    | .sq => fun c fr p => [.gpr 7 c, .gpr 7 p.x, .words fr.rsi 64 p.st.inp, .readable fr.rsi 40,
        .writable fr.rdi 40, .fact (fr.rdi.toNat % 8 = 0),
        .fact (fr.rdi.toNat + 40 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 40 ≤ fr.rdi.toNat),
        .fact (fr.rsi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat),
        .fact (fr.rdi.toNat + 40 ≤ 0x1145f0 ∨ 0x1148c4 ≤ fr.rdi.toNat),
        .fact (fr.rsp.toNat + 8 ≤ 0x1145f0 ∨ 0x1148c4 ≤ fr.low.toNat),
        .fact (fr.rdi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)]
    | .byte => fun c fr p => [.gpr 7 p.x, .words c 64 #v[p.o0, p.o1, p.o2, p.o3, p.o4],
        .fact (c.toNat + 41 ≤ 2 ^ 32), .fact (c.toNat + 41 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ c.toNat),
        .fact (fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.low.toNat)]
    | .entry => fun c fr p => [.gpr 7 c, .gpr 7 p.out] ++ sqrtBase c fr p.out p.sp #v[p.a0, p.a1, p.a2, p.a3, p.a4] #v[p.o0, p.o1, p.o2, p.o3, p.o4]
    | .afterSquare => fun c fr p => [.fact (c = fr.rdi), .gpr 0 p.rax, .words (fr.rsp - 0x190) 64 p.st.w] ++ sqrtBase c fr p.out p.sp #v[p.a0, p.a1, p.a2, p.a3, p.a4] #v[p.o0, p.o1, p.o2, p.o3, p.o4]
  Result := Result
  output r := ⟨#v[r.rax], none, r.st⟩
  done c _ r := [.gpr 0 r.rax, .words c 64 r.st.w]
  footprint c _ := [⟨c.toNat, 40⟩]

def layout (next : Block Op Label signature 1 13) :=
  Layout.withFrame frameAt K256.Proofs.Sec1.LIR.Fn115950.doneAt (core next)

variable (next : Block Op Label signature 1 13)

theorem byte_block (code : CodeMap) : (layout next).BlockSimulation code .byte := by
  x86_refine

set_option maxHeartbeats 4000000 in
theorem entry_block (code : CodeMap) : (layout next).BlockSimulation code .entry := by
  x86_refine


private def squareInput (p : EntryParams) : Limbs :=
  #v[p.a0, p.a1, p.a2, p.a3, p.a4]

private def squareAddress (p : EntryParams) : Word := p.sp + 40

private def squareResult (p : EntryParams) : CFG.Output Word Store 1 :=
  ⟨#v[squareAddress p], none, ⟨squareInput p, squareWords (squareInput p)⟩⟩

def entryLocation (next : Block Op Label signature 1 13) (p : EntryParams) :
    CFG.Location Word Store Label signature :=
  ⟨.entry, (core next).args .entry p, p.st⟩

def resumeLocation (next : Block Op Label signature 1 13) (p : EntryParams) :
    CFG.Location Word Store Label signature :=
  ⟨.afterSquare, (core next).args .afterSquare
      ⟨squareAddress p, p.out, p.sp, p.a0, p.a1, p.a2, p.a3, p.a4,
        p.o0, p.o1, p.o2, p.o3, p.o4, (squareResult p).store⟩,
    (squareResult p).store⟩

private theorem square_call {code : CodeMap} {fr : Activation} {l : LIR.lifted.Location}
    {dst : Word} {s : Store}
    (h : (layout next).Rel code (fr, dst) ⟨.sq, #v[dst], s⟩ l) :
    ∃ lo, LIR.lifted.program.Exec (Lift.dialect code) ⟨l, []⟩ lo ∧
      (layout next).RetRel code (fr, dst) ⟨#v[dst], none, ⟨s.inp, squareWords s.inp⟩⟩ lo := by
  obtain ⟨hl, ⟨p, hp, hst, ha⟩, hf⟩ := h
  change l.label = .l1145f0 at hl
  clear hp
  change s = p.st at hst
  rw [hst]
  change Atom.All code l.arguments l.store
    (LIR.Fn1145f0.frameAtG0 .l1145f0 fr ++ (core next).atoms .sq dst fr p) at ha
  obtain ⟨hframe, hats⟩ := (Atom.all_append _ _).1 ha
  obtain ⟨hdst, _, hin, hread, hwrite, halign, hdisj, hstack, hcode, hstackcode, hout, _⟩ := hats
  have frameCopy := hframe
  obtain ⟨_, _, _, _, _, _, _, hd, _⟩ := frameCopy
  have hptr : fr.rdi = dst := Value.eq_bits (hd.symm.trans hdst)
  rw [← hptr] at hf ⊢
  let old : Limbs := Vector.ofFn fun i => memLoad l.store (wordAddr fr.rdi 64 i.val) 64
  have hold : WordsAt l.store fr.rdi 64 old := by
    intro i hi
    simp only [old, Vector.getElem_ofFn]
  have hr : Square.layout.Rel code (fr, ()) ⟨.entry, #v[], (p.st.inp, old)⟩ l :=
    ⟨hl, ⟨_, rfl, rfl, (Atom.all_append _ _).2
      ⟨hframe, hin, hread, hold, hwrite, halign, hdisj, hstack, hcode, hstackcode, hout, trivial⟩⟩, hf⟩
  obtain ⟨o, he, ho, _⟩ := Square.call code fr (p.st.inp, old) l hr
  obtain ⟨hoTag, ⟨r, heq, hr⟩, hwriteFrame⟩ := ho
  have heq' := congrArg CFG.Output.store heq
  change (p.st.inp, squareWords p.st.inp) = r at heq'
  subst r
  change Atom.All code o.values o.store
    (LIR.Fn1145f0.doneAt fr ++ Square.core.done () fr (p.st.inp, squareWords p.st.inp)) at hr
  obtain ⟨hdone, hrax, _, hwords, _⟩ := (Atom.all_append _ _).1 hr
  exact ⟨o, he, hoTag, ⟨⟨fr.rdi, ⟨p.st.inp, squareWords p.st.inp⟩⟩, rfl,
    (Atom.all_append _ _).2 ⟨hdone, hrax, hwords, trivial⟩⟩, hwriteFrame⟩

theorem firstSquare {code : CodeMap} {ctx : Activation × Word} {l : LIR.lifted.Location}
    {stack : List LIR.lifted.StackFrame} (p : EntryParams)
    (h : (layout next).Rel code ctx (entryLocation next p) l) :
    ∃ resume, (LIR.lifted.program.sem (Lift.dialect code)).Reaches ⟨l, stack⟩ ⟨resume, stack⟩ ∧
      (layout next).Rel code ctx (resumeLocation next p) resume := by
  have hs := entry_block next code ctx _ _ l h
  let target : CFG.Location Word Store Label signature :=
    ⟨.sq, #v[squareAddress p], ⟨squareInput p, p.st.w⟩⟩
  let ret : CFG.StackFrame Word Label signature 1 :=
    { target := .afterSquare, kept := (core next).args .entry p, arity := rfl, guard := none }
  change (layout next).MatchedBy code ctx l (.call target ret) at hs
  obtain ⟨before, hjump, hs⟩ := hs
  cases he : LIR.lifted.program.runBlock (Lift.dialect code) before with
  | call child frame =>
    rw [he] at hs
    obtain ⟨⟨fr, dst⟩, hchild, hresume⟩ := hs
    have hp := hchild.params
    obtain ⟨q, hq, _, ha⟩ := hp
    change #v[squareAddress p] = #v[q.x] at hq
    have hx := congrArg (fun v : Vector Word 1 => v[0]) hq
    change squareAddress p = q.x at hx
    change Atom.All code child.arguments child.store
      (LIR.Fn1145f0.frameAtG0 .l1145f0 fr ++ (core next).atoms .sq dst fr q) at ha
    obtain ⟨_, hd, hq, _⟩ := (Atom.all_append _ _).1 ha
    have hdx : dst = squareAddress p := (Value.eq_bits (hd.symm.trans hq)).trans hx.symm
    rw [hdx] at hchild hresume
    obtain ⟨output, hexec, hout⟩ := square_call next hchild
    obtain ⟨haccept, hback⟩ := hresume (squareResult p) output hout rfl
    refine ⟨frame.resume output, ((hjump.reaches stack).tail ?_).trans
      (ParseSignature.exec_reaches_resume hexec frame stack haccept), hback⟩
    change (LIR.lifted.program.runBlock (Lift.dialect code) before).next (Lift.dialect code) stack = _
    rw [he]
    rfl
  | jump _ | returned _ | stuck => rw [he] at hs; exact hs.elim

def byteLocation (next : Block Op Label signature 1 13) (p : ByteParams) :
    CFG.Location Word Store Label signature :=
  ⟨.byte, (core next).args .byte p, p.st⟩

theorem byteCall {code : CodeMap} {ctx : Activation × Word} {l : LIR.lifted.Location}
    (p : ByteParams) (h : (layout next).Rel code ctx (byteLocation next p) l) :
    ∃ output, LIR.lifted.program.Exec (Lift.dialect code) ⟨l, []⟩ output ∧
      (layout next).RetRel code ctx
        ⟨#v[(p.x.setWidth 8).setWidth 64], none, { p.st with w := #v[p.o0, p.o1, p.o2, p.o3, p.o4] }⟩
        output := by
  have hs := byte_block next code ctx _ _ l h
  let result : CFG.Output Word Store 1 :=
    ⟨#v[(p.x.setWidth 8).setWidth 64], none, { p.st with w := #v[p.o0, p.o1, p.o2, p.o3, p.o4] }⟩
  change (layout next).MatchedBy code ctx l (.returned result) at hs
  obtain ⟨before, hjump, hr⟩ := hs
  cases he : LIR.lifted.program.runBlock (Lift.dialect code) before with
  | returned output =>
    rw [he] at hr
    refine ⟨output, Program.Exec.of_sem ((hjump.reaches []).exec (.ret ?_)), hr⟩
    change (LIR.lifted.program.runBlock (Lift.dialect code) before).next (Lift.dialect code) [] = _
    rw [he]
    rfl
  | jump _ | call _ _ | stuck => rw [he] at hr; exact hr.elim

end K256.Proofs.Sec1.Sqrt.Entry
