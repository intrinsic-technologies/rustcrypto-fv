import K256.Proofs.Sec1.Sqrt.Finish
import K256.Proofs.Sec1.Tactic.Core
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Sec1.Sqrt.Finish

attribute [local refine_layout] List.tail_cons

open X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field

def barrierContinuation : LIR.lifted.StackFrame :=
  { target := .l11a51c, kept := #v[], arity := rfl, guard := some ⟨64, 0x11a51c⟩ }

def Writeback.afterBarrier (w : Writeback) : Writeback :=
  { w with rax := w.status.setWidth 64 }

@[refine_layout] def barrierInputs (fr : Activation) (w : Writeback) : List Atom :=
  [.gpr 4 (fr.rsp - 0x1c0), .gpr 7 w.rax, .mem (fr.rsp - 0x1c0) 64 0x11a51c,
    .fact (fr.rsp.toNat ≤ 0x127d50 ∨ 0x127d61 ≤ fr.low.toNat)] ++
    (LIR.Fn115950.frameAt .l11a51c fr).tail ++ (inputs fr w).tail

private inductive Op : Nat → Type where
  | byte : Op 1

private def eval : {n : Nat} → Op n → Values Word n → Writeback → Option (Word × Writeback)
  | _, .byte, v, w => some ((v[0].setWidth 8).setWidth 64, w.afterBarrier)

private def dialect : Dialect Op Word Writeback where
  eval := eval
  truth := (· != 0)

private def program : Program Op Unit (fun _ => 6) 1 where
  blocks _ := .letOp .byte #v[%0] (.terminate (.ret #v[%6]))

private def arguments (w : Writeback) : Values Word 6 :=
  #v[w.rax, w.d0, w.d1, w.d2, w.d3, w.d4]

private def result (v : Word) (w : Writeback) : CFG.Output Word Writeback 1 :=
  ⟨#v[v], none, w⟩

private def layout : Layout program dialect LIR.lifted (Activation × Unit) where
  start _ := .l127d50
  Params _ := Writeback
  args _ := arguments
  store _ w := w
  atoms _ c := barrierInputs c.1
  Result := Word × Writeback
  output r := result r.1 r.2
  done c r := [.gpr 0 r.1] ++ LIR.Fn115950.frameAt .l11a51c c.1 ++ (inputs c.1 r.2).tail
  retAddr _ := 0x11a51c
  original c := c.1.original
  regions c := c.1.region :: footprint c.1

set_option maxHeartbeats 4000000 in
private theorem barrierBlock (code : CodeMap) : layout.BlockSimulation code () := by
  x86_refine [arguments, result, Writeback.afterBarrier, Writeback.status, footprint]

theorem barrierThenWriteback {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    (fr : Activation) (w : Writeback)
    (entry : Atom.All code args mem (barrierInputs fr w))
    (frame : RamWriteFrame fr.original mem (fr.region :: footprint fr)) :
    ∃ o, LIR.program.Exec (Lift.dialect code)
        ⟨⟨.l127d50, args, mem⟩, [barrierContinuation]⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
      o.values[0] = ⟨64, fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 w.limbs ∧
      memLoad o.store (fr.rdi + 40) 8 = w.status ∧
      RamWriteFrame fr.original o.store (fr.region :: footprint fr) := by
  let loc : CFG.Location Word Writeback Unit (fun _ => 6) := ⟨(), arguments w, w⟩
  have exec : program.Exec dialect ⟨loc, []⟩ (result w.afterBarrier.rax w.afterBarrier) :=
    .done rfl
  have rel : layout.Rel code (fr, ()) loc ⟨.l127d50, args, mem⟩ :=
    ⟨rfl, ⟨w, rfl, rfl, entry⟩, frame⟩
  obtain ⟨mid, run, tag, ⟨⟨r, payload⟩, eq, ha⟩, hf⟩ :=
    (layout.simulation code (fr, ()) (fun () => barrierBlock code)).exec exec.sem
      (a := ⟨⟨.l127d50, args, mem⟩, []⟩) ⟨(fr, ()), rel, rfl⟩
  have hrax : w.afterBarrier.rax = r := congrArg (fun o => o.values[0]) eq
  have hp : w.afterBarrier = payload := congrArg CFG.Output.store eq
  subst r payload
  change Atom.All code mid.values mid.store
    ([.gpr 0 w.afterBarrier.rax] ++
      LIR.Fn115950.frameAt .l11a51c fr ++ (inputs fr w.afterBarrier).tail) at ha
  obtain ⟨rax, tail⟩ := ha
  obtain ⟨saved, data⟩ := (Atom.all_append _ _).1 tail
  have ready : Atom.All code mid.values mid.store (inputs fr w.afterBarrier) := ⟨rax, data⟩
  obtain ⟨o, ho, tags, done, hdr, words, flag, writes⟩ :=
    writebackExec fr w.afterBarrier saved ready hf
  have accept : barrierContinuation.Accepts (Lift.dialect code) mid.tag = true := by
    rw [tag]
    rfl
  have reach := ParseSignature.exec_reaches_resume (Program.Exec.of_sem run) barrierContinuation [] accept
  have flagSame : w.afterBarrier.status = w.status := BitVec.setWidth_setWidth_of_le w.status (by decide)
  exact ⟨o, Program.Exec.of_sem (reach.exec ho.sem), tags, done, hdr, words, flag.trans flagSame, writes⟩

end K256.Proofs.Sec1.Sqrt.Finish
