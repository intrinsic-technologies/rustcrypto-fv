import K256.Proofs.Sec1.LIR.Fn115950.Frame
import K256.Proofs.Sec1.Tactic.Core
import K256.Proofs.Common.Field.Repr

namespace K256.Proofs.Sec1.Sqrt.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field

structure Writeback where
  d0 : Word
  d1 : Word
  d2 : Word
  d3 : Word
  d4 : Word
  rax : Word

def Writeback.limbs (w : Writeback) : Limbs := #v[w.d0, w.d1, w.d2, w.d3, w.d4]

def Writeback.status (w : Writeback) : BitVec 8 := w.rax.setWidth 8

def footprint (fr : Activation) : List MemoryRegion := [⟨fr.rdi.toNat, 41⟩]

@[refine_layout] def inputs (fr : Activation) (w : Writeback) : List Atom :=
  [.gpr 0 w.rax, .gpr 14 w.d3, .gpr 3 w.d4,
    .mem (fr.rsp - 0x108) 64 w.d0, .mem (fr.rsp - 0x110) 64 w.d1, .mem (fr.rsp - 0xb8) 64 w.d2,
    .writable fr.rdi 41,
    .fact (fr.rdi.toNat + 41 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
    .fact (fr.rdi.toNat + 41 ≤ 0x11a51c ∨ 0x11a567 ≤ fr.rdi.toNat)]

private inductive Op : Nat → Type where
  | gather : Op 6

private def eval : {n : Nat} → Op n → Values Word n → Writeback → Option (Word × Writeback)
  | _, .gather, v, _ => some (0, ⟨v[0], v[1], v[2], v[3], v[4], v[5]⟩)

private def dialect : Dialect Op Word Writeback where
  eval := eval
  truth := (· != 0)

private def program : Program Op Unit (fun _ => 7) 1 where
  blocks _ := .letOp .gather #v[%1, %2, %3, %4, %5, %6] (.terminate (.ret #v[%0]))

private def params (w : Writeback) (dst : Word) : Values Word 7 :=
  #v[dst, w.d0, w.d1, w.d2, w.d3, w.d4, w.rax]

private def result (dst : Word) (w : Writeback) : CFG.Output Word Writeback 1 :=
  ⟨#v[dst], none, w⟩

private def outputs (dst ret : Word) (w : Writeback) : List Atom :=
  [.gpr 0 ret, .words dst 64 w.limbs, .mem (dst + 40) 8 w.status]

private def core : LayoutCore program dialect LIR.lifted Word where
  start _ := .l11a51c
  Params _ := Word × Writeback
  args _ p := params p.2 p.1
  store _ p := p.2
  atoms _ dst fr p := [.fact (p.1 = fr.rdi), .fact (dst = fr.rdi)] ++ inputs fr p.2
  Result := Word × Writeback
  output r := result r.1 r.2
  done dst _ r := outputs dst r.1 r.2
  footprint dst _ := [⟨dst.toNat, 41⟩]

private def layout :=
  Layout.withFrame LIR.Fn115950.frameAt LIR.Fn115950.doneAt core

set_option maxHeartbeats 4000000 in
private theorem block (code : CodeMap) : layout.BlockSimulation code () := by
  x86_refine [params, result, Writeback.limbs, Writeback.status]

theorem writebackExec {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    (fr : Activation) (w : Writeback)
    (saved : Atom.All code args mem (LIR.Fn115950.frameAt .l11a51c fr))
    (ready : Atom.All code args mem (inputs fr w))
    (frame : RamWriteFrame fr.original mem (fr.region :: footprint fr)) :
    ∃ o, LIR.program.Exec (Lift.dialect code) ⟨⟨.l11a51c, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
      o.values[0] = ⟨64, fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 w.limbs ∧
      memLoad o.store (fr.rdi + 40) 8 = w.status ∧
      RamWriteFrame fr.original o.store (fr.region :: footprint fr) := by
  let caller : CFG.Location Word Writeback Unit (fun _ => 7) := ⟨(), params w fr.rdi, w⟩
  have run : program.Exec dialect ⟨caller, []⟩ (result fr.rdi w) := .done rfl
  have rel : layout.Rel code (fr, fr.rdi) caller ⟨.l11a51c, args, mem⟩ :=
    ⟨rfl, ⟨(fr.rdi, w), rfl, rfl, (Atom.all_append _ _).2 ⟨saved, rfl, rfl, ready⟩⟩, frame⟩
  obtain ⟨o, hexec, tag, ⟨⟨ret, payload⟩, eq, regs⟩, hf⟩ :=
    (layout.simulation code (fr, fr.rdi) (fun () => block code)).exec run.sem
      (a := ⟨⟨.l11a51c, args, mem⟩, []⟩) ⟨(fr, fr.rdi), rel, rfl⟩
  have hret : fr.rdi = ret := congrArg (fun r => r.values[0]) eq
  have hpayload : w = payload := congrArg CFG.Output.store eq
  subst ret payload
  have h : Atom.All code o.values o.store (LIR.Fn115950.doneAt fr ++ outputs fr.rdi fr.rdi w) := regs
  obtain ⟨hdone, hrax, hwords, hflag, _⟩ := (Atom.all_append _ _).1 h
  exact ⟨o, Program.Exec.of_sem hexec, tag, hdone, hrax, hwords, hflag, hf⟩

end K256.Proofs.Sec1.Sqrt.Finish
