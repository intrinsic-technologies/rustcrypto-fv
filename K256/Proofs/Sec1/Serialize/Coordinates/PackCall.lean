import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Sec1.Serialize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

inductive Axis where
  | x | y

def Axis.packSite : Axis → Label
  | .x => .l121633
  | .y => .l121682

def Axis.afterPack : Axis → Label
  | .x => .l121643
  | .y => .l121692

def Axis.packReturn : Axis → BitVec 64
  | .x => 0x121643
  | .y => 0x121692

def Axis.offset : Axis → BitVec 64
  | .x => 151
  | .y => 183

def callFrame (l : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨l, #v[], rfl, some ⟨64, ret⟩⟩

theorem reaches_call {code : CodeMap} {caller child : Location Value Ram Label signature}
    {l : Label} {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (call : program.runBlock (dialect code) caller = .call child (callFrame l ret))
    (run : program.Exec (dialect code) ⟨child, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) :
    (program.sem (dialect code)).Reaches ⟨caller, []⟩ ⟨⟨l, out.values, out.store⟩, []⟩ := by
  refine .step (b := ⟨child, [callFrame l ret]⟩) ?_ ?_
  · simp only [Program.sem, Program.step, call, Transfer.next]
  · exact ParseSignature.exec_reaches_resume run (callFrame l ret) [] (by rw [tag]; change decide (_ = _) = true; exact decide_eq_true rfl)

theorem packCall (k : Axis) {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {args : Values Value Reg.count} {mem : Ram} {base : BitVec 64}
    (rsp : args[4] = ⟨64, base⟩) (src : args[15] = ⟨64, base + 80⟩)
    (slot : Writable code mem (base - 8) 8) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect code) ⟨k.packSite, args, mem⟩ =
        .call ⟨.l1148d0, b, memStore mem (base - 8) k.packReturn⟩
          (callFrame k.afterPack k.packReturn) ∧
      b[4] = ⟨64, base - 8⟩ ∧ b[6] = ⟨64, base + 80⟩ ∧
      b[7] = ⟨64, base + k.offset⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = args[i]) := by
  have hsp := congrArg (Value.get 64) rsp
  have hsrc := congrArg (Value.get 64) src
  change args[4].get 64 = base at hsp
  change args[15].get 64 = base + 80 at hsrc
  cases k with
  | x =>
    refine ⟨?_, ?block, ?regs⟩
    case block =>
      have hs : StoreOk code mem (base - 8) 8 0x12163e 5 :=
        ParseSignature.storeOk_of_codeRange (off := 11) slot
          (fun x hx => cover x (code_l121633 x hx)) (by decide)
      change program.runBlock _ ⟨.l121633, _, _⟩ = _
      cfg_eval [hsp, hsrc, hs]
      rfl
    case regs =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases i with ⟨i, hi'⟩
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

  | y =>
    refine ⟨?_, ?block, ?regs⟩
    case block =>
      have hs : StoreOk code mem (base - 8) 8 0x12168d 5 :=
        ParseSignature.storeOk_of_codeRange (off := 11) slot
          (fun x hx => cover x (code_l121682 x hx)) (by decide)
      change program.runBlock _ ⟨.l121682, _, _⟩ = _
      cfg_eval [hsp, hsrc, hs]
      rfl
    case regs =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases i with ⟨i, hi'⟩
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl


end K256.Proofs.Sec1.Serialize.Coordinates
