import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Sec1.Serialize

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift LIR

private theorem registers_ext {a b : Vector Value 53} (h : ∀ i : Fin 53, a[i.val] = b[i.val]) :
    a = b := Vector.ext fun i hi => h ⟨i, hi⟩

theorem uncompressedBranch {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    (compress : Value.get 64 args[5] = 0) :
    program.runBlock (dialect code) ⟨.l121692, args, mem⟩ =
      .jump ⟨.l121702, args.set 19 (.ofBool true), mem⟩ := by
  have zero : (testFlags (0 : BitVec 32)).ZF.getD false = true := by decide +kernel
  cfg_eval [compress, zero]
  congr 2
  apply registers_ext
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

def copyReturn : StackFrame Value Label signature Reg.count :=
  { target := .l1218ce, kept := #v[], arity := rfl, guard := some ⟨64, 0x1218ce⟩ }

theorem copySetup {code : CodeMap} {args : Vector Value 53} {mem : Ram} {sp dst : BitVec 64}
    (rsp : Value.get 64 args[4] = sp) (rbx : Value.get 64 args[3] = dst)
    (push : StoreOk code mem (sp - 8) 8 0x1218c8 6)
    (slot : LoadOk mem 0x203dd0 8) (target : memLoad mem 0x203dd0 64 = 0x12a820) :
    let child := (((args.set 2 ⟨64, 65⟩).set 4 ⟨64, sp - 8⟩).set 6 ⟨64, sp + 80⟩).set 7 ⟨64, dst⟩
    program.runBlock (dialect code) ⟨.l1218bb, args, mem⟩ =
      .call ⟨.l12a820, child, memStore mem (sp - 8) (0x1218ce : BitVec 64)⟩ copyReturn := by
  dsimp only
  cfg_eval
  simp only [rsp, rbx, slot, target, push, and_self, ite_true]
  congr 2
  apply registers_ext
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem returnBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp : BitVec 64} (rsp : Value.get 64 args[4] = sp)
    (slots : ∀ offset ∈ [280,288,296,304,312], LoadOk mem (sp + BitVec.ofNat 64 offset) 8)
    (low : (memLoad mem (sp + 312) 64).toNat < 2^32) :
    ∃ out : Output Value Ram Reg.count,
      program.runBlock (dialect code) ⟨.l1218ce, args, mem⟩ = .returned out ∧
      out.store = mem ∧ out.tag = some ⟨64, memLoad mem (sp + 312) 64⟩ ∧
      out.values[0] = ⟨64, Value.get 64 args[3]⟩ ∧ out.values[4] = ⟨64, sp + 320⟩ ∧
      out.values[3] = ⟨64, memLoad mem (sp + 280) 64⟩ ∧
      out.values[14] = ⟨64, memLoad mem (sp + 288) 64⟩ ∧
      out.values[15] = ⟨64, memLoad mem (sp + 296) 64⟩ ∧
      out.values[5] = ⟨64, memLoad mem (sp + 304) 64⟩ ∧
      ∀ i : Fin 53, i.val ∈ [12,13,22,39,50,51] → out.values[i] = args[i] := by
  have h0 : LoadOk mem (sp + 280) 8 := slots 280 (by decide)
  have h1 : LoadOk mem (sp + 288) 8 := slots 288 (by decide)
  have h2 : LoadOk mem (sp + 296) 8 := slots 296 (by decide)
  have h3 : LoadOk mem (sp + 304) 8 := slots 304 (by decide)
  have h4 : LoadOk mem (sp + 312) 8 := slots 312 (by decide)
  refine ⟨?out, ?step, ?post⟩
  case step =>
    cfg_eval [rsp, h0, h1, h2, h3, h4, low]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Serialize
