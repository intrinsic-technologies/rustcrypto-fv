import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.Wrapper.Entry
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Sec1.Affine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR

private theorem registers_eq {a b : Vector Value 53} (h : ∀ i : Fin 53, a[i.val] = b[i.val]) :
    a = b := Vector.ext fun i hi => h ⟨i, hi⟩

theorem parityCall {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (args : Vector Value 53) (mem : Ram) (sp : BitVec 64) (rsp : args[4].get 64 = sp)
    (writable : Writable code mem (sp - 8) 8) :
    program.runBlock (dialect code) ⟨.l1214bb, args, mem⟩ =
      .call ⟨.l127d50, args.set 4 ⟨64, sp - 8⟩, memStore mem (sp - 8) (0x1214c0 : BitVec 64)⟩
        (Wrapper.callFrame .l1214c0 0x1214c0) := by
  have push : StoreOk code mem (sp - 8) 8 0x1214bb 5 :=
    ParseSignature.storeOk_of_codeRange (off := 0) writable
      (fun x hx => hcode x (code_l1214bb x hx)) (by decide)
  cfg_eval
  simp only [rsp, push, ↓reduceIte]
  congr 2
  apply registers_eq
  intro i
  simp only [Vector.getElem_set]
  finite_cases i <;> rfl

theorem coordinateCall {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (compressed : Bool) (args : Vector Value 53) (mem : Ram) (sp : BitVec 64)
    (rsp : args[4].get 64 = sp) (writable : Writable code mem (sp - 8) 8) :
    let next := if compressed then Label.l1214ce else .l121502
    let ret : BitVec 64 := if compressed then 0x1214ce else 0x121502
    let arg := if compressed then ((args[0].get 64).setWidth 8).setWidth 64 else args[2].get 64 + 33
    let child := (((args.set 2 ⟨64, arg⟩).set 4 ⟨64, sp - 8⟩).set 6 ⟨64, args[14].get 64⟩).set 7 ⟨64, sp⟩
    program.runBlock (dialect code) ⟨if compressed then .l1214c0 else .l1214f3, args, mem⟩ =
      .call ⟨if compressed then .l1205b0 else .l11f780, child, memStore mem (sp - 8) ret⟩
        (Wrapper.callFrame next ret) := by
  have pushX : StoreOk code mem (sp - 8) 8 0x1214c9 5 :=
    ParseSignature.storeOk_of_codeRange (off := 9) writable
      (fun x hx => hcode x (code_l1214c0 x hx)) (by decide)
  have pushXY : StoreOk code mem (sp - 8) 8 0x1214fd 5 :=
    ParseSignature.storeOk_of_codeRange (off := 10) writable
      (fun x hx => hcode x (code_l1214f3 x hx)) (by decide)
  cases compressed
  case' false => change program.runBlock _ ⟨.l1214f3, args, mem⟩ = .call ⟨.l11f780, _, _⟩ _
  case' true => change program.runBlock _ ⟨.l1214c0, args, mem⟩ = .call ⟨.l1205b0, _, _⟩ _
  all_goals cfg_eval <;> simp only [rsp, pushX, pushXY, ↓reduceIte] <;> congr 2 <;>
    apply registers_eq <;> intro i <;> simp only [Vector.getElem_set] <;> finite_cases i <;> rfl

end K256.Proofs.Sec1.Affine
