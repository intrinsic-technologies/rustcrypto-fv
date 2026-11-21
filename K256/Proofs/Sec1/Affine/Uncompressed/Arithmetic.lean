import K256.Proofs.Sec1.Affine.Uncompressed.Payload
import K256.Proofs.Sec1.Affine.Uncompressed.SquareWords
import K256.Proofs.Sec1.Affine.Uncompressed.ProductWords
import K256.Proofs.Sec1.Affine.Uncompressed.Equation

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

def localLimbs (m : Ram) (sp : Word) (second : Bool) : Limbs :=
  Vector.ofFn fun i : Fin 5 =>
    memLoad m (sp + limbOffset ((if second then 5 else 0) + i.val)) 64

structure ArithmeticPost (args next : Values Value Reg.count) (mem m : Ram) (sp : Word)
    (x y : Limbs) (validY : Bool) : Prop where
  stack : next[4].get 64 = sp - 8
  argument : next[7].get 64 = BitVec.ofNat 64 (equation (cubeProduct x (squareX x)) (squareY y)).toNat
  returnSlot : memLoad m (sp - 8) 64 = 0x120298
  coordinatesX : localLimbs m sp false = x
  coordinatesY : localLimbs m sp true = y
  flag : memLoad m (sp + 192) 64 = BitVec.ofNat 64 validY.toNat
  frame : RamWriteFrame mem m [⟨(sp - 8).toNat, 208⟩]
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → next[i] = args[i]

def ArithmeticCall (code : CodeMap) : Prop :=
  ∀ (args : Values Value Reg.count) (mem : Ram) (sp a b c d : Word) (ok : Bool),
    args[4].get 64 = sp → (args[0].get 64).setWidth 8 = BitVec.ofNat 8 ok.toNat →
    args[15].get 64 = d &&& 0xfffffffffffff →
    args[13].get 64 = shldResult 12 c d &&& 0xfffffffffffff →
    args[12].get 64 = shldResult 24 b c → args[3].get 64 = shldResult 36 a b →
    args[14].get 64 = a >>> 16 → args[5].get 64 = 0xfffffffffffff →
    Writable code mem (sp - 8) 208 →
    ∃ next m, program.runBlock (dialect code) ⟨.l11f8f6, args, mem⟩ =
      .call ⟨.l127d50, next, m⟩ (choiceResume .l120298 0x120298 rfl) ∧
      ArithmeticPost args next mem m sp (localLimbs mem sp false)
        (if ok then unpack a b c d else Vector.replicate 5 0) ok

end K256.Proofs.Sec1.Affine.Uncompressed
