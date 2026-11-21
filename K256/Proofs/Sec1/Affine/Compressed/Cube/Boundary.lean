import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs Prelude K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field Serialize.Coordinates

def savedX (mem : Ram) (sp : Word) : Limbs :=
  #v[memLoad mem (sp + 80) 64, memLoad mem (sp + 88) 64, memLoad mem (sp + 64) 64,
    memLoad mem (sp + 48) 64, memLoad mem (sp + 72) 64]

def maskedX (a b c d : Word) (ok : Bool) : Limbs :=
  if ok then Uncompressed.unpack a b c d else Vector.replicate 5 0

structure CubePost (args next : Values Value Reg.count) (mem m : Ram) (sp : Word)
    (xs : Limbs) (ok : Bool) : Prop where
  rsp : next[4] = ⟨64, sp - 8⟩
  rdi : next[7] = ⟨64, sp + 304⟩
  rsi : next[6] = ⟨64, sp + 144⟩
  gprs : ∀ i : Fin 53, i.val ∈ [1,2,3,5,8,9,12,13,14,15] → next[i] = ⟨64, next[i].get 64⟩
  kept : ∀ i : Fin 53, i.val ∈ [22,39,50,51] → next[i] = args[i]
  ret : memLoad m (sp - 8) 64 = 0x120d03
  output : memLoad m (sp + 136) 64 = memLoad mem (sp + 136) 64
  parity : memLoad m (sp + 108) 8 = memLoad mem (sp + 108) 8
  flag : memLoad m (sp + 128) 64 = BitVec.ofNat 64 ok.toNat
  x : savedX m sp = xs
  cube : ∃ us : Limbs, WordsAt m (sp + 144) 64 us ∧
    FieldRepr us ⟨(limbValue xs * limbValue xs * limbValue xs + 7) % modulus,
      Nat.mod_lt _ (by decide)⟩ 8
  frame : RamWriteFrame mem m [⟨(sp - 8).toNat, 192⟩]

def CubeCall (code : CodeMap) : Prop :=
  ∀ (args : Values Value Reg.count) (mem : Ram) (sp a b c d : Word) (ok : Bool),
    args[4].get 64 = sp → (args[0].get 64).setWidth 8 = BitVec.ofNat 8 ok.toNat →
    args[12].get 64 = d &&& 0xfffffffffffff →
    args[13].get 64 = shldResult 12 c d &&& 0xfffffffffffff →
    args[14].get 64 = shldResult 24 b c → args[3].get 64 = shldResult 36 a b →
    args[15].get 64 = a >>> 16 → args[5].get 64 = 0xfffffffffffff →
    Writable code mem (sp - 8) 192 →
    ∃ next m, program.runBlock (dialect code) ⟨.l12065f, args, mem⟩ =
      .call ⟨.l115950, next, m⟩ (callFrame .l120d03 0x120d03) ∧
      CubePost args next mem m sp (maskedX a b c d ok) ok

end K256.Proofs.Sec1.Affine.Compressed
