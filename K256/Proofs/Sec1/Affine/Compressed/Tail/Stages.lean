import K256.Proofs.Sec1.Affine.Compressed.Phases
import K256.Proofs.Sec1.Affine.Compressed.Parity

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

def selectWrites (sp : Word) : List MemoryRegion :=
  [⟨(sp-121).toNat,121⟩, ⟨(sp+8).toNat,16⟩, ⟨(sp+32).toNat,16⟩,
   ⟨(sp+96).toNat,8⟩, ⟨(sp+184).toNat,248⟩]

structure NormalizeAt (code : CodeMap) (args next : Values Value Reg.count) (mem m : Ram)
    (sp ret : Word) (src dst : Nat) (a : Limbs) (ok : Bool) : Prop where
  rsp : next[4] = ⟨64, sp-8⟩
  rsi : next[6] = ⟨64, sp + BitVec.ofNat 64 src⟩
  rdi : next[7] = ⟨64, sp + BitVec.ofNat 64 dst⟩
  wide : ∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15] → next[i] = ⟨64,next[i].get 64⟩
  kept : ∀ i : Fin 53, i.val ∈ [22,39,50,51] → next[i] = args[i]
  slot : memLoad m (sp-8) 64 = ret
  words : WordsAt m (sp + BitVec.ofNat 64 src) 64 a
  flag : memLoad m (sp+32) 8 = BitVec.ofNat 8 ok.toNat
  frame : RamWriteFrame mem m (selectWrites sp)

end K256.Proofs.Sec1.Affine.Compressed
