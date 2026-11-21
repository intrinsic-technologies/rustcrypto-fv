import AesGcm.Proofs.Machine.LIR.Fn102bd0.Frame
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.GHASH.Bytes

namespace AesGcm.Proofs.Machine.GHASHInterface
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASH

def MultiplyContract (code : CodeMap) : Prop :=
  CallContract LIR.lifted code .l102bd0 LIR.Fn102bd0.frameInfo
    (fun fr ↦ [span (fr.rdi + 16) 16])
    (fun fr mem ↦ Writable code mem fr.rdi 32 ∧
      (callStack fr).Disjoint (span fr.rdi 32))
    (fun fr mem ↦
      let result := polyvalMultiplyWords
        (fr.rsi ^^^ memLoad fr.original (fr.rdi + 16) 64)
        (fr.rdx ^^^ memLoad fr.original (fr.rdi + 24) 64)
        (memLoad fr.original fr.rdi 64) (memLoad fr.original (fr.rdi + 8) 64)
      memLoad mem (fr.rdi + 16) 64 = result.1 ∧
      memLoad mem (fr.rdi + 24) 64 = result.2)

def updateBlocks (mem : Ram) (src : BitVec 64) (count : Nat)
    (y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range count).foldl (fun acc j ↦ polyvalMultiplyWords
    (acc.1 ^^^ bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16 * j + 8)) 64))
    (acc.2 ^^^ bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16 * j)) 64)) y0 y1) initial

end AesGcm.Proofs.Machine.GHASHInterface
