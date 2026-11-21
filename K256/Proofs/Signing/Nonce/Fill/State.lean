import K256.Proofs.Signing.Nonce.Initialize.State
import K256.Proofs.Verify.LIR.Fn100a40.Frame

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

abbrev sp (fr : Activation) := fr.rsp - 232

def regions (fr : Activation) : List MemoryRegion :=
  [fr.region, ⟨fr.rsi.toNat,32⟩, ⟨(fr.rdi+8).toNat,64⟩]

structure Environment (fr : Activation) : Prop where
  image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  low : fr.low = fr.rsp - 2160
  depth : 2160 ≤ fr.rsp.toNat
  limit : fr.rsp.toNat + 768 < 2^32
  window : Writable Extracted.programImage fr.original fr.rsp 768
  gen : fr.rdi = fr.rsp + 696
  dst : fr.rsi = fr.rsp + 392
  size : fr.rdx = 32
  orderPtr : memLoad fr.original fr.rdi 64 = fr.rsp + 600
  orderWords : WordsAt fr.original (fr.rsp + 600) 64 (scalarWords domain.n)

structure Frame (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn100a40.frameAt .l100ac0 fr)
  widths : ∀ i : Fin Reg.count, i.val ∈ Activation.entryNumbers → a[i].width = 64
  bits : memLoad m (sp fr + 56) 32 = 256
  statePtr : memLoad m (sp fr + 64) 64 = fr.rdi + 8
  valuePtr : memLoad m (sp fr + 136) 64 = fr.rdi + 40
  writes : RamWriteFrame fr.original m (regions fr)

structure Head (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop extends Frame fr a m where
  stateAt : StateAt m (fr.rdi+8) state
  rdi : a[7] = ⟨64,fr.rdi+8⟩
  r12 : a[12] = ⟨64,fr.rdi+40⟩
  rbx : a[3] = ⟨64,0x12a820⟩

structure Generated (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop extends Frame fr a m where
  stateAt : StateAt m (fr.rdi+8) (Drbg.updateValue state)
  bytes : (⟨fr.rsi.toNat,32⟩ : MemoryRegion).HasBytes m (Drbg.updateValue state).value
  rdi : a[7] = ⟨64,fr.rdi+8⟩

structure Updated (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop extends Frame fr a m where
  stateAt : StateAt m (fr.rdi+8) (retry state)
  bytes : (⟨fr.rsi.toNat,32⟩ : MemoryRegion).HasBytes m (Drbg.updateValue state).value

structure Decoded (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop extends Frame fr a m where
  stateAt : StateAt m (fr.rdi+8) (retry state)
  words : WordsAt m (sp fr + 8) 64 (scalarWords (candidate state).1)
  r12 : a[12] = ⟨64,sp fr + 8⟩
  r13 : a[13] = ⟨64,32⟩
  r15 : a[15] = ⟨64,fr.rsp + 600⟩

structure Tested (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop extends Frame fr a m where
  stateAt : StateAt m (fr.rdi+8) (retry state)
  words : WordsAt m (sp fr + 72) 64 (scalarWords (candidate state).1)
  r13 : a[13] = ⟨64,32⟩
  r15 : a[15] = ⟨64,fr.rsp + 600⟩

abbrev testTarget (k : Nat) : Label := if 0 < k ∧ k < domain.n then .l100df5 else .l100dd3

end K256.Proofs.Signing.Nonce.Fill
