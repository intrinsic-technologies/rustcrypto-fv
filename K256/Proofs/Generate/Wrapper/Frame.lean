import K256.Proofs.Generate.SigningKey
import K256.Proofs.Generate.Memory

namespace K256.Proofs.Generate.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters

abbrev regions (s : RamState) := #v[outputRegion signingKeyGenerateFromRng s,
  Stack.region s signingKeyGenerateFromRng.minStackBytes]

structure CallerFrame (s : RamState) (args : Vector Value Reg.count) (mem : Ram) : Prop where
  rsp : args[4] = ⟨64, s.regValue .rsp - 280⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [5, 12, 13, 15, 22] → args[i] = (Reg.ofIndex i).read s
  rbx : memLoad mem (s.regValue .rsp - 16) 64 = s.regValue .rbx
  r14 : memLoad mem (s.regValue .rsp - 8) 64 = s.regValue .r14
  ret : memLoad mem (s.regValue .rsp) 64 = (returnBoundary s).rip
  writes : RamWriteFrame s.external mem (regions s).toList

abbrev Segment (l : LIR.Label) (args : Vector Value Reg.count) (mem : Ram)
    (l' : LIR.Label) (args' : Vector Value Reg.count) (mem' : Ram) :=
  Run.Reaches ⟨⟨l, args, mem⟩, []⟩ ⟨⟨l', args', mem'⟩, []⟩

abbrev atBytes (p : BitVec 64) (n : Nat) (mem : Ram) (b : ByteArray) :=
  (⟨p.toNat, n⟩ : MemoryRegion).HasBytes mem b

end K256.Proofs.Generate.Wrapper
