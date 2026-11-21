import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Sec1.Parser.Affine
import K256.Proofs.Common.Finish

namespace K256.Proofs.Generate

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters

structure KeyReady (initial : RamState) (random : ByteArray) (args : Vector Value Reg.count)
    (mem : Ram) (d : Nat) (point : Curve.Point) : Prop where
  scalar : K256.Spec.Secp256k1.randomSecret random = some d
  publicKey : Keys.publicKey Secp256k1.domain (Encoding.natToOctets 32 d) = some point
  limbs : WordsAt mem (initial.regValue .rsp - 192) 64
    (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2 ^ (64 * i.val)))
  affine : Sec1.Parser.PublicKeyAt mem (initial.regValue .rsp - 160) point
  rsp : args[4] = ⟨64, initial.regValue .rsp - 280⟩
  dst : args[3] = ⟨64, initial.regValue .rdi⟩
  key : args[14] = ⟨64, initial.regValue .rsp - 192⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [5, 12, 13, 15, 22] → args[i] = (Reg.ofIndex i).read initial
  rbx : memLoad mem (initial.regValue .rsp - 16) 64 = initial.regValue .rbx
  r14 : memLoad mem (initial.regValue .rsp - 8) 64 = initial.regValue .r14
  ret : memLoad mem (initial.regValue .rsp) 64 = (returnBoundary initial).rip
  writes : RamWriteFrame initial.external mem [Stack.region initial signingKeyGenerateFromRng.minStackBytes]

noncomputable abbrev Run := LIR.program.sem (dialect Extracted.programImage)

theorem execution_of_key {initial : RamState} {random : ByteArray}
    (generate : ∃ args mem d point, Run.Reaches ⟨LIR.lifted.locationOf .l102510 initial, []⟩
      ⟨⟨.l102539, args, mem⟩, []⟩ ∧ KeyReady initial random args mem d point)
    (serialize : ∀ args mem d point, KeyReady initial random args mem d point →
      ∃ out, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l102539, args, mem⟩, []⟩ out ∧
        Common.Returned initial #v[outputRegion signingKeyGenerateFromRng initial,
          Stack.region initial signingKeyGenerateFromRng.minStackBytes] out ∧
        (outputRegion signingKeyGenerateFromRng initial).HasBytes out.store
          (K256.Spec.Secp256k1.generatedSigningKey random)) :
    ∃ out, LIR.program.Exec (dialect Extracted.programImage)
      ⟨LIR.lifted.locationOf .l102510 initial, []⟩ out ∧
        Common.Returned initial #v[outputRegion signingKeyGenerateFromRng initial,
          Stack.region initial signingKeyGenerateFromRng.minStackBytes] out ∧
        (outputRegion signingKeyGenerateFromRng initial).HasBytes out.store
          (K256.Spec.Secp256k1.generatedSigningKey random) := by
  obtain ⟨args, mem, d, point, steps, key⟩ := generate
  obtain ⟨out, finish, post⟩ := serialize args mem d point key
  exact ⟨out, Program.Exec.of_sem (steps.exec finish.sem), post⟩

end K256.Proofs.Generate
