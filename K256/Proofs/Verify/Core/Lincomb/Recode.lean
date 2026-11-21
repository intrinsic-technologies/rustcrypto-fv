import K256.Proofs.Verify.Core.Lincomb.Recode.Execution

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem recode {a : Registers} {m : Ram} {sp dst src : BitVec 64} {n : Nat}
    (entry : RoutineEntry a m sp 0x110) (di : a[7].get 64 = dst) (si : a[6].get 64 = 257)
    (dx : a[2].get 64 = src) (cx : a[1].get 64 = 16) (r8 : a[8].get 64 = 128)
    (r9 : a[9].get 64 = 5) (bound : n < 2^128)
    (input : memLoad m src 128 = BitVec.ofNat 128 n) (read : Readable m src 16)
    (zero : DigitBytes m dst []) (write : Writable Extracted.programImage m dst 257)
    (source : Outside [scratch sp 0x110, ⟨dst.toNat, 257⟩] src 16)
    (dest : Outside [scratch sp 0x110, ⟨sp.toNat, 8⟩] dst 257) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1107b0, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 0x110 [⟨dst.toNat, 257⟩] out ∧
      out.values[0] = ⟨64, BitVec.ofNat 64 (Naf.digits n).length⟩ ∧
      DigitBytes out.store dst (Naf.digits n) := by
  have h := Recode.execute ⟨entry, write, dest⟩ di si dx cx r8 r9 read zero source
  have nat : (memLoad m src 128).toNat = n := by
    rw [input, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  simpa only [nat] using h

end K256.Proofs.Verify.Core.Lincomb
