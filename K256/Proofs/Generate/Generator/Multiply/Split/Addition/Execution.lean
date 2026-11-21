import K256.Proofs.Generate.Generator.Multiply.Split.Parameters
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Arithmetic
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Machine

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem add : AddExecution := by
  intro fr a m x y entry image order hx hy rx ry dst above sep wx wy
  have ptr := order rfl
  have param := parameterAt image (p := 0x2021a0) (x := domain.n) (by simp [parameters])
  obtain ⟨win, low⟩ : Writable Extracted.programImage m (fr.rsp - 64) 64 ∧
      fr.low.toNat + 64 ≤ fr.rsp.toNat := by
    simp only [Fn1109b0.frameAt, Fn1109b0.frameAtG1, Atom.All, Atom.Holds] at entry
    lifted_inputs entry
    exact ⟨by assumption, by assumption⟩
  have start : (fr.rsp - 64).toNat = fr.rsp.toNat - 64 :=
    BitVec.toNat_sub_of_le (by change 64 ≤ fr.rsp.toNat; omega)
  have dis := param.apart win (by decide)
  rw [start] at dis
  have apart : ∀ src ∈ [fr.rsi, fr.rdx, fr.rcx],
      src.toNat + 32 ≤ fr.rsp.toNat - 64 ∨ fr.rsp.toNat ≤ src.toNat := by
    intro src h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · have h := (sep fr.rsi (by simp)).1
      omega
    · have h := (sep fr.rdx (by simp)).1
      omega
    · rw [ptr]
      omega
  obtain ⟨out, run, tag, done_, widths, words, frame⟩ :=
    Addition.run entry rx ry (ptr ▸ param.readable) dst above apart wx wy (ptr ▸ param.words)
  exact ⟨out, run, tag, done_, widths, Addition.addWords_eq hx hy ▸ words, frame⟩

end K256.Proofs.Generate.Generator.Multiply.Split
