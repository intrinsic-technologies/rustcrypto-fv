import K256.Proofs.Signing.Nonce.Initialize.Update.State
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem returnPath {fr : Activation} {input : Input} {state : State} {a : Verify.Core.Registers} {m : Ram}
    (env : Environment fr input) (live : Live .l104951 fr a m state) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l104951, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn103f30.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,64⟩] ∧
      StateAt out.store fr.rdi state := by
  have atoms := live.atoms
  simp only [Fn103f30.frameAt, Fn103f30.frameAtG5, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, mx, ft, fc, bx, r12, r13, r14, r15, bp, retR, retM, retLow, win, _⟩ := atoms
  have ptr : a[4].get 64 = fr.rsp - 712 := congrArg (Value.get 64) rsp
  have depth := env.depth
  have pop (k : BitVec 64) (h : 8 ≤ k.toNat ∧ k.toNat ≤ 48) : LoadOk m (fr.rsp-k) 8 := by
    apply LoadOk.of_region win.readable <;> bv_omega
  have ret : LoadOk m fr.rsp 8 := ⟨retR.low, retR.present⟩
  refine ⟨?_, .done ?run, ?tag, ?restored, ?widths, ?writes, ?bytes⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp (disch := decide) only [ptr, reduceAddOffset, BitVec.sub_add_cancel, pop, ret, retM,
      retLow, bx, bp, r12, r13, r14, r15, and_self, ite_true]
    rfl
  case writes => exact live.writes
  case bytes => exact live.bytes
  case tag => rfl
  case restored => exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ft, fc, trivial⟩
  case widths =>
    rintro ⟨i, hi⟩ mem
    have old := live.widths rfl ⟨i, hi⟩ mem
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> exact old

end K256.Proofs.Signing.Nonce.Initialize.Update
