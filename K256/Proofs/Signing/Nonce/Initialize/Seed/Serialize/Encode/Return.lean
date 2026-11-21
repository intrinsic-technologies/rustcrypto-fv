import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.State
import K256.Proofs.Verify.LIR.Generated.Values

import K256.Proofs.Verify.LIR.Fn100000.Frame

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

theorem Encode.finish {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (depth : 208 ≤ fr.rsp.toNat)
    (loop : Encode.Loop fr x 4 a m) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨Encode.label 4,a,m⟩,[]⟩ out ∧
      out.store = m ∧ out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn100000.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values := by
  have atoms := loop.atoms
  change Atom.All _ _ _ (Fn100000.frameAt .l100153 fr) at atoms
  simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,mx,ft,fc,bx,r12,r13,r14,r15,bp,rr,ret,retLow,area,_⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 72 := congrArg (Value.get 64) sp
  have offset (k : Nat) (hk : k ≤ 208) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have small : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [small]; omega)),small]
  have floor : (fr.rsp - 208).toNat = fr.rsp.toNat - 208 := offset 208 (by decide)
  have pop (k : Nat) (hk : k ≤ 48) (hk' : 8 ≤ k) :
      LoadOk m (fr.rsp - BitVec.ofNat 64 k) 8 := by
    apply LoadOk.of_region area.readable
    · rw [offset k (by omega),floor]
      omega
    · rw [offset k (by omega),floor]
      omega
  have retOk : LoadOk m fr.rsp 8 := ⟨rr.low,rr.present⟩
  have p8 : LoadOk m (fr.rsp - 8) 8 := pop 8 (by decide) (by decide)
  have p16 : LoadOk m (fr.rsp - 16) 8 := pop 16 (by decide) (by decide)
  have p24 : LoadOk m (fr.rsp - 24) 8 := pop 24 (by decide) (by decide)
  have p32 : LoadOk m (fr.rsp - 32) 8 := pop 32 (by decide) (by decide)
  have p40 : LoadOk m (fr.rsp - 40) 8 := pop 40 (by decide) (by decide)
  have p48 : LoadOk m (fr.rsp - 48) 8 := pop 48 (by decide) (by decide)
  refine ⟨?_, .done ?run, ?mem, ?tag, ?atoms, ?widths⟩
  case run =>
    change program.step _ ⟨⟨.l100153,a,m⟩,[]⟩ = _
    unfold Program.step
    cfg_eval
    simp only [rsp, Lift.reduceAddOffset, BitVec.sub_add_cancel, p48, p40, p32, p24, p16, p8,
      bx,r12,r13,r14,r15,bp,retOk,ret,retLow,and_self,↓reduceIte]
    rfl
  case mem => rfl
  case tag => rfl
  case atoms => exact ⟨rfl,df,rfl,rfl,rfl,rfl,rfl,rfl,mx,ft,fc,trivial⟩
  case widths =>
    rintro ⟨i,hi⟩ member
    have width := loop.widths ⟨i,hi⟩ member
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact width

end K256.Proofs.Signing.Nonce.Initialize
