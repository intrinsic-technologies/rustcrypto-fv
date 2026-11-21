import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Parser.ReadSlice

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem writable_of_agrees {s t : RamState} {cs : List Component}
    {a : BitVec 64} {len : Nat} (h : Writable s a len) (ha : AgreesExcept cs s t) :
    Writable t a len :=
  ⟨⟨h.low, fun i hi ↦ ha.grow _ (h.mem i hi)⟩, h.tables⟩

theorem storePre_of_holds {e : Effect} {s t : RamState}
    (h : e.Holds s t) (ho : Obs (e.after s true) t)
    {p : BitVec 64} {codeLen : Nat} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (ha : AddrObs addr)
    (hw : Writable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    Pre p codeLen addr len t := by
  refine ⟨h.rip_of hrip, ?_, RangeApart.carry ho ha hap⟩
  rw [ha.eq ho]
  exact writable_of_agrees hw h.agrees

theorem mov_byte [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Pre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0xc6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8Effect p am imm) := by
  intro s hr hc hp
  apply mov_m8_imm8_effect_step p am hv hx hb imm s hr hc
  exact ⟨hp.rip, ⟨hp.write.low, hp.write.mem, hp.write.tables⟩, hp.code⟩

end P256.Proofs.SignatureFromDer.Parser.ReadSlice
