import K256.Proofs.Generate.Generator.Multiply.Loop.Body.State
import K256.Proofs.Generate.Generator.Multiply.Loop.Memory
import K256.Proofs.Generate.Generator.Entry

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

abbrev roundSp (fr : Activation) := fr.rsp - 0xcb8
abbrev digitPointer (fr : Activation) (k : Nat) := (fr.r9 + BitVec.ofNat 64 (32+k)) + 1
abbrev lookupSite (first : Bool) : Label := if first then .l11f64e else .l11f68a
abbrev lookupResume (first : Bool) : Label := if first then .l11f677 else .l11f69b
abbrev lookupTag (first : Bool) : BitVec 64 := if first then 0x11f677 else 0x11f69b
abbrev additionResume (first : Bool) : Label := if first then .l11f68a else .l11f6a6
abbrev additionTag (first : Bool) : BitVec 64 := if first then 0x11f68a else 0x11f6a6
abbrev tableOffset (first : Bool) : BitVec 64 := if first then 0x850 else 0x490
abbrev windowComponent (first : Bool) (d : Nat) := if first then firstComponent d else secondComponent d
abbrev windowBase (first : Bool) (d : Nat) := if first then firstBase d else secondBase d
abbrev windowIndex (first : Bool) (d k : Nat) := Curve.radixDigit (Curve.radixRemaining (windowComponent first d).natAbs k)

structure WindowCall (fr : Activation) (site child resume : Label) (tag : BitVec 64)
    (a b : Registers) (m : Ram) : Prop where
  step : program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩ =
    .call ⟨child,b,memStore m (roundSp fr - 8) tag⟩ (callFrame resume tag)
  widths : ParseSignature.ArgumentWidths b
  saved : SavedWidths b
  rsp : b[4] = ⟨64,roundSp fr - 8⟩
  control : ∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j]

end K256.Proofs.Generate.Generator.Multiply
