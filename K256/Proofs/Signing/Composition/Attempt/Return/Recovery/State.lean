import K256.Proofs.Signing.Composition.Attempt.Return.State

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

structure Staged (s : RamState) (d r sigS : Nat) (a : Registers) (m : Ram) : Prop
    extends CoreMemory s d m where
  rsp : a[4] = ⟨64,sp s⟩
  df : a[22] = ⟨1,0⟩
  saved : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64
  args : ParseSignature.ArgumentWidths a
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16
  first : WordsAt m (sp s+192) 64 (scalarWords r)
  second : WordsAt m (sp s+224) 64 (scalarWords sigS)

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
