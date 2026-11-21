import ChaCha20Poly1305.Proofs.Decrypt.PrefixEntry
import ChaCha20Poly1305.Proofs.Decrypt.PrefixShim
import ChaCha20Poly1305.Proofs.Decrypt.PrefixAlloc
import ChaCha20Poly1305.Proofs.Decrypt.PrefixCopy

namespace ChaCha20Poly1305.Proofs.Decrypt.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

abbrev layout (e : Short.Env) (x : Inputs e) :=
  Layout.withFrame Short.frameAt Decrypt.doneAt (core e x)

theorem run {e : Short.Env} {x : Inputs e} (hg : Short.Geometry e (2^32)) {c a}
    (h : (layout e x).Rel fnCode c ⟨.entry,#v[],()⟩ a)
    {post : Output Value Ram Reg.count → Prop}
    (finish : ∀ b, (layout e x).Rel fnCode c ⟨.finish,#v[],()⟩ b →
      ∃ o, lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect fnCode) ⟨b,[]⟩ o ∧ post o) :
    ∃ o, lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect fnCode) ⟨a,[]⟩ o ∧ post o := by
  let ret : Output Unit Unit 0 := ⟨#v[],none,()⟩
  apply composeCall (layout e x) (ret := ret) (entryBlock e x hg _ _ _ _ h) rfl
  · intro ctx f rel
    exact composeReturn (layout e x) (shimBlock e x hg _ _ _ _ rel)
  · intro b rel
    apply composeCall (layout e x) (ret := ret) (allocBlock e x hg _ _ _ _ rel) rfl
    · intro ctx f rel
      exact composeReturn (layout e x) (copyBlock e x hg _ _ _ _ rel)
    · exact finish

end ChaCha20Poly1305.Proofs.Decrypt.Prefix
