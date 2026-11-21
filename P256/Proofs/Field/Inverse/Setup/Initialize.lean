import P256.Proofs.Field.Inverse.Setup.ParameterValues
import P256.Proofs.Field.Inverse.Setup.Saved

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

set_option exponentiation.threshold 512 in
theorem inverse_parameters [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ n t, Advances boundary n s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x114119 ∧ stackPtr t = stackPtr s-168 ∧
      t.regValue .rbx = s.regValue .rdi ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.regValue .rdi = stackPtr s-168 ∧ t.regValue .rdx = stackPtr s-128 ∧
      t.regValue .r8 = stackPtr s-96 ∧ t.regValue .rcx = 0xffffffffffffffff ∧
      AgreesExcept (setupComponents s) s t ∧
      Nat256At t (stackPtr s-128) P256.Spec.Operations.domain.p ∧
      Nat256At t (stackPtr s-96) (2^512 % P256.Spec.Operations.domain.p) ∧
      SavedWords s t := by
  obtain ⟨a,runa,ra,_,ipa,spa,bxa,sia,memorya,aga,_⟩ := inverse_entry pre
  have aa : AgreesExcept (setupComponents s) s a := aga.mono (by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · have cases : c = .reg 3 ∨ c = .rip := by simpa using hc
      rcases cases with rfl | rfl <;> simp [setupComponents])
  obtain ⟨nb,b,runb,rb,spb,ab,ipb,eb⟩ :=
    parameter_word_run pre ra spa aa 0 ipa
  obtain ⟨nc,c,runc,rc,spc,ac,ipc,ec⟩ :=
    parameter_word_run pre rb spb ab 1 ipb
  obtain ⟨nd,d,rund,rd,spd,ad,ipd,ed⟩ :=
    parameter_word_run pre rc spc ac 2 ipc
  obtain ⟨ne,e,rune,re,spe,ae,ipe,ee⟩ :=
    parameter_word_run pre rd spd ad 3 ipd
  obtain ⟨nf,f,runf,rf,spf,af,ipf,ef⟩ := parameter_middle_run pre re spe ae ipe
  obtain ⟨ng,g,rung,rg,spg,ag,ipg,eg⟩ :=
    parameter_word_run pre rf spf af 4 ipf
  obtain ⟨nh,h,runh,rh,sph,ah,iph,eh⟩ :=
    parameter_word_run pre rg spg ag 5 ipg
  obtain ⟨nj,j,runj,rj,spj,aj,ipj,ej⟩ :=
    parameter_word_run pre rh sph ah 6 iph
  obtain ⟨nk,k,runk,rk,spk,ak,ipk,ek⟩ :=
    parameter_word_run pre rj spj aj 7 ipj
  obtain ⟨nl,t,runt,rt,spt,agt,ipt,et⟩ := parameter_arguments_run pre rk spk ak ipk
  have savedA := entry_saved_words memorya
  have savedB := savedA.after_frame pre (parameter_word_frame pre spa 0 eb)
  have savedC := savedB.after_frame pre (parameter_word_frame pre spb 1 ec)
  have savedD := savedC.after_frame pre (parameter_word_frame pre spc 2 ed)
  have savedE := savedD.after_frame pre (parameter_word_frame pre spd 3 ee)
  have savedF := savedE.after_frame pre (parameter_middle_frame pre spe ef)
  have savedG := savedF.after_frame pre (parameter_word_frame pre spf 4 eg)
  have savedH := savedG.after_frame pre (parameter_word_frame pre spg 5 eh)
  have savedJ := savedH.after_frame pre (parameter_word_frame pre sph 6 ej)
  have savedK := savedJ.after_frame pre (parameter_word_frame pre spj 7 ek)
  have savedT := saved_words_arguments savedK et
  have va : CopiedParameters s a 0 := by intro i hi; omega
  have vb := copied_parameters_word spa (setup_loaded pre aa) 0 va eb
  have vc := copied_parameters_word spb (setup_loaded pre ab) 1 vb ec
  have vd := copied_parameters_word spc (setup_loaded pre ac) 2 vc ed
  have ve := copied_parameters_word spd (setup_loaded pre ad) 3 vd ee
  have vf := copied_parameters_middle spe ve ef
  have vg := copied_parameters_word spf (setup_loaded pre af) 4 vf eg
  have vh := copied_parameters_word spg (setup_loaded pre ag) 5 vg eh
  have vj := copied_parameters_word sph (setup_loaded pre ah) 6 vh ej
  have vk := copied_parameters_word spj (setup_loaded pre aj) 7 vj ek
  have vt := copied_parameters_arguments vk et
  have values := parameter_values pre agt vt
  have r8f : f.regValue .r8 = stackPtr e+72 := ef.writes.2
  have r8g : g.regValue .r8 = f.regValue .r8 :=
    eg.agrees.read (n := 64) (r := 8) (by simp [wordEffect, RipCopy.effect, Effect.components])
  have r8h : h.regValue .r8 = g.regValue .r8 :=
    eh.agrees.read (n := 64) (r := 8) (by simp [wordEffect, RipCopy.effect, Effect.components])
  have r8j : j.regValue .r8 = h.regValue .r8 :=
    ej.agrees.read (n := 64) (r := 8) (by simp [wordEffect, RipCopy.effect, Effect.components])
  have r8k : k.regValue .r8 = j.regValue .r8 :=
    ek.agrees.read (n := 64) (r := 8) (by simp [wordEffect, RipCopy.effect, Effect.components])
  have r8t : t.regValue .r8 = k.regValue .r8 :=
    et.agrees.read (n := 64) (r := 8) (by simp [parameterArgumentEffect, Effect.components])
  refine ⟨_,t,(((((((((runa.trans runb).trans runc).trans rund).trans rune).trans runf).trans rung).trans runh).trans runj).trans runk).trans runt,
    rt,setup_loaded pre agt,ipt,spt,?_,?_,?_,?_,?_,?_,agt,values.1,values.2,savedT⟩
  · calc
      t.regValue .rbx = k.regValue .rbx := et.agrees.read (n := 64) (r := 3)
        (by simp [parameterArgumentEffect, Effect.components])
      k.regValue .rbx = j.regValue .rbx := ek.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      j.regValue .rbx = h.regValue .rbx := ej.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      h.regValue .rbx = g.regValue .rbx := eh.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      g.regValue .rbx = f.regValue .rbx := eg.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      f.regValue .rbx = e.regValue .rbx := ef.agrees.read (n := 64) (r := 3)
        (by simp [parameterMiddleEffect, Effect.components])
      e.regValue .rbx = d.regValue .rbx := ee.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      d.regValue .rbx = c.regValue .rbx := ed.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      c.regValue .rbx = b.regValue .rbx := ec.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      b.regValue .rbx = a.regValue .rbx := eb.agrees.read (n := 64) (r := 3)
        (by simp [wordEffect, RipCopy.effect, Effect.components])
      _ = s.regValue .rdi := bxa
  · exact agt.read (n := 64) (r := 6) (by simp [setupComponents, entryComponents, pushSequenceFrame])
  · exact et.writes.1.trans spk
  · have h := et.writes.2.1
    change t.regValue .rdx = stackPtr k+40 at h
    rw [h,spk]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · rw [r8t,r8k,r8j,r8h,r8g,r8f,spe]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · exact et.writes.2.2

end P256.Proofs.Field.Inverse
