import P256.Proofs.Ecdh.Normalize.Conversion.Initial
import P256.Proofs.Ecdh.Normalize.Conversion.Round1
import P256.Proofs.Ecdh.Normalize.Conversion.Round2
import P256.Proofs.Ecdh.Normalize.Conversion.Round3
import P256.Proofs.Field.Interface
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic
import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Conversion

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Sec1Serialize (canonicalLimb)

theorem core_correct [Bindings] {t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep t)
    (loaded : ProgramLoaded t) (rip : t.RIP = 0x107d09)
    (readable : MemReadable t (t.regValue .rsi) 32)
    (value : Field.MontgomeryAt t (t.regValue .rsi) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧
      AgreesExcept registers t u ∧ u.RIP = 0x107e15 ∧
      u.regValue .rsi = canonicalLimb x 0 ∧ u.regValue .rcx = canonicalLimb x 1 ∧
      u.regValue .rax = canonicalLimb x 2 ∧ u.regValue .rdx = canonicalLimb x 3 := by
  have st : Stage t t t boundary := ⟨ready,loaded,readable,0,by simp⟩
  obtain ⟨v0,st0,ip0,h0,k0,z0,ag0'⟩ := initial outside st rfl rip
  have ag0 : AgreesExcept registers t v0 := ag0'.mono (by simp [inputRegisters,registers])
  have source0 : v0.regValue .rsi = t.regValue .rsi :=
    ag0'.read (n := 64) (r := 6) (by simp [inputRegisters])
  obtain ⟨v1,st1,ip1,hv1,k1,mask1,half1,ag1⟩ :=
    round1 outside st0 source0 ip0 k0 z0
  have source1 : v1.regValue .rsi = t.regValue .rsi :=
    (ag1.read (n := 64) (r := 6) (by simp [inputRegisters])).trans source0
  obtain ⟨v2,st2,ip2,hv2,k2,mask2,half2,ag2⟩ :=
    round2 outside st1 source1 ip1 k1 mask1 half1
  have source2 : v2.regValue .rsi = t.regValue .rsi :=
    (ag2.read (n := 64) (r := 6) (by simp [inputRegisters])).trans source1
  obtain ⟨u,stu,ipu,hv3,_,_,_,ag3⟩ :=
    round3 outside st2 source2 ip2 k2 mask2 half2
  have ag1' : AgreesExcept registers v0 v1 := ag1.mono (by simp [inputRegisters,registers])
  have ag2' : AgreesExcept registers v1 v2 := ag2.mono (by simp [inputRegisters,registers])
  have ag01 := agrees_trans ag0 ag1'
  have ag012 := agrees_trans ag01 ag2'
  rw [h0.1,h0.2.1,h0.2.2.1,h0.2.2.2,
    read_mem_of_agrees ag0] at hv1
  have h10 := congrArg Prod.fst hv1
  have h11 := congrArg (fun v => v.2.1) hv1
  have h12 := congrArg (fun v => v.2.2.1) hv1
  have h13 := congrArg (fun v => v.2.2.2) hv1
  dsimp only at h10 h11 h12 h13
  rw [h10,h11,h12,h13,read_mem_of_agrees ag01] at hv2
  have h20 := congrArg Prod.fst hv2
  have h21 := congrArg (fun v => v.2.1) hv2
  have h22 := congrArg (fun v => v.2.2.1) hv2
  have h23 := congrArg (fun v => v.2.2.2) hv2
  dsimp only at h20 h21 h22 h23
  rw [h20,h21,h22,h23,read_mem_of_agrees ag012] at hv3
  have values : (u.regValue .rsi,u.regValue .rcx,u.regValue .rax,u.regValue .rdx) =
      Sec1Serialize.Conversion.compilerConversionBV
        (memLoad t.external (t.regValue .rsi) 64)
        (memLoad t.external (t.regValue .rsi+8) 64)
        (memLoad t.external (t.regValue .rsi+16) 64)
        (memLoad t.external (t.regValue .rsi+24) 64) := hv3
  have canonical := values.trans (Sec1Serialize.Conversion.compilerConversionBV_of_montgomeryAt value)
  simp only [Prod.mk.injEq] at canonical
  obtain ⟨fuel,run⟩ := stu.execution
  exact ⟨fuel,u,run,stu.ready,agrees_trans ag012 ag3,ipu,canonical⟩

end P256.Proofs.Ecdh.Normalize.Conversion
