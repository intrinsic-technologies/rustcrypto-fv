import P256.Proofs.EcdhWrapper.Finish.Copy.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions P256.Proofs.Common.Der.Decode.Header

theorem check_capacity [Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : stackPtr s=stackPtr initial-504) (rip : s.RIP=0x106bd5)
    (saved : memLoad s.external (stackPtr initial-464) 64=initial.regValue .r8) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧ ReadyToStep t ∧
      t.RIP=0x106be4 ∧ t.regValue .r8=initial.regValue .r8 ∧
      AgreesExcept [.reg 8,.flags,.rip] s t := by
  obtain ⟨a,ra,ha,ea⟩ := (mov_r64_m64_effect_step 0x106bd5 0x4c (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6bd5 _ (by decide) (by decide +kernel))
    ⟨rip,Peer.Buffer.readable call grow rsp (off := 40) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bda (by decide)))
  have ga : AgreesExcept [.reg 8,.rip] s a := ea.agrees
  have r8 : a.regValue .r8=initial.regValue .r8 := by
    have h : a.regValue .r8=memLoad s.external (stackPtr s+40) 64 := ea.writes
    rw [h]
    change memLoad s.external (stackPtr s+BitVec.ofNat 64 40) 64=_
    rw [Peer.Buffer.address rsp (off := 40) (by decide)]
    exact saved
  have la : ProgramLoaded a := by
    simpa only [ProgramLoaded,ga.external (by simp [Component.Covers])] using loaded
  obtain ⟨b,rb,hb,eb⟩ := (cmp_r64_imm8_effect_step 0x106bda 0x49 0xf8 39
    (by simp [RexWPrefix]) rfl rfl).advances ha
    (programText_slice (programLoaded_codeIn la) 0x6bda _ (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bde (by decide)))
  have gb : AgreesExcept [.flags,.rip] a b := eb.agrees
  have lb : ProgramLoaded b := by
    simpa only [ProgramLoaded,gb.external (by simp [Component.Covers])] using la
  have cf : (StatusFlags.ofRFLAGS b.RFLAGS).CF=false := by
    have h := eb.flags.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).CF=decide ((a.regValue .r8).toNat<39) at h
    rw [h,r8]
    exact decide_eq_false (by have := capacity call; omega)
  have zf : (StatusFlags.ofRFLAGS b.RFLAGS).ZF=false := by
    have h := eb.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF=((a.regValue .r8-39)==0) at h
    rw [h,r8]
    apply Bool.eq_false_iff.mpr
    intro hz
    have eq : initial.regValue .r8=39 := by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using
        BitVec.sub_eq_iff_eq_add.mp (of_decide_eq_true hz)
    have hn := congrArg BitVec.toNat eq
    have := capacity call
    change (initial.regValue .r8).toNat=39 at hn
    omega
  obtain ⟨t,rt,ht,et⟩ := (jcc_rel32_not_taken_effect_step 0x106bde 6 0x10f).advances hb
    (programText_slice (programLoaded_codeIn lb) 0x6bde _ (by decide) (by decide +kernel))
    ⟨eb.rip,by change (_ || _)=false; rw [cf,zf]; rfl⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6be4 (by decide)))
  have gt : AgreesExcept [.rip] b t := et.agrees
  exact ⟨t,(ra.trans rb).trans rt,ht,et.rip,
    ((gb.trans gt).read (n := 64) (r := 8) (by simp)).trans r8,
    ((ga.trans gb).trans gt).mono (by simp)⟩

end P256.Proofs.EcdhWrapper.Finish.Copy
