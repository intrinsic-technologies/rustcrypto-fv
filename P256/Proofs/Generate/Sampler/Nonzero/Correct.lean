import P256.Proofs.Generate.Sampler.Nonzero.Copy
import P256.Proofs.Generate.Sampler.Nonzero.Arguments
import P256.Proofs.Generate.Sampler.Nonzero.Preserve
import P256.Proofs.Generate.Sampler.Nonzero.Branch

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    {offset x : Nat} (pre : Pre s boundary input)
    (state : LoopReady s t input offset 0x100c00 32)
    (scalar : Nat256At t (stackPtr s-184) x)
    (_remaining : t.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)))
    (available : offset+32 ≤ input.size) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      (if x=0 then LoopReady s u input (offset+32) else
        State s u ∧ u.RIP=0x100d1d ∧ Nat256At u (stackPtr s-256) x ∧
          memLoad u.external (stackPtr s-192) 64 = s.regValue .rdi) := by
  have addr8 (q : RamState) (st : State s q) :
      stackPtr q+80#64 = stackPtr s-184#64 :=
    scalar_stack_address (frameOffset := 264) st.rsp (by decide) (by decide)
  have addr56 (q : RamState) (st : State s q) :
      stackPtr q+8#64 = stackPtr s-256#64 :=
    scalar_stack_address (frameOffset := 264) st.rsp (by decide) (by decide)
  have addr48 (q : RamState) (st : State s q) :
      stackPtr q+72#64 = stackPtr s-192#64 :=
    scalar_stack_address (frameOffset := 264) st.rsp (by decide) (by decide)
  obtain ⟨na,a,ra,sa,ipa,copies,ga⟩ := copy pre state.toState state.rip
    (by simpa only [BitVec.ofNat_eq_ofNat,addr8 t state.toState] using scalar)
  have xa := copies 8 (by simp)
  have ya := copies 184 (by simp)
  simp only [BitVec.ofNat_eq_ofNat] at xa ya
  obtain ⟨nb,b,rb,sb,ipb,zb,gb⟩ := clear pre sa ipa
  have gab := clear_tail sa gb
  have addr88 (q : RamState) (st : State s q) :
      stackPtr q+184#64 = stackPtr s-80#64 :=
    scalar_stack_address (frameOffset := 264) st.rsp (by decide) (by decide)
  have xb : Nat256At b (stackPtr s-80) x := by
    rw [addr88 a sa] at ya
    exact ⟨ya.1,fun i hi => (tail_byte pre gab (by decide) (by decide) i hi).trans (ya.2 i hi)⟩
  have r15b : b.regValue .r15 = stackPtr b+80 := by
    change b.regValue .r15 = stackPtr b+80#64
    rw [addr8 b sb]
    exact ((ga.trans gab).read (n := 64) (r := 15)
      (by simp [copyClobbers,tailClobbers])).trans state.decoded
  obtain ⟨c,rc,sc,ipc,dic,sic,gc⟩ := prepare_zero pre sb ipb r15b
  have spc : stackPtr c = stackPtr b := gc.read (n := 64) (r := 4) (by simp)
  have memc := gc.external (by simp [Component.Covers])
  obtain ⟨nd,d,rd,sd,ipd,vd,gd⟩ := zero_call pre sc ipc
    (by simpa only [Nat256At,memc] using xb)
    (by simpa only [Nat256At,memc,BitVec.ofNat_eq_ofNat,addr8 b sb] using zb)
    (dic.trans (addr88 c sc)) (sic.trans (addr8 c sc))
  obtain ⟨e,re,se,ipe,ve,ge⟩ := invert pre sd ipd vd
  obtain ⟨f,rf,sf,ipf,vf,gf⟩ := choice pre se ipe
  have tail : AgreesExcept (tailClobbers s) a f := by
    exact ((((gab.trans gc).trans gd).trans ge).trans gf).mono
      (by simp [tailClobbers,zeroClobbers,choiceClobbers])
  have vf' : (f.regValue .rax).setWidth 8 = (if x=0 then 0 else 1) := by
    rw [vf,ve]
    split <;> rfl
  obtain ⟨g,rg,sg,ipg,count,gg⟩ := decrement pre sf ipf
  obtain ⟨u,⟨nu,ru⟩,su,ipu,gu⟩ := branch pre sg ipg
  have after : AgreesExcept [.reg 13,.flags,.rip] f u := (gg.trans gu).mono (by simp)
  have memu := after.external (by simp [Component.Covers])
  have xu : Nat256At u (stackPtr s-256) x := by
    rw [addr56 a sa] at xa
    refine ⟨xa.1,fun i hi => ?_⟩
    rw [memu]
    exact (tail_byte pre tail (by decide) (by decide) i hi).trans (xa.2 i hi)
  have outa : memLoad a.external (stackPtr s-192) 64 = s.regValue .rdi := by
    have addr := addr48 t state.toState
    change memLoad a.external (stackPtr s-192#64) 64 = _
    rw [←addr]
    have before : memLoad t.external (stackPtr t+72#64) 64 = s.regValue .rdi := by
      rw [addr]; exact state.output
    apply Eq.trans (b := memLoad t.external (stackPtr t+72#64) 64) ?_ before
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact copy_byte ga (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide) i hi
  have outu : memLoad u.external (stackPtr s-192) 64 = s.regValue .rdi := by
    rw [memu]
    apply Eq.trans _ outa
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact tail_byte pre tail (by decide) (by decide) i hi
  have finalRip : u.RIP = if x=0 then 0x100c94 else 0x100d1d := by
    have ax : (g.regValue .rax).setWidth 8 = (if x=0 then 0 else 1) := by
      have keep : g.regValue .rax = f.regValue .rax := gg.read (n := 64) (r := 0) (by simp)
      rw [keep]
      exact vf'
    rw [ipu,ax]
    split <;> rfl
  have combined := (ga.trans tail).trans after
  refine ⟨u,⟨_,(((((((ra.trans rb).trans rc).trans rd).trans re).trans rf).trans rg).trans ru)⟩,?_⟩
  split
  next hx =>
    refine ⟨su,?_,?_,?_,?_,?_,?_,outu⟩
    · simpa only [hx,ite_true] using finalRip
    · exact (combined.read (n := 64) (r := 14)
        (by simp [copyClobbers,tailClobbers])).trans state.descriptor
    · exact (combined.read (n := 64) (r := 5)
        (by simp [copyClobbers,tailClobbers])).trans state.source
    · have h : f.regValue .r13 = t.regValue .r13 :=
        (ga.trans tail).read (n := 64) (r := 13) (by simp [copyClobbers,tailClobbers])
      have keep : u.regValue .r13 = g.regValue .r13 := gu.read (n := 64) (r := 13) (by simp)
      rw [keep,count,h,state.remaining]
      have eq : input.size-offset = (input.size-(offset+32))+32 := by omega
      rw [eq,BitVec.ofNat_add]
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_sub_cancel]
    · exact (combined.read (n := 64) (r := 15)
        (by simp [copyClobbers,tailClobbers])).trans state.decoded
    · exact (combined.read (n := 64) (r := 12)
        (by simp [copyClobbers,tailClobbers])).trans state.buffer
  next hx =>
    exact ⟨su,by simpa only [hx,ite_false] using finalRip,xu,outu⟩

end P256.Proofs.Generate.Sampler.Nonzero
