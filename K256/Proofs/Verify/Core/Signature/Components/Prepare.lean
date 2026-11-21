import K256.Proofs.Verify.Core.Signature.Components.State
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Components

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Generate.Generator.Multiply (scalarWords)
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem first {fr : Activation} {a : Registers} {p d r s} (e : Entry fr a p d r s)
    (sp : Word) (hs : sp = localSp fr)
    (stack : Writable Extracted.programImage fr.original (sp - 24) 512)
    (sig : Readable fr.original (sp + 848) 64)
    (loads : Loads fr.original sp 848 (scalarWords r)) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104f20,a,fr.original⟩ =
        .call ⟨.l10a280,b,stage (saveRegs fr sp) sp 0x104fa4 (scalarWords r)⟩ (resumeAt .l104fa4 0x104fa4) ∧
      Arguments fr b := by
  have ent := e.atoms
  simp only [Fn104f20.frameAt,Fn104f20.frameAtG6,Atom.All,Atom.Holds] at ent
  obtain ⟨rsp,df,rcx,rdx,rbx,rbp,rsi,rdi,r8,r9,r12,r13,r14,r15,mx,ft,fc,_⟩ := ent
  have rs : a[4].get 64 = sp + 488 := (congrArg (Value.get 64) rsp).trans (by rw [hs]; exact (BitVec.sub_add_cancel ..).symm)
  have base : fr.r8 = sp + 848 := by rw [hs,e.sig]; dsimp only [localSp]; bv_omega
  have g15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have g14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have g13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have g12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have g3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) rbx
  have g1 : a[1].get 64 = fr.rcx := congrArg (Value.get 64) rcx
  have g2 : a[2].get 64 = fr.rdx := congrArg (Value.get 64) rdx
  have g6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) rsi
  have g7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) rdi
  have g8 : a[8].get 64 = sp + 848 := (congrArg (Value.get 64) r8).trans base
  obtain ⟨l0,l1,l2,l3⟩ := loads
  change memLoad _ (sp + 848) 64 = _ at l0
  change memLoad _ (sp + 856) 64 = _ at l1
  change memLoad _ (sp + 864) 64 = _ at l2
  change memLoad _ (sp + 872) 64 = _ at l3
  unfold saveRegs
  generalize hm : fr.original = m at stack sig l0 l1 l2 l3 ⊢
  refine ⟨?b,?run,?args⟩
  case run =>
    unfold stage
    cfg_eval [rs,g15,g14,g13,g12,g3,g1,g2,g6,g7,g8]
    segment_words [l0,l1,l2,l3]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104f20)
    rfl
  case args =>
    subst sp
    refine ⟨⟨rfl,rbp,rfl,rfl,rfl,?_,df,mx,ft,fc⟩,rfl,rfl,rfl,rfl,
      congrArg Value.width rdx,congrArg Value.width r8,congrArg Value.width r9⟩
    exact congrArg (Value.mk 64) base.symm

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem second {fr : Activation} {a : Registers} {m : Ram} {r s : Nat}
    (f : Fixed fr a) (sp : Word) (hs : sp = localSp fr) (rsp : a[4].get 64 = sp)
    (base : fr.r8 = sp + 848) (dx : a[2].width = 64) (r8 : a[8].width = 64) (r9 : a[9].width = 64)
    (stack : Writable Extracted.programImage m (sp - 24) 512)
    (sig : Readable m (sp + 848) 64) (lr : Loads m sp 848 (scalarWords r))
    (ls : Loads m sp 880 (scalarWords s)) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104fbc,a,m⟩ =
      .call ⟨.l10a280,b,stage (saveR m sp (scalarWords r)) sp 0x105051 (scalarWords s)⟩
        (resumeAt .l105051 0x105051) ∧ Arguments fr b := by
  obtain ⟨r0,r1,r2,r3⟩ := lr
  obtain ⟨s0,s1,s2,s3⟩ := ls
  change memLoad m (sp + 848) 64 = _ at r0
  change memLoad m (sp + 856) 64 = _ at r1
  change memLoad m (sp + 864) 64 = _ at r2
  change memLoad m (sp + 872) 64 = _ at r3
  change memLoad m (sp + 880) 64 = _ at s0
  change memLoad m (sp + 888) 64 = _ at s1
  change memLoad m (sp + 896) 64 = _ at s2
  change memLoad m (sp + 904) 64 = _ at s3
  refine ⟨?b,?run,?args⟩
  case run =>
    have sigPtr : a[15].get 64 = sp + 848 := (congrArg (Value.get 64) f.r15).trans base
    cfg_eval [rsp,sigPtr]
    segment_words [r0,r1,r2,r3,s0,s1,s2,s3]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104fbc)
    rfl
  case args =>
    subst sp
    exact ⟨⟨f.bx,f.bp,f.r12,f.r13,f.r14,f.r15,f.df,f.mx,f.ft,f.fc⟩,rfl,rfl,rfl,rfl,dx,r8,r9⟩

end K256.Proofs.Verify.Core.Components
