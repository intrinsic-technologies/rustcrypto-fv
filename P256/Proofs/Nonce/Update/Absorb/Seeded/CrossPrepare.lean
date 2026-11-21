import P256.Proofs.Nonce.Update.Absorb.Seeded.Read
import P256.Proofs.Nonce.Update.Absorb.Seeded.CrossSetup
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure CrossReady [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (address : BitVec 64) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a2fd
  current : s.regValue .r14 = initial.regValue .rsi
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key input
  source : s.regValue .rsi = address
  destination : s.regValue .rdi = scratch initial + 185
  count : s.regValue .rdx = 31
  tail : s.regValue .r15 = address + 31
  buffer : s.regValue .r13 = scratch initial + 152
  remaining : s.regValue .rbx = 1

set_option maxHeartbeats 1000000 in
theorem prepare_cross [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (read : Read initial s state input 0 address 32) (size : input.size = 33) :
    ∃ fuel t, Advances boundary fuel s t ∧ CrossReady initial t state input address := by
  have p : s.regValue .rdi = 33 := read.position.trans (by rw [size]; decide +kernel)
  have count : s.regValue .rdx = 31 := read.capacity.trans (by rw [size]; decide +kernel)
  have rem : s.regValue .rbx = 1 := read.remaining.trans (by rw [size]; decide +kernel)
  have carry : (StatusFlags.ofRFLAGS s.RFLAGS).CF = false := read.carry.trans (by rw [size]; decide +kernel)
  obtain ⟨a,stepA,readyA,branchA⟩ := jcc_rel8_effect_step 0x10a2e0 2 0xae s
    (readyToStep read.machine read.bindingsSupported)
    (programText_slice (programLoaded_codeIn read.loaded) 0xa2e0 _ (by decide) (by decide +kernel))
    ⟨read.rip,by intro; decide⟩
  have ripA : a.RIP = 0x10a2e2 := by
    rw [branchA.rip]
    change (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then 0x10a290 else 0x10a2e2) = _
    simp only [carry,Bool.false_eq_true,↓reduceIte]
  have runA : Advances boundary 1 s a := Advances.of_step stepA (.inl (by
    rw [ripA]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa2e2 (by decide))))
  have aa : AgreesExcept [.rip] s a := branchA.agrees
  have ctxA := read.toContext.after_nomem pre readyA aa (by simp) (by simp) (by simp [Component.Covers])
  obtain ⟨b,runB,readyB,test⟩ := (test_r64_r64_effect_step 0x10a2e2 0x48 0xff (by simp [RexWPrefix]) rfl).advances readyA
    (programText_slice (programLoaded_codeIn ctxA.loaded) 0xa2e2 _ (by decide) (by decide +kernel)) ripA
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa2e5 (by decide)))
  have ab : AgreesExcept [.flags,.rip] a b := test.agrees
  have ctxB := ctxA.after_nomem pre readyB ab (by simp) (by simp) (by simp [Component.Covers])
  have zero : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = false := by
    have h := test.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = ((a.regValue .rdi &&& a.regValue .rdi) == 0) at h
    have pa : a.regValue .rdi = 33 := (aa.read (n:=64) (r:=7) (by simp)).trans p
    rw [pa] at h
    exact h.trans (by decide +kernel)
  obtain ⟨c,stepC,readyC,branchC⟩ := jcc_rel32_effect_step 0x10a2e5 4 0xa3 b readyB
    (programText_slice (programLoaded_codeIn ctxB.loaded) 0xa2e5 _ (by decide) (by decide +kernel))
    ⟨test.rip,by intro; decide⟩
  have ripC : c.RIP = 0x10a2eb := by
    rw [branchC.rip]
    change (if (StatusFlags.ofRFLAGS b.RFLAGS).ZF then 0x10a38e else 0x10a2eb) = _
    simp only [zero,Bool.false_eq_true,↓reduceIte]
  have runC : Advances boundary 1 b c := Advances.of_step stepC (.inl (by
    rw [ripC]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa2eb (by decide))))
  have ac : AgreesExcept [.rip] b c := branchC.agrees
  have ctxC := ctxB.after_nomem pre readyC ac (by simp) (by simp) (by simp [Component.Covers])
  have before := (aa.trans ab).trans ac
  obtain ⟨fuel,t,run,readyT,_,effect⟩ := CrossSetup.run boundary pre.outerBoundary c readyC
    (CrossSetup.code ctxC.loaded) ripC
  have ag : AgreesExcept [.reg 15,.reg 13,.reg 7,.reg 6,.flags,.rip] c t := effect.agrees
  have ctxT := ctxC.after_nomem pre readyT ag (by simp) (by simp) (by simp [Component.Covers])
  have h := effect.writes
  change t.regValue .r15 = c.regValue .r12 + c.regValue .rdx ∧ t.regValue .r13 = stackPtr c + 152 ∧
    t.regValue .rdi = c.regValue .rdi + (stackPtr c + 152) ∧ t.regValue .rsi = c.regValue .r12 at h
  have sourceC : c.regValue .r12 = address := (before.read (n:=64) (r:=12) (by simp)).trans read.source
  have countC : c.regValue .rdx = 31 := (before.read (n:=64) (r:=2) (by simp)).trans count
  have pC : c.regValue .rdi = 33 := (before.read (n:=64) (r:=7) (by simp)).trans p
  rw [sourceC,countC,pC,ctxC.rsp] at h
  refine ⟨1+1+1+fuel,t,((runA.trans runB).trans runC).trans run,ctxT,effect.rip,?_,
    read.hmac.copy (fun _ _ => by rw [(before.trans ag).external (by simp [Component.Covers])]),h.2.2.2,?_,
    ((before.trans ag).read (n:=64) (r:=2) (by simp)).trans count,h.1,h.2.1,
    ((before.trans ag).read (n:=64) (r:=3) (by simp)).trans rem⟩
  · have hcur : t.regValue .r14 = initial.regValue .rsi + BitVec.ofNat 64 (16*0) := ((before.trans ag).read (n:=64) (r:=14) (by simp)).trans read.current
    simpa only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hcur
  · exact h.2.2.1.trans (by simp only [scratch]; bv_omega)

end P256.Proofs.Nonce.Update.Absorb.Seeded
