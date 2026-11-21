import P256.Proofs.Nonce.Update.Absorb.Seeded.Read
import P256.Proofs.Nonce.Update.Absorb.Seeded.ShortSetup
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure ShortReady [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (index : Nat) (address : BitVec 64) (len : Nat) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a2a3
  current : s.regValue .r14 = initial.regValue .rsi + BitVec.ofNat 64 (16 * index)
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key input
  source : s.regValue .rsi = address
  destination : s.regValue .rdi = scratch initial + 152 + BitVec.ofNat 64 (input.size % 64)
  count : s.regValue .rdx = BitVec.ofNat 64 len
  position : s.regValue .rbx = BitVec.ofNat 64 (input.size % 64)
  length : s.regValue .r15 = BitVec.ofNat 64 len

theorem prepare_short [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : ByteArray} {index len : Nat} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (read : Read initial s state input index address len)
    (short : input.size % 64 + len < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ShortReady initial t state input index address len := by
  obtain ⟨u,step,ready,branch⟩ := jcc_rel8_effect_step 0x10a2e0 2 0xae s
    (readyToStep read.machine read.bindingsSupported)
    (programText_slice (programLoaded_codeIn read.loaded) 0xa2e0 _ (by decide) (by decide +kernel))
    ⟨read.rip,by intro; decide⟩
  have carry : (StatusFlags.ofRFLAGS s.RFLAGS).CF = true := by
    rw [read.carry]
    change decide ((BitVec.ofNat 64 len).toNat < (64 - BitVec.ofNat 64 (input.size % 64)).toNat) = true
    simp only [decide_eq_true_eq]
    bv_omega
  have ripU : u.RIP = 0x10a290 := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then 0x10a290 else 0x10a2e2) = _
    simp only [carry,↓reduceIte]
  have branchRun : Advances boundary 1 s u := Advances.of_step step (.inl (by
    rw [ripU]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa290 (by decide))))
  have a : AgreesExcept [.rip] s u := branch.agrees
  have ctxU := read.toContext.after_nomem pre ready a (by simp) (by simp) (by simp [Component.Covers])
  obtain ⟨fuel,t,run,readyT,_,effect⟩ := ShortSetup.run boundary pre.outerBoundary u ready
    (ShortSetup.code ctxU.loaded) ripU
  have b : AgreesExcept [.reg 3,.reg 0,.reg 7,.reg 6,.reg 2,.flags,.rip] u t := effect.agrees
  have ctxT := ctxU.after_nomem pre readyT b (by simp) (by simp) (by simp [Component.Covers])
  have h := effect.writes
  change t.regValue .rbx = ((u.regValue .rdi).setWidth 32).setWidth 64 ∧
    t.regValue .rax = stackPtr u + 152 ∧ t.regValue .rdi = u.regValue .rdi + (stackPtr u + 152) ∧
    t.regValue .rsi = u.regValue .r12 ∧ t.regValue .rdx = u.regValue .r15 at h
  have p : u.regValue .rdi = BitVec.ofNat 64 (input.size % 64) := (a.read (n:=64) (r:=7) (by simp)).trans read.position
  have source : u.regValue .r12 = address := (a.read (n:=64) (r:=12) (by simp)).trans read.source
  have length : u.regValue .r15 = BitVec.ofNat 64 len := (a.read (n:=64) (r:=15) (by simp)).trans read.length
  rw [p,source,length,ctxU.rsp] at h
  refine ⟨1+fuel,t,branchRun.trans run,ctxT,effect.rip,
    ((a.trans b).read (n:=64) (r:=14) (by simp)).trans read.current,
    read.hmac.copy (fun _ _ => by rw [(a.trans b).external (by simp [Component.Covers])]),
    h.2.2.2.1,?_,h.2.2.2.2,?_, (b.read (n:=64) (r:=15) (by simp)).trans length⟩
  · exact h.2.2.1.trans (by simp only [scratch]; bv_omega)
  · exact h.1.trans (by bv_omega)

end P256.Proofs.Nonce.Update.Absorb.Seeded
