import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Join
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Tail

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open WindowMachine

theorem window_execute [Bindings] {s : RamState} {boundary : ReturnBoundary} {n i c : Nat} {output : BitVec 64}
    (pre : WindowPre s n i c output) (outer : ¬InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP=(if (n/2^i%32+c)%2=0 then 0x10f43f else 0x10f470) ∧
      t.regValue .rdx=BitVec.ofNat 64 (n/2^i%32+c) ∧ t.regValue .rsi=output ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.flags,.rip] s t := by
  obtain ⟨fuelA,a,runA,readyA,loadedA,ripA,windowA,agreesA⟩ := WindowMachine.join pre outer
  have memoryA := agreesA.external (by simp [Component.Covers])
  have stackA : a.regValue .rsp=s.regValue .rsp := agreesA.read (r:=4) (n:=64) (by simp)
  have carryA : a.regValue .r13=BitVec.ofNat 64 c :=
    (agreesA.read (r:=13) (n:=64) (by simp)).trans pre.carry
  have value : tailValue a=BitVec.ofNat 64 (n/2^i%32+c) := by
    change (a.regValue .rdx &&& memLoad a.external (a.regValue .rsp+40) 64)+a.regValue .r13=_
    rw [memoryA,stackA,pre.mask,windowA,carryA,BitVec.ofNat_add]
  have tailPre : TailPre a := ⟨ripA,by
    rw [stackA]; exact pre.readableMask.of_external_eq memoryA,by
    rw [stackA]; exact pre.readableOutput.of_external_eq memoryA⟩
  obtain ⟨fuelB,b,runB,readyB,_,effect⟩ := tail_block boundary outer a readyA
    (programText_slice (programLoaded_codeIn loadedA) 0xf42d tailBytes
      (by decide) (by decide +kernel)) tailPre
  have agreesB : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.flags,.rip] s b :=
    (agreesA.trans effect.agrees).mono (by simp [tailEffect,Effect.components])
  have memoryB := agreesB.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by
    intro a b fetch; rw [memoryB]; exact pre.loaded a b fetch
  have rdxB : b.regValue .rdx=BitVec.ofNat 64 (n/2^i%32+c) := effect.writes.1.trans value
  have rsiB : b.regValue .rsi=output := by
    have h : b.regValue .rsi=memLoad a.external (a.regValue .rsp+16) 64 := effect.writes.2
    rw [h,memoryA,stackA,pre.outputPointer]
  have zero : (StatusFlags.ofRFLAGS b.RFLAGS).ZF=decide ((n/2^i%32+c)%2=0) := by
    have h := effect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF=(((tailValue a).setWidth 8 &&& 1)==0) at h
    rw [h,value,low_bit_zero]
  have condition : condHolds 5 (StatusFlags.ofRFLAGS b.RFLAGS)=decide ((n/2^i%32+c)%2≠0) := by
    change (!(StatusFlags.ofRFLAGS b.RFLAGS).ZF)=_
    rw [zero]
    by_cases even : (n/2^i%32+c)%2=0 <;> simp [even]
  obtain ⟨t,runT,readyT,loadedT,ripT,agreesT⟩ := Iterator.Advance.branch8 (offset:=0xf43d) 5 0x31
    (decide ((n/2^i%32+c)%2≠0)) readyB loadedB effect.rip condition
    (by decide) (by decide +kernel) (by decide +kernel) (by
      by_cases even : (n/2^i%32+c)%2=0
      · simpa [even,branchTarget,Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0xf43f (by decide))
      · simpa [even,branchTarget,Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0xf470 (by decide)))
  refine ⟨fuelA+fuelB+1,t,(runA.trans runB).trans runT,readyT,loadedT,?_,?_,?_,?_⟩
  · by_cases even : (n/2^i%32+c)%2=0 <;> simpa [even,branchTarget,Extracted.textAddress] using ripT
  · exact (agreesT.read (r:=2) (n:=64) (by simp)).trans rdxB
  · exact (agreesT.read (r:=6) (n:=64) (by simp)).trans rsiB
  · exact (agreesB.trans agreesT).mono (by simp)

end P256.Proofs.Verifying.Combination.Naf.Machine
