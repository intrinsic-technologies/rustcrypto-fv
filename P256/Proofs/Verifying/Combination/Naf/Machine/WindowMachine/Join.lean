import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Select
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Within
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Cross
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Values

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem join [Bindings] {s : RamState} {boundary : ReturnBoundary} {n i c : Nat} {output : BitVec 64}
    (pre : WindowPre s n i c output) (outer : ¬InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP=0x10f42d ∧ t.regValue .rdx &&& 31=BitVec.ofNat 64 (n/2^i%32) ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.flags,.rip] s t := by
  obtain ⟨a,runA,readyA,loadedA,ripA,agreesA⟩ := select pre.ready pre.loaded pre.rip
    pre.index pre.width (Nat.mod_lt _ (by decide)) outer
  have first : a.regValue .rax=Iterator.word n (i/64) :=
    (agreesA.read (r:=0) (n:=64) (by simp)).trans pre.first
  have second : a.regValue .rdx=Iterator.word n (i/64+1) :=
    (agreesA.read (r:=2) (n:=64) (by simp)).trans pre.second
  have index : a.regValue .rbx=BitVec.ofNat 64 (i%64) :=
    (agreesA.read (r:=3) (n:=64) (by simp)).trans pre.index
  have negative : a.regValue .rbp= -BitVec.ofNat 64 i :=
    (agreesA.read (r:=5) (n:=64) (by simp)).trans pre.negative
  by_cases within : i%64+5<64
  · obtain ⟨fuel,t,runT,readyT,_,effect⟩ := within_block boundary outer a readyA
      (programText_slice (programLoaded_codeIn loadedA) 0xf408 withinBytes
        (by decide) (by decide +kernel)) (by simpa only [within,↓reduceIte] using ripA)
    have agrees : AgreesExcept [.reg 0,.reg 1,.reg 2,.flags,.rip] s t :=
      (agreesA.trans effect.agrees).mono (by simp [withinEffect,Effect.components])
    have memory := agrees.external (by simp [Component.Covers])
    refine ⟨3+fuel,t,runA.trans runT,readyT,?_,effect.rip,?_,agrees⟩
    · intro a b fetch; rw [memory]; exact pre.loaded a b fetch
    · have value : t.regValue .rdx=a.regValue .rax >>> shiftCount 64 ((a.regValue .rbx).setWidth 8) :=
        effect.writes.2.2
      rw [value,first,index,index_shift_count]
      simpa only [within,↓reduceIte] using window_at_index pre.bound (i:=i)
  · obtain ⟨fuel,t,runT,readyT,_,effect⟩ := cross_block boundary outer a readyA
      (programText_slice (programLoaded_codeIn loadedA) 0xf420 crossBytes
        (by decide) (by decide +kernel)) (by simpa only [within,↓reduceIte] using ripA)
    have agrees : AgreesExcept [.reg 0,.reg 1,.reg 2,.flags,.rip] s t :=
      (agreesA.trans effect.agrees).mono (by simp [crossEffect,Effect.components])
    have memory := agrees.external (by simp [Component.Covers])
    refine ⟨3+fuel,t,runA.trans runT,readyT,?_,effect.rip,?_,agrees⟩
    · intro a b fetch; rw [memory]; exact pre.loaded a b fetch
    · have value : t.regValue .rdx=
          (a.regValue .rdx <<< shiftCount 64 ((a.regValue .rbp).setWidth 8)) |||
          (a.regValue .rax >>> shiftCount 64 ((a.regValue .rbx).setWidth 8)) := effect.writes.2.2
      rw [value,first,second,index,negative,index_shift_count,negative_shift_count (by omega),BitVec.or_comm]
      simpa only [within,↓reduceIte] using window_at_index pre.bound (i:=i)

end P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine
