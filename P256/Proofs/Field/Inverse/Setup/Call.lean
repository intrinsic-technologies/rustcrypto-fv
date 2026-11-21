import P256.Proofs.Field.Inverse.Setup.Call.Memory

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem inverse_safeGcd_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ n u, Advances boundary n s u ∧ SafeGcdPre u boundary ∧
      stackPtr u = stackPtr s - 176 ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .rsi = s.regValue .rsi ∧
      u.regValue .rdi = stackPtr s - 168 ∧
      (returnBoundary u).rip = 0x11411e ∧
      AgreesExcept (callComponents s) s u ∧ SavedWords s u := by
  obtain ⟨n,t,run,ready,loaded,rip,rsp,rbx,rsi,rdi,rdx,r8,rcx,agrees,modulus,adjuster,saved⟩ :=
    inverse_parameters pre
  obtain ⟨u,step,readyU,loadedU,effect,_⟩ := call_rel32_exists pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary ready loaded agrees.grow
    168 0x14119 0xffffda52 rsp rip (by decide) (by decide) (by decide)
    (by decide +kernel) (by exact inProgram_of_textOffset 0x11b70 (by decide))
  change (callEffect (fun _ => 0x111b70) 0x11411e t).Holds t u at effect
  have push : pushAddr t = stackPtr s - 176 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  have sp : stackPtr u = stackPtr s - 176 := effect.writes.1.trans push
  have bx : u.regValue .rbx = s.regValue .rdi :=
    (effect.agrees.read (n := 64) (r := 3) (by simp)).trans rbx
  have si : u.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans rsi
  have di : u.regValue .rdi = stackPtr s - 168 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans rdi
  have dx : u.regValue .rdx = stackPtr s - 128 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans rdx
  have eight : u.regValue .r8 = stackPtr s - 96 :=
    (effect.agrees.read (n := 64) (r := 8) (by simp)).trans r8
  have agCall : AgreesExcept [.reg 4, .mem (stackPtr s - 176) 8, .rip] t u := by
    simpa only [pushEffect_components, push] using effect.agrees
  have total : AgreesExcept (callComponents s) s u := agrees.trans agCall
  have ret : (returnBoundary u).rip = 0x11411e := (callEffect_stack effect).1
  let layout : StackBufferLayout 880 40 704 := ⟨176,168,by decide,by decide,by decide,by decide⟩
  have child := CalleePre.of_input_and_stack pre layout
    (bindingsSupported_of_ready_agrees pre.bindingsSupported readyU total)
    (supportedMachine_of_ready_agrees pre.machine readyU total)
    (total.directionFlagClear (by simp [callComponents, setupComponents, entryComponents,
      pushSequenceFrame]) pre.directionFlag)
    loadedU total.grow effect.rip sp si di
    (by rw [ret]; exact inProgram_of_textOffset 0x1411e (by decide))
  refine ⟨n+1,u,run.trans step,?_,sp,bx,si,di,ret,total,saved_words_call pre rsp saved effect⟩
  refine ⟨child, safeGcd_parameter_pre pre total.grow sp di (by decide) dx,
    safeGcd_parameter_pre pre total.grow sp di (by decide) eight, ?_, ?_, ?_⟩
  · rw [dx]
    exact safeGcd_call_value pre rsp effect (by decide) (by decide) modulus
  · rw [eight]
    exact safeGcd_call_value pre rsp effect (by decide) (by decide) adjuster
  · exact (effect.agrees.read (n := 64) (r := 1) (by simp)).trans rcx

theorem safeGcd_call_input [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Pre s boundary) (agrees : AgreesExcept (callComponents s) s t)
    (input : Nat256At s (s.regValue .rsi) x) :
    Nat256At t (s.regValue .rsi) x := by
  have frame := safeGcd_call_frame pre agrees
  refine ⟨input.1, fun i hi => ?_⟩
  rw [frame]
  · exact input.2 i hi
  · intro region hr ha
    have eq : region = Stack.region s 880 := by simpa using hr
    subst region
    apply pre.separation 0 2 (by decide) _ ?_ ha
    change (registerRegion s .rsi 32).Contains _
    exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi

end P256.Proofs.Field.Inverse
