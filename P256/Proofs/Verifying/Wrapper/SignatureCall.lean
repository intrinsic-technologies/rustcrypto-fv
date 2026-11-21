import P256.Proofs.Verifying.Wrapper.SignatureRead
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def signatureLayout : StackBufferLayout 10280 72 896 :=
  ⟨288,208,by decide,by decide,by decide,by decide⟩

def signatureCallComponents (initial : RamState) : List Component :=
  [.reg 7,.reg 2,.reg 4,.mem (stackPtr initial-288) 8,.rip]

theorem enter_signature_decoder [Bindings] {initial s : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s)
    (frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial))
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x103133)
    (source : s.regValue .rsi = memLoad initial.external (initial.regValue .rdi+8#64) 64)
    (length : s.regValue .rax = 64) :
    ∃ t, CalleePre t (returnBoundary initial) 0x109ac0 64 72 896 ∧
      t.regValue .rdx = 64 ∧ (registerRegion t .rsi 64).HasBytes t.external signature ∧
      t.regValue .rdi = stackPtr initial-208 ∧ stackPtr t = stackPtr initial-288 ∧
      (returnBoundary t).rip = 0x103140 ∧
      AgreesExcept (signatureCallComponents initial) s t ∧
      ∃ fuel, Advances (returnBoundary initial) fuel s t := by
  obtain ⟨n,u,run,ready,_,effect⟩ := signature_arguments (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3133 signatureArgumentBytes
      (by decide) (by decide +kernel)) rip
  have ag : AgreesExcept [.reg 7,.reg 2,.rip] s u := by
    simpa only [signatureArgumentEffect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append] using effect.agrees
  have su := state.after_registers ready ag (by simp [Component.Covers]) (by simp) (by simp)
  have values : u.regValue .rdi = stackPtr s+72 ∧ u.regValue .rdx = s.regValue .rax := effect.writes
  have output : u.regValue .rdi = stackPtr initial-208 := by
    rw [values.1,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨t,runT,readyT,loadedT,ce,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside ready su.loaded su.allocated 280 0x313b 0x6980 su.rsp
    effect.rip (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x9ac0 (by decide))
  have push : pushAddr u = stackPtr initial-288 := by
    rw [pushAddr,su.rsp,BitVec.sub_sub]
    rfl
  have ca : AgreesExcept [.reg 4,.mem (stackPtr initial-288) 8,.rip] u t := by
    simpa only [pushEffect_components,push] using ce.agrees
  have inputT : t.regValue .rsi = memLoad initial.external (initial.regValue .rdi+8#64) 64 :=
    ((ag.trans ca).read (n := 64) (r := 6) (by simp)).trans source
  have outputT : t.regValue .rdi = stackPtr initial-208 :=
    (ca.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary t).rip = 0x103140 := (callEffect_stack ce).1
  have sp : stackPtr t = stackPtr initial-288 := ce.writes.1.trans push
  have ripT : t.RIP = 0x109ac0 := ce.rip
  have pushFrame : MemoryWriteFrame u t (wrapperRegions verifyingKeyVerify initial) := by
    apply ca.memoryWriteFrame
    intro c hc a covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨callStack verifyingKeyVerify initial,by simp [wrapperRegions],
      stack_component_within call.stackAvailable.1 (by decide) (by decide) covered⟩
  have fullFrame : MemoryWriteFrame initial t (wrapperRegions verifyingKeyVerify initial) := by
    apply memoryWriteFrame_trans (t := u) _ pushFrame
    intro address away
    rw [ag.external (by simp [Component.Covers])]
    exact frame address away
  obtain ⟨address,original,_,bounded,bytes,_⟩ := preserved_signature_input call fullFrame
  obtain ⟨point,r,scalarS,_,_,_,size,_⟩ := verifying_arguments_decoded call.argumentsValid
  have eq : registerRegion t .rsi 64 = MemoryRegion.mk address.toNat signature.size := by
    simp only [registerRegion,inputT,original,size]
  have ib : (registerRegion t .rsi 64).Bounded := eq ▸ bounded
  have hb : (registerRegion t .rsi 64).HasBytes t.external signature := eq ▸ bytes
  have separate : (registerRegion t .rsi 64).Disjoint (Stack.region initial 10280) := by
    rw [eq,← original]
    intro a ha hs
    exact wrapper_read_disjoint call (signature_input_region call)
      (callStack verifyingKeyVerify initial) (by simp [wrapperRegions]) a ha
      (stack_contains_callStack hs)
  have stack : Stack.Valid initial 10280 := call.stackAvailable.1
  have avoids := call_stack_avoids call
  change (Stack.region initial 10280).Avoids (fun a => InProgram a ∨ InPageTables a) at avoids
  have child : CalleePre t (returnBoundary initial) 0x109ac0 64 72 896 :=
    CalleePre.of_disjoint_input_and_stack signatureLayout stack
    avoids (bindingsSupported_of_ready_agrees su.bindingsSupported readyT ca)
    (supportedMachine_of_ready_agrees su.machine readyT ca)
    (ca.directionFlagClear (by simp) su.directionFlag) loadedT ripT sp ib
    (hasBytes_allocated hb) separate outputT
    (fun a ha => ca.grow a (su.allocated a ha)) outside
    (by rw [ret]; exact inProgram_of_textOffset 0x3140 (by decide))
  refine ⟨t,child,(ca.read (n := 64) (r := 2) (by simp)).trans (values.2.trans length),
    hb,outputT,sp,ret,?_,⟨n+1,run.trans runT⟩⟩
  apply (ag.trans ca).mono
  intro c hc
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with (rfl | rfl | rfl) | rfl | rfl | rfl <;> simp [signatureCallComponents]

end P256.Proofs.Verifying.Wrapper
