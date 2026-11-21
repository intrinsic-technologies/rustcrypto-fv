import P256.Proofs.Generate.Sampler.Arguments
import P256.Proofs.Generate.Sampler.Entry
import P256.Proofs.Generate.Sampler.Call
import P256.Proofs.Generate.Sampler.Input
import P256.Proofs.Generate.Scalar.Correct

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem decode_call [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : Nat} (pre : Pre s boundary input)
    (state : LoopReady s t input offset 0x100ccf 32)
    (remaining : t.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)))
    (bytes : (MemoryRegion.mk (stackPtr s-224#64).toNat 32).HasBytes
      t.external (input.extract offset (offset+32))) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      LoopReady s u input offset 0x100cda 32 ∧
      u.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)) ∧
      Nat256At u (stackPtr s-184#64) (Arith.uint (input.extract offset (offset+32))) ∧
      u.external[stackPtr s-152#64]? =
        some (if Arith.uint (input.extract offset (offset+32)) < Operations.domain.n then 1 else 0) := by
  obtain ⟨na,a,ha,ra,_,ea⟩ := arguments_run boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (arguments_loaded state.loaded) state.rip
  have sa := state.toState.after_registers pre ra ea.agrees
    (by simp [argumentEffect,Effect.components,Component.Covers])
    (by simp [argumentEffect,Effect.components])
  obtain ⟨b,hb,sb,eb⟩ := call_push pre sa 0xcd5 0x121f6 (by decide)
    (by decide +kernel) (inProgram_of_textOffset 0x12ed0 (by decide)) ea.rip
  have dib : b.regValue .rdi = stackPtr s-184#64 :=
    (eb.agrees.read (n := 64) (r := 7) (by simp)).trans (ea.writes.1.trans state.decoded)
  have sib : b.regValue .rsi = stackPtr s-224#64 :=
    (eb.agrees.read (n := 64) (r := 6) (by simp)).trans (ea.writes.2.trans state.buffer)
  let layout : StackCallLayout 3624 32 33 72 :=
    ⟨272,224,184,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have cp : CalleePre b boundary 0x112ed0 32 33 72 :=
    CalleePre.of_stack_region pre.stack (pre.avoids _ (by simp)) pre.outerBoundary layout
      sb.bindingsSupported sb.machine sb.directionFlag sb.loaded sb.allocated eb.rip sb.rsp sib dib
      (by change InProgram (stackTop b); rw [(callEffect_stack eb).1]
          exact inProgram_of_textOffset 0xcda (by decide))
  have bb : (registerRegion b .rsi 32).HasBytes b.external (input.extract offset (offset+32)) := by
    change (MemoryRegion.mk (b.regValue .rsi).toNat 32).HasBytes _ _
    rw [sib]
    refine ⟨bytes.1,?_⟩
    intro i
    have bound : i.val < 32 := by
      have size : (input.extract offset (offset+32)).size = 32 := bytes.1
      have := i.isLt
      omega
    have keep := ScalarFrame.call_byte (frameOffset := 264) (by decide) sa.rsp eb
      (offset := 224) (len := 32) (by decide) (by decide) bound
    have ext : a.external = t.external := ea.agrees.external
      (by simp [argumentEffect,Effect.components,Component.Covers])
    have h := bytes.2 i
    simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at h ⊢
    rw [keep,ext]
    exact h
  obtain ⟨u,result,value,tag,_⟩ := Scalar.from_repr_correct cp bb
  have su := return_state pre sb result dib (by decide) (by decide) (by decide)
  have regs (r : Syntax.Reg) (hr : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      u.regValue r = t.regValue r := by
    refine (result.calleeSaved r hr).trans ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (eb.agrees.read (n := 64) (r := 3) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 3) (by simp [argumentEffect,Effect.components]))
    · exact (eb.agrees.read (n := 64) (r := 5) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 5) (by simp [argumentEffect,Effect.components]))
    · exact (eb.agrees.read (n := 64) (r := 12) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 12) (by simp [argumentEffect,Effect.components]))
    · exact (eb.agrees.read (n := 64) (r := 13) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 13) (by simp [argumentEffect,Effect.components]))
    · exact (eb.agrees.read (n := 64) (r := 14) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 14) (by simp [argumentEffect,Effect.components]))
    · exact (eb.agrees.read (n := 64) (r := 15) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 15) (by simp [argumentEffect,Effect.components]))
  have keep (i : Nat) (hi : i < 8) :
      u.external[stackPtr s-192#64+BitVec.ofNat 64 i]? =
        b.external[stackPtr s-192#64+BitVec.ofNat 64 i]? := by
    apply result.frame
    intro r hr hit
    have bound := stack_bounds pre.stack
    have stk : (stackPtr s-272).toNat = (stackPtr s).toNat-272 :=
      stack_sub_toNat pre.stack (by decide)
    have out : (stackPtr s-184#64).toNat = (stackPtr s).toNat-184 :=
      stack_sub_toNat pre.stack (by decide)
    have addr : (stackPtr s-192#64+BitVec.ofNat 64 i).toNat = (stackPtr s).toNat-192+i := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i < 2^64),
        Nat.mod_eq_of_lt (by rw [stack_sub_toNat pre.stack (by decide)]; omega),
        stack_sub_toNat pre.stack (by decide)]
    have cases : r = registerRegion b .rdi 33 ∨ r = Stack.region b 72 := by simpa using hr
    rcases cases with rfl | rfl
    · change (b.regValue .rdi).toNat ≤ _ ∧ _ < (b.regValue .rdi).toNat+33 at hit
      rw [dib,out,addr] at hit
      omega
    · change (stackPtr b).toNat-72 ≤ _ ∧ _ < (Stack.region b 72).start+(Stack.region b 72).size at hit
      rw [stack_region_end,sb.rsp,stk,addr] at hit
      omega
  have pointer : memLoad u.external (stackPtr s-192#64) 64 = s.regValue .rdi := by
    apply Eq.trans ?_ state.output
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    rw [keep i hi,ScalarFrame.call_byte (frameOffset := 264) (by decide) sa.rsp eb
      (offset := 192) (len := 8) (by decide) (by decide) hi]
    rw [ea.agrees.external (by simp [argumentEffect,Effect.components,Component.Covers])]
    rfl
  obtain ⟨nc,hc⟩ := result.execution
  refine ⟨u,⟨na+1+nc,(ha.trans hb).trans hc⟩,
    {toState := su,rip := result.rip.trans (callEffect_stack eb).1,
      descriptor := (regs .r14 (by simp)).trans state.descriptor,
      source := (regs .rbp (by simp)).trans state.source,
      remaining := (regs .r13 (by simp)).trans state.remaining,
      decoded := (regs .r15 (by simp)).trans state.decoded,
      buffer := (regs .r12 (by simp)).trans state.buffer,output := pointer},
    (regs .rbx (by simp)).trans remaining,?_,?_⟩
  · simpa only [dib] using value
  · rw [dib] at tag
    have addr : stackPtr s-184#64+32 = stackPtr s-152#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [addr] at tag
    exact tag

end P256.Proofs.Generate.Sampler
