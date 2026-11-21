import P256.Proofs.Generate.Sampler.Call
import P256.Proofs.PublicPoint.Correct
import P256.Proofs.Generate.Sampler.Finish.Arguments

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem public_point [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {d : Nat}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100d45)
    (scalar : Nat256At t (stackPtr t + 8) d)
    (copied : Nat256At t (stackPtr t + 40) d)
    (pointer : memLoad t.external (stackPtr t + 72) 64 = s.regValue .rdi) :
    ∃ n u, Advances boundary n t u ∧ State s u ∧ u.RIP = 0x100d54 ∧
      Nat256At u (stackPtr u + 8) d ∧
      Sec1.AffineAt u (stackPtr u + 112) (Points.mul d Operations.domain.G) ∧
      memLoad u.external (stackPtr u + 72) 64 = s.regValue .rdi := by
  obtain ⟨a,ha,sa,ipa,di,si,ma,spa⟩ := prepare_call pre state rip
  have xa : Nat256At a (stackPtr a + 40) d := by simpa only [Nat256At,ma,spa] using copied
  have original : Nat256At a (stackPtr a + 8) d := by simpa only [Nat256At,ma,spa] using scalar
  have pa : memLoad a.external (stackPtr a + 72) 64 = s.regValue .rdi := by
    simpa only [ma,spa] using pointer
  obtain ⟨b,hb,sb,eb⟩ := call_push pre sa 0xd4f 0xd99c (by decide)
    (by decide +kernel) (inProgram_of_textOffset 0xe6f0 (by decide)) ipa
  have dib : b.regValue .rdi = stackPtr s - 152 := by
    have h : b.regValue .rdi = a.regValue .rdi := eb.agrees.read (n := 64) (r := 7) (by simp)
    rw [h,di]
    exact scalar_stack_address (frameOffset := 264) sa.rsp (by decide) (by decide)
  have sib : b.regValue .rsi = stackPtr s - 224 := by
    have h : b.regValue .rsi = a.regValue .rsi := eb.agrees.read (n := 64) (r := 6) (by simp)
    rw [h,si]
    exact scalar_stack_address (frameOffset := 264) sa.rsp (by decide) (by decide)
  let layout : StackCallLayout 3624 32 65 3352 :=
    ⟨272,224,152,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have cp : CalleePre b boundary 0x10e6f0 32 65 3352 :=
    CalleePre.of_stack_region pre.stack (pre.avoids _ (by simp)) pre.outerBoundary layout
      sb.bindingsSupported sb.machine sb.directionFlag sb.loaded sb.allocated eb.rip sb.rsp sib dib
      (by change InProgram (stackTop b); rw [(callEffect_stack eb).1]
          exact inProgram_of_textOffset 0xd54 (by decide))
  have callKeep (off len : Nat) (ho : off ≤ 264) (hl : len ≤ off+8) (i : Nat) (hi : i<len) :=
    ScalarFrame.call_byte (frameOffset := 264) (by decide) sa.rsp eb ho hl hi
  have xb : Nat256At b (b.regValue .rsi) d := by
    rw [sib]
    have addr : stackPtr a + 40 = stackPtr s - 224 :=
      scalar_stack_address (frameOffset := 264) sa.rsp (by decide) (by decide)
    rw [addr] at xa
    exact ⟨xa.1,fun i hi => (callKeep 224 32 (by decide) (by decide) i hi).trans (xa.2 i hi)⟩
  obtain ⟨u,result,point⟩ := PublicPoint.public_point_correct bindings b boundary d cp xb
  have su := return_state pre sb result dib (by decide) (by decide) (by decide)
  have keep (off len : Nat) (ho : off ≤ 264) (hl : len ≤ off+8)
      (disjoint : 152+len ≤ off ∨ off+65 ≤ 152) (i : Nat) (hi : i<len) :
      u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      b.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
    apply result.frame
    intro region hr hit
    have hb := stack_bounds pre.stack
    have spb : (stackPtr s - 272).toNat = (stackPtr s).toNat - 272 :=
      stack_sub_toNat pre.stack (offset := 272) (by decide)
    have outb : (stackPtr s - 152).toNat = (stackPtr s).toNat - 152 :=
      stack_sub_toNat pre.stack (offset := 152) (by decide)
    have addr : (stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat - off + i := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i < 2^64),
        Nat.mod_eq_of_lt (by rw [stack_sub_toNat pre.stack (by omega)]; omega),
        stack_sub_toNat pre.stack (by omega)]
    have cases : region = registerRegion b .rdi 65 ∨ region = Stack.region b 3352 := by simpa using hr
    rcases cases with rfl | rfl
    · change (b.regValue .rdi).toNat ≤ _ ∧ _ < (b.regValue .rdi).toNat + 65 at hit
      rw [dib,outb,addr] at hit
      rcases disjoint with h | h <;> omega
    · change (stackPtr b).toNat - 3352 ≤ _ ∧ _ < (Stack.region b 3352).start + (Stack.region b 3352).size at hit
      rw [stack_region_end,sb.rsp,spb,addr] at hit
      omega
  have sp : stackPtr u = stackPtr a := su.rsp.trans sa.rsp.symm
  obtain ⟨n,hn⟩ := result.execution
  refine ⟨2+1+n,u,(ha.trans hb).trans hn,su,result.rip.trans (callEffect_stack eb).1,?_,?_,?_⟩
  · rw [sp]
    have addr : stackPtr a + 8 = stackPtr s - 256 :=
      scalar_stack_address (frameOffset := 264) sa.rsp (by decide) (by decide)
    rw [addr]
    rw [addr] at original
    exact ⟨original.1,fun i hi => (keep 256 32 (by decide) (by decide) (.inl (by decide)) i hi).trans
      ((callKeep 256 32 (by decide) (by decide) i hi).trans (original.2 i hi))⟩
  · have addr : stackPtr u + 112 = stackPtr s - 152 :=
      scalar_stack_address (frameOffset := 264) su.rsp (by decide) (by decide)
    simpa only [dib,addr] using point
  · have addra : stackPtr a + 72 = stackPtr s - 192 :=
      scalar_stack_address (frameOffset := 264) sa.rsp (by decide) (by decide)
    rw [addra] at pa
    rw [sp,addra]
    refine Eq.trans ?_ pa
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact (keep 192 8 (by decide) (by decide) (.inl (by decide)) i hi).trans
      (callKeep 192 8 (by decide) (by decide) i hi)

end P256.Proofs.Generate.Sampler.Finish
