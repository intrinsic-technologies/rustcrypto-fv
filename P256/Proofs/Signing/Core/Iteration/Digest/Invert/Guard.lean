import P256.Proofs.Program.Code
import P256.Proofs.Signing.Core.Iteration.Digest.Prefix
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Memory.LoadByte
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Invert

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

theorem inverse_guard [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t)
    (rip : t.RIP = 0x10cd04) (flag : t.external[frameBase s + 560]? = some 1) :
    ∃ u, Advances boundary 4 t u ∧ Frame s u ∧ u.RIP = 0x10cd1b ∧
      AgreesExcept [.reg 0, .mem (frameBase s + 1328) 1, .flags, .rip] t u := by
  have outside (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset bound)
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (movzx_r32_m8_effect_step 0x10cd04 0 (.sib 4 none 0 (.d32 560))
      (by decide +kernel) rfl rfl).advances (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xcd04 _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable t (stackPtr t + 560) 1
        exact stack_readable (frameOffset := 2280) pre.toCalleePre (NextNonce.scalarFrame frame) (by decide) (by decide)⟩
      (outside 0xcd0c (by decide))
  have agreesA : AgreesExcept [.reg 0, .rip] t a := effectA.agrees
  have frameA := after_registers frame readyA agreesA
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  have oneA : (a.regValue .rax).setWidth 8 = 1 := by
    have value := effectA.writes
    change a.regValue .rax = (memLoad t.external (stackPtr t + 560) 8).setWidth 64 at value
    rw [frame.rsp] at value
    change a.regValue .rax = (memLoad t.external (frameBase s+560) 8).setWidth 64 at value
    rw [P256.Proofs.Common.Memory.memLoad8_of_byte flag] at value
    rw [value]
    rfl
  let am := AddrMode.sib 4 none 0 (.d32 1328)
  have addr : storeAddrAt 0x10cd0c am 7 a = frameBase s + 1328#64 := by
    change stackPtr a + 1328#64 = _
    rw [frameA.rsp]
  have write : MemWritable a (frameBase s + 1328#64) 1 :=
    Prefix.Block.writable_narrow (local_writable8 pre frameA (offset := 1328) (by decide) (by decide)) (by decide)
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10cd0c 0 (by decide) am (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0xcd0c _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, addr ▸ write, by
        change RangeApart (storeAddrAt 0x10cd0c am 7 a) 1 0x10cd0c 7
        rw [addr]
        exact local_code_apart pre frameA (offset := 1328) (len := 1)
          (codeOffset := 0xcd0c) (codeLen := 7) (by decide) (by decide)⟩
      (outside 0xcd13 (by decide))
  change (storeEffect 0x10cd0c 7 (storeAddrAt 0x10cd0c am 7)
    (fun state => (Operand.reg 0 : Operand 8).read state) a).Holds a b at effectB
  have agreesB : AgreesExcept [.mem (frameBase s + 1328#64) 1, .rip] a b := by
    simpa only [storeEffect_components, addr, Nat.reduceDiv] using effectB.agrees
  have writesB : WordWrites (frameBase s) [1328] [.mem (frameBase s + 1328#64) 1,.rip] := by
    intro c hc address cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl
    · obtain ⟨i,hi,rfl⟩ := cover
      exact ⟨1328,by simp,i,by omega,rfl⟩
    · exact cover.elim
  have frameB := after_effect pre frameA readyB agreesB writesB
    (by intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; subst off; decide) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨c, runC, readyC, effectC⟩ := (cmp_al_imm8_effect_step 0x10cd13 1).advances readyB
    (programText_slice (programLoaded_codeIn frameB.loaded) 0xcd13 [0x3c,1]
      (by decide) (by decide +kernel)) effectB.rip (outside 0xcd15 (by decide))
  have agreesC : AgreesExcept [.flags,.rip] b c := effectC.agrees
  have frameC := after_registers frameB readyC agreesC
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  have oneB : (b.regValue .rax).setWidth 8 = 1 :=
    (agreesB.read (n := 8) (r := 0) (by simp)).trans oneA
  have zeroFlag : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = true := by
    have h := effectC.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = (cmpSpec ((b.regValue .rax).setWidth 8) 1).ZF at h
    rw [h, oneB]
    decide +kernel
  have cond : condHolds 5 (StatusFlags.ofRFLAGS c.RFLAGS) = false := by
    change (!(StatusFlags.ofRFLAGS c.RFLAGS).ZF) = false
    rw [zeroFlag]
    rfl
  have next : (jccEffect 0x10cd15 6 5 ((0x7e9 : BitVec 32).signExtend 64) c).rip = 0x10cd1b := by
    simp only [jccEffect, cond, branchEffect, Bool.false_eq_true, ↓reduceIte, BitVec.reduceAdd]
    rfl
  obtain ⟨u, runU, readyU, effectU⟩ := (jcc_rel32_effect_step 0x10cd15 5 0x7e9).advances readyC
    (programText_slice (programLoaded_codeIn frameC.loaded) 0xcd15 _
      (by decide) (by decide +kernel))
    ⟨effectC.rip, by rw [cond]; exact Bool.noConfusion⟩
    (by rw [next]; exact outside 0xcd1b (by decide))
  have agreesU : AgreesExcept [.rip] c u := effectU.agrees
  have frameU := after_registers frameC readyU agreesU
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  refine ⟨u, ((runA.trans runB).trans runC).trans runU, frameU, effectU.rip.trans next, ?_⟩
  exact (((agreesA.trans agreesB).trans agreesC).trans agreesU).mono (by simp)

end P256.Proofs.Signing.Core.Iteration.Digest.Invert
