import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.Code
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program.Routines Program ScalarFrame
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

theorem accept_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (frame : Frame s t) (second : Bool)
    (rip : t.RIP = if second then 0x10db70 else 0x10dac3)
    (one : (t.regValue .rax).setWidth 8 = 1) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧
      u.RIP = (if second then 0x10db7f else 0x10dad2) ∧
      AgreesExcept [.mem (frameBase s+128) 1, .flags, .rip] t u := by
  let offset : Nat := if second then 0xdb70 else 0xdac3
  let pc := Extracted.textAddress + BitVec.ofNat 64 offset
  let disp : BitVec 32 := if second then 0x627 else 0x6d4
  let am := AddrMode.sib 4 none 0 (.d32 128)
  have rip0 : t.RIP = pc := by cases second <;> exact rip
  have outside (i : Nat) (hi : i ≤ 15) : pc + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply boundary_ne_program pre.outerBoundary
    have h := inProgram_of_textOffset (offset+i) (by cases second <;> dsimp [offset] <;> omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, pc] using h
  have addr : storeAddrAt pc am 7 t = frameBase s + 128#64 := by
    change stackPtr t + 128#64 = _
    rw [frame.rsp]
    rfl
  have write : MemWritable t (frameBase s+128#64) 1 := by
    have eq : frameBase s+128#64 = stackPtr s - 1048#64 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [eq]
    exact writable_of_grow (stack_sub_writable pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
      (offset := 1048) (len := 1) (by decide) (by decide) (by decide)
      (by have := Nat.mod_lt (stackPtr s-1048#64).toNat (by decide : 0<4096); omega))
      frame.allocated
  have code : CodeIn (codeRange pc (0x88 :: am.modrm 0 :: am.tail)) t :=
    programText_slice (programLoaded_codeIn frame.loaded) offset _
      (by cases second <;> decide) (by cases second <;> decide +kernel)
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_m8_r8_legacy_effect_step pc 0 (by decide) am (by decide +kernel) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported) code
      ⟨rip0, addr ▸ write, by
        change RangeApart (storeAddrAt pc am 7 t) 1 pc 7
        rw [addr]
        have h := stack_code pre.toCalleePre frame (offset := 128) (len := 1)
          (codeOffset := offset) (codeLen := 7) (by decide) (by decide)
          (by cases second <;> decide)
        simpa only [frame.rsp,frameBase,pc] using h⟩
      (outside 7 (by decide))
  change (storeEffect pc 7 (storeAddrAt pc am 7)
    (fun state => (Operand.reg 0 : Operand 8).read state) t).Holds t a at effectA
  have agreesA : AgreesExcept [.mem (frameBase s+128#64) 1, .rip] t a := by
    simpa only [storeEffect_components, addr, Nat.reduceDiv] using effectA.agrees
  have localA : WritesWithin [.mem (frameBase s+128#64) 1, .rip]
      #v[registerRegion s .rdi 24,workRegion s 9992] := by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · have addr : frameBase s+128#64 = stackPtr s-1048#64 := by
        simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      rw [addr] at cover
      exact ⟨workRegion s 9992,by simp,
        work_contains pre.toCalleePre (by decide) (by decide) cover⟩
    · exact cover.elim
  have frameA := frame.after_effect pre.toCalleePre (by decide) readyA agreesA localA (by simp)
  obtain ⟨b, runB, readyB, effectB⟩ := (cmp_al_imm8_effect_step (pc+7#64) 1).advances (boundary := boundary) readyA
    (by
      have h := programText_slice (programLoaded_codeIn frameA.loaded) (offset+7) [0x3c,1]
        (by cases second <;> decide) (by cases second <;> decide +kernel)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, pc] using h)
    effectA.rip (by simpa only [cmpAlImm8Effect, BitVec.add_assoc, BitVec.reduceAdd] using outside 9 (by decide))
  have agreesB : AgreesExcept [.flags,.rip] a b := effectB.agrees
  have frameB := frameA.after_registers readyB agreesB (by simp [Component.Covers]) (by simp)
  have oneA : (a.regValue .rax).setWidth 8 = 1 :=
    (agreesA.read (n := 8) (r := 0) (by simp)).trans one
  have zeroFlag : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = true := by
    have h := effectB.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = (cmpSpec ((a.regValue .rax).setWidth 8) 1).ZF at h
    rw [h, oneA]
    decide +kernel
  have cond : condHolds 5 (StatusFlags.ofRFLAGS b.RFLAGS) = false := by
    change (!(StatusFlags.ofRFLAGS b.RFLAGS).ZF) = false
    rw [zeroFlag]
    rfl
  have next : (jccEffect (pc+9#64) 6 5 (disp.signExtend 64) b).rip = pc+15#64 := by
    simp only [jccEffect, cond, branchEffect, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
  obtain ⟨u,runU,readyU,effectU⟩ := (jcc_rel32_effect_step (pc+9#64) 5 disp).advances readyB
    (by
      have h := programText_slice (programLoaded_codeIn frameB.loaded) (offset+9)
        (0x0f :: jccOpcode32 5 :: immBytes 32 disp)
        (by cases second <;> decide) (by cases second <;> decide +kernel)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, pc] using h)
    ⟨by simpa only [cmpAlImm8Effect, BitVec.add_assoc, BitVec.reduceAdd] using effectB.rip,
      by rw [cond]; exact Bool.noConfusion⟩
    (by rw [next]; exact outside 15 (by decide))
  have agreesU : AgreesExcept [.rip] b u := effectU.agrees
  have frameU := frameB.after_registers readyU agreesU (by simp [Component.Covers]) (by simp)
  refine ⟨u, (runA.trans runB).trans runU, frameU, ?_, ?_⟩
  · have h := effectU.rip.trans next
    cases second <;> exact h
  · exact ((agreesA.trans agreesB).trans agreesU).mono (by simp)

end P256.Proofs.Verifying.Core.Prepare
