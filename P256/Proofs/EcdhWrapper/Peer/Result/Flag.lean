import P256.Proofs.EcdhWrapper.Peer.Result.Memory
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Common.Memory.LoadByte
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Der.Decode.Header.Control

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Result

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions P256.Proofs.Common.Memory
open P256.Proofs.Common.Der.Decode.Header

theorem flag [Bindings] {initial s : RamState} {secret peer : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP=0x106b85) (rsp : stackPtr s=stackPtr initial-504)
    (valid : s.external[stackPtr initial-56]?=some 1) :
    ∃ t, Advances (returnBoundary initial) 5 s t ∧ ReadyToStep t ∧ t.RIP=0x106baa ∧
      AgreesExcept [.reg 0,.flags,.rip,.mem (stackPtr initial-336) 1] s t := by
  have stack : Stack.Valid initial 4104 := call.stackAvailable.1
  have src : stackPtr s+448=stackPtr initial-56 := by
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have dst : stackPtr s+168=stackPtr initial-336 := by
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have read : MemReadable s (stackPtr s+448) 1 := by
    rw [src]
    exact readable_of_grow (stack_sub_readable stack (offset := 56) (by decide) (by decide)) grow
  obtain ⟨a,ra,readyA,ea⟩ := (movzx_r32_m8_effect_step 0x106b85 0
    (.sib 4 none 0 (.d32 448)) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6b85 _ (by decide) (by decide +kernel))
    ⟨rip,read⟩ (boundary_ne_program outside (inProgram_of_textOffset 0x6b8d (by decide)))
  have ga : AgreesExcept [.reg 0,.rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have sa : stackPtr a=stackPtr s := ga.read (n := 64) (r := 4) (by simp)
  have ax : a.regValue .rax=1 := by
    have h : a.regValue .rax=(memLoad s.external (stackPtr s+448) 8).setWidth 64 := ea.writes
    rw [h,src,memLoad8_of_byte valid]; rfl
  have writable : MemWritable a (stackPtr a+168) 1 := by
    rw [sa,dst]
    exact writable_of_grow (stack_sub_writable stack
      (fun b hb hpage ↦ call_stack_avoids call b hb (.inr hpage))
      (offset := 336) (len := 1) (by decide) (by decide) (by decide)
      (by have := Nat.mod_lt (stackPtr initial-336).toNat (by decide : 0<4096); omega))
      (fun b hb ↦ ga.grow b (grow b hb))
  have apart : RangeApart (stackPtr a+168) 1 0x106b8d 7 := by
    rw [sa,dst]
    exact stack_buffer_code_apart stack (call_stack_avoids (routine := ecdhDiffieHellman) call)
      (offset := 336) (len := 1) (by decide) (by decide)
      (codeOffset := 0x6b8d) (codeLength := 7) (by decide)
  obtain ⟨b,rb,readyB,eb⟩ := (mov_m8_r8_legacy_effect_step 0x106b8d 0 (by decide)
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl).advances readyA
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0x6b8d _
      (by decide) (by decide +kernel)) ⟨ea.rip,writable,apart⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b94 (by decide)))
  have gb : AgreesExcept [.mem (stackPtr initial-336) 1,.rip] a b := by
    simpa only [storeEffect_components,Nat.reduceDiv,show 2+(AddrMode.sib 4 none 0 (.d32 168)).tail.length=7 from rfl,show storeAddrAt 0x106b8d (.sib 4 none 0 (.d32 168)) 7 a=stackPtr a+168 from rfl,sa,dst] using eb.agrees
  have totalB := ga.trans gb
  have gbig : AgreesExcept (components initial) s b := totalB.mono (by simp [components])
  have lb := loaded_after call gbig loaded
  have sb : stackPtr b=stackPtr s := totalB.read (n := 64) (r := 4) (by simp)
  have byte : memLoad b.external (stackPtr initial-336) 8=1 := by
    have h : memLoad b.external (stackPtr a+168) 8=(a.regValue .rax).setWidth 8 := eb.writes
    rw [sa,dst,ax] at h
    exact h
  obtain ⟨c,rc,readyC,ec⟩ := (lea_r64_effect_step 0x106b94 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl).advances readyB
    (programText_slice (programLoaded_codeIn lb) 0x6b94 _ (by decide) (by decide +kernel)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b9c (by decide)))
  have gc : AgreesExcept [.reg 0,.rip] b c := ec.agrees
  have mc := gc.external (by simp [Component.Covers])
  have sc : stackPtr c=stackPtr s := (gc.read (n := 64) (r := 4) (by simp)).trans sb
  have readC : MemReadable c (stackPtr c+168) 1 := by
    rw [sc,dst]
    exact readable_of_grow (stack_sub_readable stack (offset := 336) (by decide) (by decide))
      (fun z hz ↦ gc.grow z (totalB.grow z (grow z hz)))
  obtain ⟨d,rd,readyD,ed⟩ := (cmp_m8_imm8_effect_step 0x106b9c
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl 0).advances readyC
    (programText_slice ((programLoaded_codeIn lb).of_external_eq mc) 0x6b9c _
      (by decide) (by decide +kernel)) ⟨ec.rip,readC⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ba4 (by decide)))
  have gd : AgreesExcept [.flags,.rip] c d := ed.agrees
  have md := gd.external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS d.RFLAGS).ZF=false := by
    have h := ed.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS d.RFLAGS).ZF=(cmpSpec (memLoad c.external (stackPtr c+168) 8) 0).ZF at h
    rw [h,sc,dst,mc,byte]; rfl
  obtain ⟨t,rt,readyT,et⟩ := (jcc_rel32_not_taken_effect_step 0x106ba4 4 0x144).advances readyD
    (programText_slice (((programLoaded_codeIn lb).of_external_eq mc).of_external_eq md)
      0x6ba4 _ (by decide) (by decide +kernel)) ⟨ed.rip,zf⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6baa (by decide)))
  exact ⟨t,(((ra.trans rb).trans rc).trans rd).trans rt,readyT,et.rip,
    (((totalB.trans gc).trans gd).trans et.agrees).mono (by simp)⟩

end P256.Proofs.EcdhWrapper.Peer.Result
