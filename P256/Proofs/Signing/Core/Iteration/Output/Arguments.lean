import P256.Proofs.Signing.Core.Iteration.Output.Calls
import P256.Proofs.Signing.Core.Iteration.Output.Blocks.ScalarArguments
import P256.Proofs.Signing.Core.Iteration.Output.Blocks.XArguments
import P256.Proofs.Signing.Core.Iteration.Output.Blocks.CompareArguments
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {r scalarS x y : Nat}

theorem scalar_arguments (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d3c4) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d3d7 ∧ u.regValue .rsi = frameBase s+176 ∧
      u.regValue .rdi = frameBase s+432 ∧ u.regValue .r14 = frameBase s+432 ∧ u.external = t.external := by
  obtain ⟨n,u,run,ready,_,effect⟩ := Blocks.ScalarArguments_correct boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd3c4 Blocks.ScalarArgumentsBytes
      (by decide) (by decide +kernel)) ⟨rip⟩
  have ag := effect.agrees
  have fu := after_registers frame ready ag (by simp [Blocks.ScalarArgumentsEffect,Effect.components,Component.Covers])
    (by simp [Blocks.ScalarArgumentsEffect,Effect.components]) (by simp [Blocks.ScalarArgumentsEffect,Effect.components])
    (by simp [Blocks.ScalarArgumentsEffect,Effect.components]) (by simp [Blocks.ScalarArgumentsEffect,Effect.components])
  have pu := payload.after_registers ag (by simp [Blocks.ScalarArgumentsEffect,Effect.components,Component.Covers])
    (by simp [Blocks.ScalarArgumentsEffect,Effect.components]) (by simp [Blocks.ScalarArgumentsEffect,Effect.components])
    (by simp [Blocks.ScalarArgumentsEffect,Effect.components])
  obtain ⟨r14,rsi,rdi⟩ := effect.writes
  exact ⟨n,u,run,fu,pu,effect.rip,rsi.trans (congrArg (·+176) frame.rsp),
    rdi.trans (congrArg (·+432) frame.rsp),r14.trans (congrArg (·+432) frame.rsp),
    ag.external (by simp [Blocks.ScalarArgumentsEffect,Effect.components,Component.Covers])⟩

theorem x_arguments (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d3dc) (value : Field.MontgomeryAt t (frameBase s+104) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d423 ∧ u.regValue .rsi = frameBase s+1328 ∧ u.regValue .rdi = frameBase s+528 ∧
      Field.MontgomeryAt u (frameBase s+1328) x ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue reg = t.regValue reg) ∧
      (∀ i < 32,u.external[frameBase s+136+BitVec.ofNat 64 i]? = t.external[frameBase s+136+BitVec.ofNat 64 i]?) := by
  have raw : Blocks.XArgumentsPre t := by
    refine ⟨rip,?_,?_,?_⟩
    · intro off ho; rw [frame.rsp]
      exact local_readable pre frame (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    · intro off ho; rw [frame.rsp]
      apply local_writable8 pre frame
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl|rfl <;> decide
    · intro off ho co cl hc; rw [frame.rsp]
      exact local_code_apart pre frame (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega) hc
  obtain ⟨n,u,run,ready,_,effect⟩ := Blocks.XArguments_correct boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd3dc Blocks.XArgumentsBytes
      (by decide) (by decide +kernel)) raw
  have writes : WordWrites (frameBase s) [1328, 1336, 1344, 1352] (Blocks.XArgumentsEffect t).components := by
    intro c hc a ha
    simp only [Blocks.XArgumentsEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
    all_goals obtain ⟨i,hi,eq⟩ := ha; rw [frame.rsp] at eq
    · exact ⟨1352,by simp,i,hi,eq⟩
    · exact ⟨1344,by simp,i,hi,eq⟩
    · exact ⟨1336,by simp,i,hi,eq⟩
    · exact ⟨1328,by simp,i,hi,eq⟩
  have bound : ∀ off ∈ ([1328, 1336, 1344, 1352] : List Nat),off+8 ≤ 2232 := by
    intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
  have fu := after_effect pre frame ready effect.agrees writes bound
    (by simp [Blocks.XArgumentsEffect,Effect.components]) (by simp [Blocks.XArgumentsEffect,Effect.components])
    (by simp [Blocks.XArgumentsEffect,Effect.components]) (by simp [Blocks.XArgumentsEffect,Effect.components])
  have pu := payload.after_stack pre effect.agrees writes bound
    (by simp [Blocks.XArgumentsEffect,Effect.components]) (by simp [Blocks.XArgumentsEffect,Effect.components])
    (by simp [Blocks.XArgumentsEffect,Effect.components])
  have regs : ∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue reg = t.regValue reg := by
    intro reg hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact effect.agrees.read (n:=64) (r:=3) (by simp [Blocks.XArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=5) (by simp [Blocks.XArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=12) (by simp [Blocks.XArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=13) (by simp [Blocks.XArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=14) (by simp [Blocks.XArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=15) (by simp [Blocks.XArgumentsEffect,Effect.components])
  have kept : ∀ i < 32,u.external[frameBase s+136+BitVec.ofNat 64 i]? = t.external[frameBase s+136+BitVec.ofNat 64 i]? := by
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using word_writes_byte writes effect.agrees
      (offset:=136+i) (by omega) (by intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; constructor <;> omega)
  obtain ⟨_,_,di,si,w3,w2,w1,w0⟩ := effect.writes
  have copied : Field.MontgomeryAt u (frameBase s+1328) x := by
    apply Field.montgomeryAt_of_memLoad_limbs value.1
    · exact (local_readable pre fu (offset:=1328) (len:=32) (by decide)).mem
    · intro j hj
      have hjv := value.memLoad_limb j hj
      rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
      all_goals simp only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] at hjv ⊢
      · change memLoad u.external (stackPtr t+1328) 64 = memLoad t.external (stackPtr t+104) 64 at w0
        rw [frame.rsp] at w0; exact w0.trans hjv
      · change memLoad u.external (stackPtr t+1336) 64 = memLoad t.external (stackPtr t+112) 64 at w1
        rw [frame.rsp] at w1; exact w1.trans hjv
      · change memLoad u.external (stackPtr t+1344) 64 = memLoad t.external (stackPtr t+120) 64 at w2
        rw [frame.rsp] at w2; exact w2.trans hjv
      · change memLoad u.external (stackPtr t+1352) 64 = memLoad t.external (stackPtr t+128) 64 at w3
        rw [frame.rsp] at w3; exact w3.trans hjv
  exact ⟨n,u,run,fu,pu,effect.rip,si.trans (congrArg (·+1328) frame.rsp),
    di.trans (congrArg (·+528) frame.rsp),copied,regs,kept⟩

theorem compare_arguments (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d428) (r14 : t.regValue .r14 = frameBase s+432) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d484 ∧ u.regValue .rsi = frameBase s+528 ∧ u.regValue .rdi = frameBase s+432 ∧
      u.regValue .rdx = 32 ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue reg = t.regValue reg) ∧
      (∀ i < 32,u.external[frameBase s+136+BitVec.ofNat 64 i]? = t.external[frameBase s+136+BitVec.ofNat 64 i]?) := by
  have raw : Blocks.CompareArgumentsPre t := by
    refine ⟨rip,?_,?_,?_⟩
    · intro off ho; rw [frame.rsp]
      exact local_readable pre frame (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    · intro off ho; rw [frame.rsp]
      apply local_writable8 pre frame
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl|rfl <;> decide
    · intro off ho co cl hc; rw [frame.rsp]
      exact local_code_apart pre frame (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega) hc
  obtain ⟨n,u,run,ready,_,effect⟩ := Blocks.CompareArguments_correct boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd428 Blocks.CompareArgumentsBytes
      (by decide) (by decide +kernel)) raw
  have writes : WordWrites (frameBase s) [528, 536, 544, 552] (Blocks.CompareArgumentsEffect t).components := by
    intro c hc a ha
    simp only [Blocks.CompareArgumentsEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
    all_goals obtain ⟨i,hi,eq⟩ := ha; rw [frame.rsp] at eq
    · exact ⟨528,by simp,i,hi,eq⟩
    · exact ⟨536,by simp,i,hi,eq⟩
    · exact ⟨544,by simp,i,hi,eq⟩
    · exact ⟨552,by simp,i,hi,eq⟩
  have bound : ∀ off ∈ ([528, 536, 544, 552] : List Nat),off+8 ≤ 2232 := by
    intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega
  have fu := after_effect pre frame ready effect.agrees writes bound
    (by simp [Blocks.CompareArgumentsEffect,Effect.components]) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    (by simp [Blocks.CompareArgumentsEffect,Effect.components]) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
  have pu := payload.after_stack pre effect.agrees writes bound
    (by simp [Blocks.CompareArgumentsEffect,Effect.components]) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    (by simp [Blocks.CompareArgumentsEffect,Effect.components])
  have regs : ∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue reg = t.regValue reg := by
    intro reg hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact effect.agrees.read (n:=64) (r:=3) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=5) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=12) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=13) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=14) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
    · exact effect.agrees.read (n:=64) (r:=15) (by simp [Blocks.CompareArgumentsEffect,Effect.components])
  have kept : ∀ i < 32,u.external[frameBase s+136+BitVec.ofNat 64 i]? = t.external[frameBase s+136+BitVec.ofNat 64 i]? := by
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using word_writes_byte writes effect.agrees
      (offset:=136+i) (by omega) (by intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; constructor <;> omega)
  obtain ⟨_,_,dx,si,di,_,_,_,_⟩ := effect.writes
  exact ⟨n,u,run,fu,pu,effect.rip,si.trans (congrArg (·+528) frame.rsp),di.trans r14,dx,regs,kept⟩

end P256.Proofs.Signing.Core.Iteration.Output
