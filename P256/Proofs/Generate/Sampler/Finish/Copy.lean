import P256.Proofs.Generate.Sampler.Finish.InputCopy
import P256.Proofs.Generate.Sampler.Finish.OutputCopy
import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Field (AdvanceTriple)

theorem copy_byte {t u : RamState} {base dst src : BitVec 64} {len : Nat}
    (agrees : AgreesExcept (Copy32.components (base + dst)) t u)
    (apart : OffsetsApart dst 32 src len) (bound : 32 + len < 2^64)
    (i : Nat) (hi : i < len) :
    u.external[base + src + BitVec.ofNat 64 i]? =
      t.external[base + src + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc cover
  simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> try exact cover.elim
  obtain ⟨j,hj,eq⟩ := cover
  exact apart.ne base hj hi bound eq.symm

theorem copy [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray} {d : Nat}
    (pre : Pre s boundary input) (state : State s t) (second : Bool)
    (rip : t.RIP = if second then 0x100d54 else 0x100d1d)
    (scalar : Nat256At t (stackPtr t + BitVec.ofNat 64 (if second then 8 else 8)) d) :
    ∃ n u, Advances boundary n t u ∧ State s u ∧
      u.RIP = (if second then 0x100d7c else 0x100d45) ∧
      Nat256At u (stackPtr u + BitVec.ofNat 64 (if second then 80 else 40)) d ∧
      AgreesExcept (Copy32.components
        (stackPtr t + BitVec.ofNat 64 (if second then 80 else 40))) t u := by
  let src : Nat := if second then 8 else 8
  let dst : Nat := if second then 80 else 40
  let off : Nat := if second then 0xd54 else 0xd1d
  let len : Nat := if second then 40 else 40
  let code := if second then OutputCopy.bytes else InputCopy.bytes
  have block : AdvanceTriple boundary
      (Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 off)
        (fun q => (Operand.reg 4 : Operand 64).read q + BitVec.ofNat 64 src)
        (fun q => (Operand.reg 4 : Operand 64).read q + BitVec.ofNat 64 dst))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 off) code)
      (Effect.post (Copy32.effect (Extracted.textAddress + BitVec.ofNat 64 off + BitVec.ofNat 64 len)
        (fun q => (Operand.reg 4 : Operand 64).read q + BitVec.ofNat 64 src)
        (fun q => (Operand.reg 4 : Operand 64).read q + BitVec.ofNat 64 dst))) := by
    cases second
    · exact InputCopy.run boundary pre.outerBoundary off (by decide)
    · exact OutputCopy.run boundary pre.outerBoundary off (by decide)
  have hp : Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 off)
      (fun q => (Operand.reg 4 : Operand 64).read q + BitVec.ofNat 64 src)
      (fun q => (Operand.reg 4 : Operand 64).read q + BitVec.ofNat 64 dst) t := by
    refine ⟨by cases second <;> exact rip, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_readable pre (offset := src + 0) (len := 8) (by cases second <;> decide)
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_readable pre (offset := src + 8) (len := 8) (by cases second <;> decide)
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_readable pre (offset := src + 16) (len := 8) (by cases second <;> decide)
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_readable pre (offset := src + 24) (len := 8) (by cases second <;> decide)
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          (state.stack_writable pre (offset := dst + 0) (len := 8)
            (by cases second <;> decide)).crossPage (by decide)
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          (state.stack_writable pre (offset := dst + 8) (len := 8)
            (by cases second <;> decide)).crossPage (by decide)
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          (state.stack_writable pre (offset := dst + 16) (len := 8)
            (by cases second <;> decide)).crossPage (by decide)
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          (state.stack_writable pre (offset := dst + 24) (len := 8)
            (by cases second <;> decide)).crossPage (by decide)
    · intro i hi j hj he
      cases second <;> exact (show OffsetsApart _ 32 _ 32 by
        unfold OffsetsApart; decide +kernel).ne (stackPtr t) hi hj (by decide) he
    · intro i hi k l bound
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_code pre (offset := dst + 0) (len := 8)
            (by cases second <;> decide) bound
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_code pre (offset := dst + 8) (len := 8)
            (by cases second <;> decide) bound
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_code pre (offset := dst + 16) (len := 8)
            (by cases second <;> decide) bound
      · simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
          state.stack_code pre (offset := dst + 24) (len := 8)
            (by cases second <;> decide) bound
  obtain ⟨n,u,run,ready,_,effect⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) off code
      (by cases second <;> decide) (by cases second <;> decide +kernel)) hp
  have g := Copy32.frame effect
  have rsp : stackPtr u = stackPtr t := g.read (n := 64) (r := 4) (by simp [Copy32.components])
  have next := state.after pre ready g (by
    intro c hc a ha
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨ScalarFrame.workRegion s 3624, by simp [bodyWrites],
      state.work_writes pre (offset := dst) (len := 32) (by cases second <;> decide) ha⟩) rsp
  have copied := Copy32.copy_bytes effect
    (state.stack_readable pre (offset := src) (len := 32) (by cases second <;> decide))
    (by
      change MemReadable u (stackPtr t + BitVec.ofNat 64 dst) 32
      simpa only [rsp] using next.stack_readable pre (offset := dst) (len := 32) (by cases second <;> decide))
  refine ⟨n,u,run,next,?_,?_,g⟩
  · cases second <;> exact effect.rip
  · rw [rsp]
    exact ⟨scalar.1,fun i hi => (copied i hi).trans (scalar.2 i hi)⟩

end P256.Proofs.Generate.Sampler.Finish
