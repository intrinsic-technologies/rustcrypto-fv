import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Output.FlagStore
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Result
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Transferred [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110d1a
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (s.regValue .rdi)
    (if valid bytes then canonical (xCoordinate bytes) else 0)
  y : Field.MontgomeryAt t (s.regValue .rdi+32)
    (if valid bytes then canonical (yCoordinate bytes) else 0)
  choice : (t.regValue .rbp).setWidth 8 = if valid bytes then 1 else 0
  infinity : (t.regValue .r15).setWidth 8 = if valid bytes then 0 else 1

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Transferred s t bytes)
    (size : bytes.size = 65) (tag : bytes.data[0]? = some 4) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (Spec.Points.decodePoint bytes) := by
  have writable (off : Nat) (bound : off < 80) :
      MemWritable t (s.regValue .rdi+BitVec.ofNat 64 off) 1 := by
    have h := (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add
      off (len := 1) (by omega)
    exact ⟨h.low, h.mem, h.tables⟩
  have hp : ResultStorePre t := by
    refine ⟨state.rip,?_,?_⟩
    · intro off member
      change MemWritable t (t.regValue .rbx+off) 1
      rw [state.output]
      have h : off = 64 ∨ off = 72 := by simpa using member
      rcases h with rfl | rfl
      · exact writable 64 (by decide)
      · exact writable 72 (by decide)
    · intro off member pc len bound
      change RangeApart (t.regValue .rbx+off) 1 _ len
      rw [state.output]
      have h : off = 64 ∨ off = 72 := by simpa using member
      rcases h with rfl | rfl
      all_goals exact (P256.Proofs.Common.Instructions.RangeApart.add_left
        (ScalarFrame.output_code pre.toCalleePre bound) _ (by decide))
  obtain ⟨n,u,run,ready,_,effect⟩ := result_store boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10d1a resultStoreBytes
      (by decide) (by decide +kernel)) hp
  have agrees : AgreesExcept [.mem (s.regValue .rdi+64) 1,.mem (s.regValue .rdi+72) 1,.rip] t u := by
    have h := effect.agrees
    simp only [resultStoreEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
      Operand.component,List.append_nil,List.cons_append,List.nil_append,Nat.reduceDiv] at h
    change AgreesExcept [.mem (t.regValue .rbx+64#64) 1,.mem (t.regValue .rbx+72#64) 1,.rip] t u at h
    rw [state.output] at h
    exact h
  have writes : WritesWithin [.mem (s.regValue .rdi+64) 1,.mem (s.regValue .rdi+72) 1,.rip]
      #v[registerRegion s .rdi 80] := by
    intro c hc a covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨_,by simp,ScalarFrame.output_contains pre.toCalleePre (by decide) covered⟩
    · exact ⟨_,by simp,ScalarFrame.output_contains pre.toCalleePre (by decide) covered⟩
    · exact covered.elim
  have frame := after_output pre state.toFrameState ready agrees writes (by simp)
  have kept := bytes_of_offsets (base := s.regValue .rdi) agrees (offset := 0) (len := 64)
    (by decide) (by
      intro address count mem
      simp only [List.mem_cons,List.not_mem_nil,or_false,
        Component.mem.injEq,reduceCtorEq] at mem
      rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨64,rfl,by decide,Or.inr (by decide)⟩
      · exact ⟨72,rfl,by decide,Or.inr (by decide)⟩)
  simp only [BitVec.add_zero] at kept
  have xu := state.x.of_bytes_eq (fun i hi => kept i (by omega))
  have yu := state.y.of_bytes_eq (t := u) (destination := s.regValue .rdi+32) (fun i hi => by
    have h := kept (32+i) (by omega)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using h)
  have byte {address : BitVec 64} {value : UInt8} (allocated : (u.external[address]?).isSome)
      (word : memLoad u.external address 8 = value.toBitVec) : u.external[address]? = some value := by
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp allocated
    exact hv.trans (congrArg some (UInt8.eq_of_toBitVec_eq
      ((P256.Proofs.Common.Memory.memLoad8_of_byte hv).symm.trans word)))
  have infiniteWord : memLoad u.external (s.regValue .rdi+64) 8 = if valid bytes then 0 else 1 := by
    have h : memLoad u.external (t.regValue .rbx+64) 8 = (t.regValue .r15).setWidth 8 := effect.writes.1
    rwa [state.output,state.infinity] at h
  have choiceWord : memLoad u.external (s.regValue .rdi+72) 8 = if valid bytes then 1 else 0 := by
    have h : memLoad u.external (t.regValue .rbx+72) 8 = (t.regValue .rbp).setWidth 8 := effect.writes.2
    rwa [state.output,state.choice] at h
  have outputMemory := ScalarFrame.output_writable pre.toCalleePre (by decide) frame.allocated
  have infiniteByte : u.external[s.regValue .rdi+64]? = some (if valid bytes then 0 else 1) :=
    byte (outputMemory.mem 64 (by decide)) (by cases hv : valid bytes <;> simpa [hv] using infiniteWord)
  have choiceByte : u.external[s.regValue .rdi+72]? = some (if valid bytes then 1 else 0) :=
    byte (outputMemory.mem 72 (by decide)) (by cases hv : valid bytes <;> simpa [hv] using choiceWord)
  exact ⟨n,u,run,frame,effect.rip,result_of_fields size tag xu yu infiniteByte choiceByte⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Output
