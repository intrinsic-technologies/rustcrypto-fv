import K256.Proofs.Sec1.Parser.Control
import K256.Proofs.Sec1.Parser.Frame.Return
import K256.Proofs.Sec1.Parser.Memory
import K256.Proofs.Sec1.Wrapper.Contracts

namespace K256.Proofs.Sec1.Parser.Result

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

structure SavedSlots (s : RamState) (mem : Ram) : Prop where
  savedR15 : memLoad mem (s.regValue .rsp - 264) 64 = s.regValue .r15
  savedR14 : memLoad mem (s.regValue .rsp - 272) 64 = s.regValue .rdi
  savedR12 : memLoad mem (s.regValue .rsp - 280) 64 = s.regValue .r12
  parserRet : memLoad mem (s.regValue .rsp - 256) 64 = 0x101dea
  wrapperRbx : memLoad mem (s.regValue .rsp - 16) 64 = s.regValue .rbx
  wrapperR14 : memLoad mem (s.regValue .rsp - 8) 64 = s.regValue .r14
  wrapperRet : memLoad mem (s.regValue .rsp) 64 = (X86Proofs.returnBoundary s).rip
  writes : RamWriteFrame s.external mem [Wrapper.stack s]

structure ExitFrame (s : RamState) (args : Values Value Reg.count) (mem : Ram) : Prop
    extends SavedSlots s mem where
  rsp : args[4].get 64 = s.regValue .rsp - 600
  rdi : args[7].get 64 = s.regValue .rsp - 112
  kept : ∀ i : Fin Reg.count, i.val ∈ [5, 13, 22] → args[i] = (Reg.ofIndex i).read s

private theorem finishExit {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count}
    {mem : Ram} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (frame : ExitFrame s args mem)
    (reached : Reaches Extracted.programImage .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s)
      .l106565 args mem) (status : BitVec 64) (rax : args[0].get 64 = status) :
    ∃ out, Wrapper.Run .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s) out ∧
      out.tag = some ⟨64, 0x101dea⟩ ∧ Wrapper.CallerFrame s [Wrapper.stack s] out.values out.store ∧
      out.store = memStore mem (s.regValue .rsp - 112) status := by
  let sp := s.regValue .rsp
  let entry := sp - 256
  let dst := sp - 112
  have savedSlot (off : BitVec 64) : entry - off = sp - (256 + off) := BitVec.sub_sub ..
  have writable : Writable Extracted.programImage mem dst 8 :=
    (Wrapper.stackWritable (offset := 112) call (by decide) (by decide) (by decide)).of_frame frame.writes
  have slots : Readable mem (entry - 32) 40 := by
    rw [savedSlot]
    exact ((Wrapper.stackWritable (offset := 288) (len := 40) call (by decide) (by decide)
      (by decide)).of_frame frame.writes).readable
  have apart : RangeApart dst 8 (entry - 32) 40 := by
    rw [savedSlot]
    exact RangeApart.of_offsets (addr_sub sp 112) (addr_sub sp 288) (by decide)
  obtain ⟨out, block, store, tag, _, outSp, _, r12, r14, r15, preserved⟩ :=
    Frame.returnBlock (sp := entry) (by rw [savedSlot]; exact frame.rsp) frame.rdi rax writable
      (fun x hx => Common.fnCode_subset_programImage x (code_l106565 x hx))
      slots apart frame.parserRet (by decide)
  have done : Wrapper.Run .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s) out :=
    Program.Exec.of_sem (reached.exec (.ret (congrArg (Transfer.next _ []) block)))
  have untouched {a : BitVec 64} (sep : RangeApart dst 8 a 8) :
      memLoad out.store a 64 = memLoad mem a 64 := by
    rw [store]
    exact memLoad_memStore_of_rangeApart _ _ _ _ _ sep
  have unchanged (off : BitVec 64)
      (sep : 8 ≤ ((0 - off) - (0 - (112 : BitVec 64))).toNat ∧
        8 ≤ ((0 - (112 : BitVec 64)) - (0 - off)).toNat) :
      memLoad out.store (sp - off) 64 = memLoad mem (sp - off) 64 :=
    untouched (RangeApart.of_offsets (addr_sub sp 112) (addr_sub sp off) sep)
  have restored (i : Fin Reg.count) (hi : i.val ∈ [5, 13, 22]) :
      out.values[i] = (Reg.ofIndex i).read s :=
    (preserved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (frame.kept i hi)
  refine ⟨out, done, tag, ⟨?_, ?_, ?_, (unchanged 16 (by decide)).trans frame.wrapperRbx,
    (unchanged 8 (by decide)).trans frame.wrapperR14, ?_, ?_⟩, store⟩
  · exact outSp.trans (congrArg (Value.mk 64) (show entry + 8 = sp - 248 by dsimp only [entry]; bv_omega))
  · rw [r14, savedSlot]
    exact congrArg (Value.mk 64) frame.savedR14
  · intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact restored 5 (by decide)
    · exact r12.trans (congrArg (Value.mk 64) (by rw [savedSlot]; exact frame.savedR12))
    · exact restored 13 (by decide)
    · exact r15.trans (congrArg (Value.mk 64) (by rw [savedSlot]; exact frame.savedR15))
    · exact restored 22 (by decide)
  · exact (untouched (RangeApart.of_offsets (addr_sub sp 112) (addr_self sp) (by decide))).trans
      frame.wrapperRet
  · rw [store]
    exact frame.writes.memStore _ (stackRange (off := 112) call (by decide) (by decide))

theorem parserCall {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {mem : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (frame : ExitFrame s args mem)
    (exit :
      (Secp256k1.decodePublicKey bytes = none ∧
        Reaches Extracted.programImage .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s)
          .l106560 args mem) ∨
      (∃ point, Secp256k1.decodePublicKey bytes = some point ∧
        Reaches Extracted.programImage .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s)
          .l106565 args mem ∧ args[0].get 64 = 0 ∧ PublicKeyAt mem (s.regValue .rsp - 104) point)) :
    Wrapper.ParserCall s bytes := by
  let sp := s.regValue .rsp
  rcases exit with ⟨reject, reached⟩ | ⟨point, accept, reached, rax, payload⟩
  · obtain ⟨next, step, one, keep⟩ :=
      Frame.failBlock (code := Extracted.programImage) (args := args) (mem := mem)
    have newFrame : ExitFrame s next mem := {
      frame with
      rsp := (congrArg (Value.get 64) (keep 4 (by decide))).trans frame.rsp
      rdi := (congrArg (Value.get 64) (keep 7 (by decide))).trans frame.rdi
      kept := fun i hi => (keep i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega)).trans (frame.kept i hi) }
    obtain ⟨out, run, tag, caller, store⟩ :=
      finishExit call newFrame (reached.trans (reaches_jump step)) 1 (congrArg (Value.get 64) one)
    refine ⟨out, run, tag, caller, ?_⟩
    rw [reject, store]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · obtain ⟨out, run, tag, caller, store⟩ := finishExit call frame reached 0 rax
    refine ⟨out, run, tag, caller, ?_⟩
    rw [accept, store]
    obtain ⟨x, y, coords, affine⟩ := payload
    refine ⟨memLoad_memStore_same _ _ _ (by decide) (by decide), x, y, coords, affine.of_copy ?_⟩
    have apart : RangeApart (sp - 112) 8 (sp - 104) 88 :=
      RangeApart.of_offsets (addr_sub sp 112) (addr_sub sp 104) (by decide)
    intro off width fits
    exact memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.right_sub apart fits)

end K256.Proofs.Sec1.Parser.Result
