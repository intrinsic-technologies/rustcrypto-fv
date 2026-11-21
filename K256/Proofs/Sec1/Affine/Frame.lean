import K256.Proofs.Sec1.Affine.Entry
import K256.Proofs.Sec1.Affine.Contract
import K256.Proofs.Sec1.Affine.Return
import K256.Proofs.Sec1.Wrapper.ParserFrame
import K256.Proofs.Sec1.Parser.CalleeMemory

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def activation (s : RamState) : Activation :=
  let sp := s.regValue .rsp - 600
  { Activation.ofEntry s 1800 0x1064f4 with
    rsp := sp - 8, rbx := sp + 160, rdi := sp + 160, rsi := sp + 4,
    r12 := 0, r14 := s.regValue .rdx, r15 := s.regValue .rsp - 112 }

theorem savedSlots (args : Values Value Reg.count) (mem : Ram) :
    let sp := args[4].get 64
    let m := saveRegisters args mem
    memLoad m (sp - 40) 64 = args[3].get 64 ∧ memLoad m (sp - 32) 64 = args[12].get 64 ∧
    memLoad m (sp - 24) 64 = args[14].get 64 ∧ memLoad m (sp - 16) 64 = args[15].get 64 ∧
    memLoad m (sp - 8) 64 = args[5].get 64 := by
  dsimp only
  let sp := args[4].get 64
  let first := memStore mem (sp - 8) (args[5].get 64)
  have eq : saveRegisters args mem = Parser.Frame.savedRegistersMemory first (sp - 8) args := by
    simp only [saveRegisters, Parser.Frame.savedRegistersMemory, first, sp, BitVec.sub_sub]
    rfl
  obtain ⟨bx, r12, r14, r15, bp⟩ := Parser.Frame.savedRegistersMemory_load first (sp - 8) args
  rw [eq]
  simp only [BitVec.sub_sub] at bx r12 r14 r15
  exact ⟨bx, r12, r14, r15, bp.trans (memLoad_memStore_same _ _ _ (by decide) (by decide))⟩

theorem EntryAt.stackFrame {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m) :
    RamWriteFrame s.external m [Stack.region s publicKeyFromSec1Bytes.minStackBytes] :=
  (Parser.packingSavedSlots call e.frame).writes

theorem EntryAt.registers {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m) :
    args[22] = ⟨1,0⟩ ∧ ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,39,50,51] →
      args[i] = (activation s).entryValue i.val := by
  have keep (i : Fin Reg.count) (hi : i.val ∈ [5,13,22,39,50,51]) :
      args[i] = (Reg.ofIndex i).read s := by
    have h := e.kept i hi
    change args[i.val] = (Wrapper.parserArgs s)[i.val] at h
    rw [Wrapper.parserArgs_get s i] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simpa only [Fin.getElem_fin, show i.val ≠ 14 by omega, show i.val ≠ 7 by omega, show i.val ≠ 4 by omega, ↓reduceIte] using h
  constructor
  · exact (keep 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset)
  · rintro ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e.base
    · exact keep 5 (by decide)
    · exact e.r12
    · exact keep 13 (by decide)
    · exact e.r14
    · exact e.r15
    · exact keep 39 (by decide)
    · exact keep 50 (by decide)
    · exact keep 51 (by decide)

theorem rootStackOffset {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (off : BitVec 64) (h : off.toNat ≤ 1928) :
    (s.regValue .rsp - off).toNat = (s.regValue .rsp).toNat - off.toNat := by
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)

theorem activationOutputWritable {s : RamState} {bytes : ByteArray} {mem : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (frame : RamWriteFrame s.external mem [Stack.region s publicKeyFromSec1Bytes.minStackBytes]) :
    Writable Extracted.programImage mem (activation s).rdi 89 := by
  change Writable _ _ (s.regValue .rsp - 600 + 160) 89
  rw [show s.regValue .rsp - 600 + 160 = s.regValue .rsp - 440 by bv_omega]
  exact (Wrapper.stackWritable (offset := 440) call (by decide) (by decide) (by decide)).of_frame frame

theorem activationOutputAbove {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    (activation s).rsp.toNat + 8 ≤ (activation s).rdi.toNat := by
  change (s.regValue .rsp - 600 - 8).toNat + 8 ≤ (s.regValue .rsp - 600 + 160).toNat
  rw [show s.regValue .rsp - 600 - 8 = s.regValue .rsp - 608 by bv_omega,
    show s.regValue .rsp - 600 + 160 = s.regValue .rsp - 440 by bv_omega,
    rootStackOffset call 608 (by decide), rootStackOffset call 440 (by decide)]
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  change (s.regValue .rsp).toNat - 608 + 8 ≤ (s.regValue .rsp).toNat - 440
  omega

theorem EntryAt.start {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m) :
    let fr := activation s
    let tag := (bytes.data[0]?.getD 0).toBitVec
    let label := if 2 ≤ tag.toNat ∧ tag.toNat < 6 then Label.l1214a0 else .l1214d0
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l121480,args,m⟩ =
        .jump ⟨label,next,saveRegisters args m⟩ ∧
      next[0] = ⟨64,tag.setWidth 64⟩ ∧ next[1] = ⟨64,tag.setWidth 64⟩ ∧ next[2] = ⟨64,fr.rsi⟩ ∧
      Atom.All Extracted.programImage next (saveRegisters args m) (Fn121480.frameAt .l121599 fr) ∧
      RamWriteFrame m (saveRegisters args m) [⟨(fr.rsp-40).toNat,40⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,15] → next[i] = args[i]) := by
  dsimp only
  let fr := activation s
  let src := fr.rsi
  let tag := (bytes.data[0]?.getD 0).toBitVec
  have stackEq : fr.rsp = s.regValue .rsp - 608 := by dsimp only [fr,activation]; bv_omega
  have sourceEq : src = s.regValue .rsp - 596 := by dsimp only [src,fr,activation]; bv_omega
  have saveEq : fr.rsp - 40 = s.regValue .rsp - 648 := by rw [stackEq]; bv_omega
  have bottomEq : fr.rsp - 1192 = s.regValue .rsp - 1800 := by rw [stackEq]; bv_omega
  have off := rootStackOffset call
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have bound : (s.regValue .rsp).toNat < 2^64 := (s.regValue .rsp).isLt
  have localWrite (n k : Nat) (hn : n ≤ 1928) (hk : k ≤ n + 8) (pos : 0 < k) :
      Writable Extracted.programImage m (s.regValue .rsp - BitVec.ofNat 64 n) k :=
    (Wrapper.stackWritable call hn hk pos).of_frame (e.stackFrame call)
  have stackRead : Readable m fr.rsp 8 := by rw [stackEq]; exact (localWrite 608 8 (by decide) (by decide) (by decide)).readable
  have savedWrite : Writable Extracted.programImage m (fr.rsp - 40) 40 := by
    rw [saveEq]; exact localWrite 648 40 (by decide) (by decide) (by decide)
  have read : Readable m src 1 := by rw [sourceEq]; exact (localWrite 596 1 (by decide) (by decide) (by decide)).readable
  have outside (p : BitVec 64) (k n : Nat) (small : k ≤ 608) (len : n ≤ 8)
      (hp : p = s.regValue .rsp - BitVec.ofNat 64 k) : Outside [⟨(fr.rsp - 40).toNat,40⟩] p n := by
    have a : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [hp, saveEq]
    have base := off 648 (by decide)
    change (s.regValue .rsp - 648).toNat = (s.regValue .rsp).toNat - 648 at base
    have ak := off (BitVec.ofNat 64 k) (by rw [a]; omega)
    rw [a] at ak
    apply And.intro
    · rw [ak]
      have h := stackRead.low
      rw [stackEq, off 608 (by decide)] at h
      change (s.regValue .rsp).toNat - 608 + 8 ≤ 2^32 at h
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      dsimp only
      omega
  have sp : args[4].get 64 = fr.rsp := congrArg (Value.get 64) e.stack
  have tagEq : memLoad m src 8 = tag := by
    apply memLoad_eq_of_memByte (by decide)
    intro j hj
    obtain rfl : j = 0 := by omega
    exact (e.input 0 (by decide)).trans (by simp [tag, storedByte])
  obtain ⟨next, step, ax, cx, dx, bx, rsp, writes, keeps⟩ :=
    affineEntry Common.fnCode_subset_programImage args m fr.rsp src fr.rdi sp
      (congrArg (Value.get 64) e.source) (congrArg (Value.get 64) e.output) savedWrite
      (by rw [stackEq, off 608 (by decide)]; change 40 ≤ (s.regValue .rsp).toNat - 608; omega)
      read (outside src 596 1 (by decide) (by decide) sourceEq)
  obtain ⟨df, init⟩ := e.registers call
  have saved := savedSlots args m
  dsimp only at saved
  rw [sp] at saved
  obtain ⟨b, r12, r14, r15, bp⟩ := saved
  have kept (i : Fin Reg.count) (hi : i.val ∈ [13,39,50,51]) : next[i] = fr.entryValue i.val :=
    (keeps i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (init i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  have win : Writable Extracted.programImage m (fr.rsp-1192) 1192 := by
    rw [bottomEq]; exact localWrite 1800 1192 (by decide) (by decide) (by decide)
  have big := show fr.low.toNat = (s.regValue .rsp).toNat - 1800 from Activation.ofEntry_low_toNat (ret := 0x1064f4) (s := s) (stackBytes := 1800)
  have retAfter : memLoad (saveRegisters args m) fr.rsp 64 = fr.ret :=
    (writes.memLoad_eq (outside fr.rsp 608 8 (by decide) (by decide) stackEq)).trans e.ret
  have aligned : (s.regValue .rsp).toNat % 16 = 8 := call.stackAvailable.2.2.2
  rw [tagEq] at ax cx step
  refine ⟨next, ?_, ax, cx, dx, ?_, writes, fun i hi => keeps i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)⟩
  · have choose {α : Type} (P : Prop) [Decidable P] (f : Label → α) :
        (if decide P then f .l1214a0 else f .l1214d0) = f (if P then .l1214a0 else .l1214d0) := by
      by_cases h : P <;> simp [h]
    exact step.trans (choose (2 ≤ tag.toNat ∧ tag.toNat < 6) (fun l => Transfer.jump ⟨l,next,saveRegisters args m⟩))
  · simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds]
    refine ⟨rsp,(keeps 22 (by decide)).trans df,bx,kept 13 (by decide),kept 39 (by decide),
      kept 50 (by decide),kept 51 (by decide), b.trans (congrArg (Value.get 64) (init 3 (by decide))),
      r12.trans (congrArg (Value.get 64) (init 12 (by decide))),
      r14.trans (congrArg (Value.get 64) (init 14 (by decide))),
      r15.trans (congrArg (Value.get 64) (init 15 (by decide))),
      bp.trans (congrArg (Value.get 64) (init 5 (by decide))),
      stackRead.of_frame writes, retAfter, (by change 0x1064f4 < 2^(32:Nat); decide), win.of_frame writes, ?_, ?_, trivial⟩
    · change fr.low.toNat + 1192 ≤ fr.rsp.toNat
      rw [big, stackEq, off 608 (by decide)]
      change (s.regValue .rsp).toNat - 1800 + 1192 ≤ (s.regValue .rsp).toNat - 608
      omega
    · change fr.rsp.toNat % 16 = 8
      rw [stackEq, off 608 (by decide)]
      change ((s.regValue .rsp).toNat - 608) % 16 = 8
      omega

end K256.Proofs.Sec1.Affine
