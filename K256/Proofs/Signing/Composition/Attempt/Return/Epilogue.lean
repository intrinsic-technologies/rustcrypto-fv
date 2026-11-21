import K256.Proofs.Signing.Composition.Attempt.Return.State
import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Signing.LIR.Fn105420
import K256.Proofs.Common.Tactic
import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Composition.Attempt.Return

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Sec1.Serialize.Assemble (fourWordsAt wordsAtOffset)

private def epilogueWrites (p : BitVec 64) : List MemoryRegion :=
  [⟨(p+192).toNat,64⟩, ⟨(p+888).toNat,72⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem epilogueBlock {p : BitVec 64} {a : Registers} {m : Ram}
    (area : Writable Extracted.programImage m p 960)
    (rsp : a[4] = ⟨64,p⟩) (dst : memLoad m (p+416) 64 = p+888)
    (ret : memLoad m (p+808) 64 = 0x102795)
    {rWords sWords : Vector (BitVec 64) 4}
    (first : WordsAt m (p+8) 64 rWords) (second : WordsAt m (p+40) 64 sWords) :
    ∃ out : Output Value Ram Reg.count,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105e11,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,0x102795⟩ ∧
      RamWriteFrame m out.store (epilogueWrites p) ∧
      out.values[4] = ⟨64,p+816⟩ ∧ out.values[22] = a[22] ∧
      out.values[3] = ⟨64,memLoad m (p+760) 64⟩ ∧
      out.values[5] = ⟨64,memLoad m (p+800) 64⟩ ∧
      out.values[13] = ⟨64,memLoad m (p+776) 64⟩ ∧
      memLoad out.store (p+888) 64 = 0 ∧
      WordsAt out.store (p+896) 64 rWords ∧ WordsAt out.store (p+928) 64 sWords := by
  have lim := area.readable.low
  have rspBits : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have code : ∀ x ∈ codeRange 0x105e11 LIR.bytes_l105e11, x ∈ Extracted.programImage :=
    fun x hx => Common.fnCode_subset_programImage x (LIR.code_l105e11 x hx)
  have pos {off : BitVec 64} (h : off.toNat ≤ 960) :
      (p + off).toNat = p.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have slot (off : BitVec 64)
      (h : (192 ≤ off.toNat ∧ off.toNat + 8 ≤ 256) ∨
        (888 ≤ off.toNat ∧ off.toNat + 8 ≤ 960)) :
      InRegions (epilogueWrites p) (p + off) 8 := by
    have within : off.toNat ≤ 960 := by rcases h with h | h <;> omega
    rcases h with h | h
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change (p+192).toNat ≤ (p+off).toNat ∧
        (p+off).toNat + 8 ≤ (p+192).toNat + 64 ∧ (p+off).toNat + 8 ≤ 2^64
      rw [pos within, pos (off := 192) (by decide)]
      change p.toNat + 192 ≤ _ ∧ _ ≤ p.toNat + 192 + 64 ∧ _
      exact ⟨by omega, by omega, by omega⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      change (p+888).toNat ≤ (p+off).toNat ∧
        (p+off).toNat + 8 ≤ (p+888).toNat + 72 ∧ (p+off).toNat + 8 ≤ 2^64
      rw [pos within, pos (off := 888) (by decide)]
      change p.toNat + 888 ≤ _ ∧ _ ≤ p.toNat + 888 + 72 ∧ _
      exact ⟨by omega, by omega, by omega⟩
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [LIR.b_l105e11_1, rspBits, BitVec.add_assoc, BitVec.reduceAdd, Lift.reduceAddOffset]
    segment_words [dst, ret, BitVec.add_assoc, BitVec.reduceAdd, and_true]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code)
    refine Eq.trans (ite_eq_left ⟨by slot_guard using code, by decide⟩) ?_
    rfl
  case post =>
    refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
    · dsimp only [Output.store]
      iterate 17 refine RamWriteFrame.memStore ?_ _ ?_
      · exact .refl _ _
      all_goals exact slot _ (by decide)
    · segment_words []
    · apply fourWordsAt <;> segment_words [BitVec.add_assoc, BitVec.reduceAdd]
      · exact wordsAtOffset first 0 (by decide)
      · exact wordsAtOffset first 1 (by decide)
      · exact wordsAtOffset first 2 (by decide)
      · exact wordsAtOffset first 3 (by decide)
    · apply fourWordsAt <;> segment_words [BitVec.add_assoc, BitVec.reduceAdd]
      · exact wordsAtOffset second 0 (by decide)
      · exact wordsAtOffset second 1 (by decide)
      · exact wordsAtOffset second 2 (by decide)
      · exact wordsAtOffset second 3 (by decide)

theorem epilogue {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {r sigS : Nat}
    (input : Normalized s d r sigS a m) :
    ∃ b n, Reach (core .l105e11 a m) ⟨⟨.l102795,b,n⟩,[]⟩ ∧ Result s (r,sigS) b n := by
  have base : stackPtr s - 11192 = sp s + (-9904) := by unfold sp; bv_omega
  have window := input.toMemory.window call
  have area : Writable Extracted.programImage m (sp s) 960 :=
    window.of_offsets (addr_self _) base (by decide)
  obtain ⟨out, run, ret, writes, rsp, df, dst, rbp, r13, tag, first, second⟩ :=
    epilogueBlock area input.rsp input.resultPtr input.coreReturn input.first input.second
  have room := (stackBounds call).1
  have top := (stackBounds call).2.1
  have spNat := (stackBounds call).2.2
  have bottom : (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have pos {i : Nat} (hi : i ≤ 960) :
      (sp s + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat - 1288 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega), spNat]
  have inside : RegionsWithin (epilogueWrites (sp s)) [Stack.region s signingKeyTrySign.minStackBytes] := by
    intro r hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    rw [stackRegion call]
    simp only [epilogueWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change (stackPtr s - 11192).toNat ≤ (sp s+192).toNat ∧
        (sp s+192).toNat + 64 ≤ (stackPtr s - 11192).toNat + 11200
      rw [bottom, show (sp s+192).toNat = _ from pos (i := 192) (by decide)]
      exact ⟨by omega, by omega⟩
    · change (stackPtr s - 11192).toNat ≤ (sp s+888).toNat ∧
        (sp s+888).toNat + 72 ≤ (stackPtr s - 11192).toNat + 11200
      rw [bottom, show (sp s+888).toNat = _ from pos (i := 888) (by decide)]
      exact ⟨by omega, by omega⟩
  have keep {off : Nat} (hi : off ≤ 32) :
      memLoad out.store (stackPtr s - BitVec.ofNat 64 off) 64 =
        memLoad m (stackPtr s - BitVec.ofNat 64 off) 64 := by
    apply writes.memLoad_eq
    have addr := Common.stackOffset (off := off) call.stackAvailable (by change off ≤ 11192; omega)
    refine ⟨by rw [addr]; omega, ?_⟩
    intro r hr
    simp only [epilogueWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (sp s+192).toNat + 64 ≤ (stackPtr s - BitVec.ofNat 64 off).toNat
      rw [addr, show (sp s+192).toNat = _ from pos (i := 192) (by decide)]
      omega
    · right
      change (sp s+888).toNat + 72 ≤ (stackPtr s - BitVec.ofNat 64 off).toNat
      rw [addr, show (sp s+888).toNat = _ from pos (i := 888) (by decide)]
      omega
  have mem : Memory s out.store := ⟨input.written.trans writes inside,
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using keep (off := 0) (by decide) :
      memLoad out.store (stackPtr s) 64 = memLoad m (stackPtr s) 64).trans input.ret,
    (keep (off := 32) (by decide)).trans input.savedWrapperRBX,
    (keep (off := 24) (by decide)).trans input.savedWrapperR12,
    (keep (off := 16) (by decide)).trans input.savedWrapperR14,
    (keep (off := 8) (by decide)).trans input.savedWrapperR15⟩
  refine ⟨out.values,out.store,.single ?_,
    ⟨mem,rsp,?_,?_,?_,df.trans input.df,tag,first,second⟩⟩
  · change (LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105e11,a,m⟩).next
      (dialect Extracted.programImage) [resume .l102795 0x102795] = _
    rw [run]
    have loc : (resume .l102795 0x102795).resume out =
        (⟨.l102795,out.values,out.store⟩ : LIR.lifted.Location) :=
      congrArg (fun args => (⟨.l102795,args,out.store⟩ : LIR.lifted.Location))
        (ParseSignature.resume_arguments (resume .l102795 0x102795) out)
    have accepts : (resume .l102795 0x102795).Accepts (dialect Extracted.programImage) out.tag = true := by
      rw [ret]
      rfl
    simp only [Transfer.next, accepts, ↓reduceIte, loc]
    rfl
  · exact dst.trans (congrArg (fun w => (⟨64,w⟩ : Value)) input.savedOutput)
  · exact rbp.trans (congrArg (fun w => (⟨64,w⟩ : Value)) input.savedRbp)
  · exact r13.trans (congrArg (fun w => (⟨64,w⟩ : Value)) input.savedR13)

end K256.Proofs.Signing.Composition.Attempt.Return
