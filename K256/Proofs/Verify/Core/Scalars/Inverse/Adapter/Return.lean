import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Barrier
import K256.Proofs.Verify.Core.Scalars.State
import K256.Proofs.Verify.Core.Serializer.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Adapter

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def returnWrites (x : BitVec 64) : List MemoryRegion :=
  [⟨(x-9).toNat,17⟩, ⟨(x+104).toNat,33⟩]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem returnInverse {b : Registers} {m : Ram} {x : BitVec 64} {v : Vector (BitVec 64) 4}
    (stack : Writable Extracted.programImage m (x-9) 146)
    (room : 9 ≤ x.toNat) (low : x.toNat + 137 ≤ 2^32)
    (rsp : b[4] = ⟨64,x⟩) (dst : b[3] = ⟨64,x+104⟩)
    (words : WordsAt m (x+8) 64 v) (flag : memLoad m (x+40) 8 = 1)
    (ret : memLoad m (x+88) 64 = 0x10519d) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a0f2,b,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x10519d⟩ ∧ out.values[4] = ⟨64,x+96⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,22,39,50,51] → out.values[i] = b[i]) ∧
      (∀ (i : Fin Reg.count) (d : BitVec 64), (i.val,d) ∈ [(3,48),(12,56),(13,64),(14,72),(15,80)] →
        out.values[i] = ⟨64,memLoad m (x+d) 64⟩) ∧
      WordsAt out.store (x+104) 64 v ∧ memLoad out.store (x+136) 8 = 1 ∧
      RamWriteFrame m out.store (returnWrites x) := by
  have rspBits : b[4].get 64 = x := congrArg (Value.get 64) rsp
  have word0 : memLoad m (x+8) 64 = v[0] := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using words 0 (by decide)
  have word1 : memLoad m (x+16) 64 = v[1] := by
    have h := words 1 (by decide)
    dsimp only [wordAddr] at h
    rw [BitVec.add_assoc] at h
    exact h
  have word2 : memLoad m (x+24) 64 = v[2] := by
    have h := words 2 (by decide)
    dsimp only [wordAddr] at h
    rw [BitVec.add_assoc] at h
    exact h
  have word3 : memLoad m (x+32) 64 = v[3] := by
    have h := words 3 (by decide)
    dsimp only [wordAddr] at h
    rw [BitVec.add_assoc] at h
    exact h
  have lowByte : (memLoad m (x+40) 32).setWidth 8 = 1 := by
    rw [← flag]
    have h32 := storedByte_memLoad m (x+40) (n := 32) 0 (by decide)
    have h8 := storedByte_memLoad m (x+40) (n := 8) 0 (by decide)
    have eq := congrArg UInt8.toBitVec (h32.trans h8.symm)
    simpa only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, UInt8.toBitVec_ofNat',
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using eq
  have firstCode : ∀ p ∈ codeRange 0x10a0f2 bytes_l10a0f2, p ∈ Extracted.programImage :=
    fun p hp => Common.fnCode_subset_programImage p (code_l10a0f2 p hp)
  have call : ∃ a : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l10a0f2,b,m⟩ =
        .call ⟨.l127d50,a,memStore m (x-8) (0x10a10f : BitVec 64)⟩ (Reduce.resume .l10a10f 0x10a10f) ∧
      a[4].get 64 = x-8 ∧ (a[7].get 64).setWidth 8 = 1 ∧
      a[14] = ⟨64,v[0]⟩ ∧ a[15] = ⟨64,v[1]⟩ ∧ a[12] = ⟨64,v[2]⟩ ∧ a[13] = ⟨64,v[3]⟩ ∧
      a[3] = b[3] ∧ a[5] = b[5] ∧ a[22] = b[22] ∧ a[39] = b[39] ∧
      a[50] = b[50] ∧ a[51] = b[51] := by
    refine ⟨?args, ?runCall, ?stackCall, ?flagCall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case runCall =>
      cfg_eval [rspBits, word0, word1, word2, word3]
      simp (disch := slot_guard using firstCode) only [ite_eq_left]
      rfl
    case stackCall => rfl
    case flagCall =>
      change ((memLoad m (x+40) 32).setWidth 64 |>.setWidth 8) = 1
      simpa only [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide)] using lowByte
    all_goals rfl
  obtain ⟨a, call, pushSp, choice, a14, a15, a12, a13, a3, a5, a22, a39, a50, a51⟩ := call
  have window : Writable Extracted.programImage m (x-9) 9 :=
    stack.sub (Nat.le_refl _) (by omega)
  obtain ⟨c,n,reach,sp,success,scratch,keep⟩ :=
    Reduce.barrier call pushSp window room (by decide)
  have spBits : c[4].get 64 = x := congrArg (Value.get 64) sp
  have dstBits : c[3].get 64 = x+104 :=
    congrArg (Value.get 64) ((keep 3 (by decide)).trans (a3.trans dst))
  have byte : (c[0].get 64).setWidth 8 = 1 := by rw [success, choice]; rfl
  have c14 := (keep 14 (by decide)).trans a14
  have c15 := (keep 15 (by decide)).trans a15
  have c12 := (keep 12 (by decide)).trans a12
  have c13 := (keep 13 (by decide)).trans a13
  let marked := memStore n (x+7) (1 : BitVec 8)
  let stored := memStore (memStore (memStore (memStore marked (x+104) v[0])
    (x+104+8) v[1]) (x+104+16) v[2]) (x+104+24) v[3]
  let result := memStore stored (x+136) (1 : BitVec 8)
  have mark : memLoad marked (x+7) 8 = 1 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have dstLow : (x+104).toNat + 32 ≤ 2^64 := by bv_omega
  have markedFrame : RamWriteFrame m marked (returnWrites x) := by
    refine ((RamWriteFrame.refl _ _).trans scratch ?_).memStore _ ?_
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, by change (x-9).toNat + 9 ≤ (x-9).toNat + 17; omega⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change (x-9).toNat ≤ (x+7).toNat ∧ (x+7).toNat+1 ≤ (x-9).toNat+17 ∧ _
      bv_omega
  have storedFrame : RamWriteFrame m stored (returnWrites x) :=
    Serializer.storeWords_frame v markedFrame
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, by change (x+104).toNat + 32 ≤ (x+104).toNat + 33; omega, dstLow⟩
  have resultFrame : RamWriteFrame m result (returnWrites x) := by
    apply storedFrame.memStore
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change (x+104).toNat ≤ (x+136).toNat ∧ (x+136).toNat+1 ≤ (x+104).toNat+33 ∧ _
    bv_omega
  have saved (d : BitVec 64) (lower : 48 ≤ d.toNat) (upper : d.toNat ≤ 88) :
      memLoad result (x+d) 64 = memLoad m (x+d) 64 := by
    apply resultFrame.memLoad_eq
    refine ⟨by bv_omega, fun r hr => ?_⟩
    simp only [returnWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (x-9).toNat + 17 ≤ (x+d).toNat
      bv_omega
    · left
      change (x+d).toNat + 8 ≤ (x+104).toNat
      bv_omega
  have back := (saved 88 (by decide) (by decide)).trans ret
  have retLow : (0x10519d : BitVec 64).toNat < 2^32 := by decide
  have stackN := stack.of_frame scratch
  have stackM : Writable Extracted.programImage marked (x-9) 146 := stackN.memStore _ _
  have stackR := stack.of_frame resultFrame
  have lastCode : ∀ p ∈ codeRange 0x10a10f bytes_l10a10f, p ∈ Extracted.programImage :=
    fun p hp => Common.fnCode_subset_programImage p (code_l10a10f p hp)
  have markEq : memStore n (x+7) (1 : BitVec 8) = marked := rfl
  have zf : (!(testFlags (1 : BitVec 8)).ZF.getD false) = true := rfl
  have r14 : c[14].get 64 = v[0] := congrArg (Value.get 64) c14
  have r15 : c[15].get 64 = v[1] := congrArg (Value.get 64) c15
  have r12 : c[12].get 64 = v[2] := congrArg (Value.get 64) c12
  have r13 : c[13].get 64 = v[3] := congrArg (Value.get 64) c13
  have storedEq : memStore (memStore (memStore (memStore marked (x+104) v[0])
      (x+112) v[1]) (x+120) v[2]) (x+128) v[3] = stored := by
    simp only [stored, BitVec.add_assoc]
    rfl
  have resultEq : memStore stored (x+136) (1 : BitVec 8) = result := rfl
  have finish (o) (step :
      program.runBlock (dialect Extracted.programImage) ⟨.l10a10f,c,n⟩ = .returned o) :
      program.Exec (dialect Extracted.programImage) ⟨⟨.l10a0f2,b,m⟩,[]⟩ o :=
    Program.Exec.of_sem (reach.exec (Program.Exec.sem
      (.done (by simp only [Program.step, step, Transfer.next]))))
  refine ⟨?out, finish _ ?run, ?tag, ?stackOut, ?kept, ?restored, ?copied, ?flagOut, ?frame⟩
  case run =>
    cfg_eval [spBits, dstBits, byte, markEq, mark, zf, r14, r15, r12, r13]
    simp only [storedEq, resultEq, back, retLow, and_true]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using lastCode)
    rfl
  case tag => rfl
  case stackOut => rfl
  case kept =>
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact (keep 5 (by decide)).trans a5
    · exact (keep 22 (by decide)).trans a22
    · exact (keep 39 (by decide)).trans a39
    · exact (keep 50 (by decide)).trans a50
    · exact (keep 51 (by decide)).trans a51
  case restored =>
    intro ⟨i,_⟩ d hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact congrArg (Value.mk 64) (saved 48 (by decide) (by decide))
    · exact congrArg (Value.mk 64) (saved 56 (by decide) (by decide))
    · exact congrArg (Value.mk 64) (saved 64 (by decide) (by decide))
    · exact congrArg (Value.mk 64) (saved 72 (by decide) (by decide))
    · exact congrArg (Value.mk 64) (saved 80 (by decide) (by decide))
  case copied =>
    have h := Serializer.storeWords_wordsAt marked (x+104) v dstLow
    apply h.write_apart _ _
    intro i hi j hj
    change i < 1 at hi
    change j < 32 at hj
    bv_omega
  case flagOut => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case frame => exact resultFrame

end K256.Proofs.Verify.Core.Scalars.Inverse.Adapter
