import K256.Proofs.Signing.Composition.Wrapper.Frame
import K256.Proofs.Signing.Generator
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.Transfer.Generator
import K256.Proofs.Signing.LIR.SigningKeyTrySign
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Image
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Composition.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

private def generatorInput (m : Ram) (p : BitVec 64) (d : Nat) : Ram :=
  memStore (memStore (memStore (memStore (memStore m
    (p+24) (scalarWords d)[3]) (p+16) (scalarWords d)[2])
    (p+8) (scalarWords d)[1]) p (scalarWords d)[0]) (p-8) (0x102696 : BitVec 64)

set_option maxRecDepth 3000 in
private theorem generatorBlock {a : Registers} {m : Ram} {p : BitVec 64} {d : Nat}
    (rsp : a[4] = ⟨64,p⟩)
    (stack : Writable Extracted.programImage m (p-8) 80)
    (key : WordsAt m (p+40) 64 (scalarWords d))
    (incoming : ∀ i : Fin Reg.count, i.val ∈ [2,8,9] → a[i].width = 64) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l10265c,a,m⟩ =
      .call ⟨.l10ee80,b,generatorInput m p d⟩ (resume .l102696 0x102696) ∧
      (b[4] = ⟨64,p-8⟩ ∧ b[6] = ⟨64,p⟩ ∧ b[7] = ⟨64,p+200⟩ ∧ b[12] = ⟨64,p+200⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → b[i].width = 64) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have spVal : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have l0 : memLoad m (p+40) 64 = (scalarWords d)[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd] using key 0 (by decide)
  have l1 : memLoad m (p+48) 64 = (scalarWords d)[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd] using key 1 (by decide)
  have l2 : memLoad m (p+56) 64 = (scalarWords d)[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd] using key 2 (by decide)
  have l3 : memLoad m (p+64) 64 = (scalarWords d)[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd] using key 3 (by decide)
  refine ⟨?_, ?run, ?post, ?widths, ?saved⟩
  case run =>
    cfg_eval [spVal]
    segment_words []
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using LIR.code_l10265c)
    simp only [l0,l1,l2,l3] <;> rfl
  case post => exact ⟨rfl,rfl,rfl,rfl⟩
  case widths =>
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact incoming 2 (by decide)
    · exact incoming 8 (by decide)
    · exact incoming 9 (by decide)
  case saved =>
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem valueWidth (v : Value) {w : Nat} (h : v.width = w) :
    v = ⟨w, v.get w⟩ := by
  cases v
  subst w
  rw [Value.get_mk]

set_option maxRecDepth 3000 in
theorem multiply {s : RamState} {secret msg : ByteArray} {d : Nat} {a m}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d) (entry : DecodeResult s d a m) :
    ∃ b n, Reach (atBlock .l10265c a m) (atBlock .l102696 b n) ∧ Multiplied s d b n := by
  let p := localSp s
  let n := generatorInput m p d
  obtain ⟨room, limit, _⟩ := stackBounds call
  have pAddr : p = stackPtr s - 472 := localSp_eq s
  have pn : p.toNat = (stackPtr s).toNat - 472 := by
    rw [pAddr]
    exact Common.stackOffset (off := 472) call.stackAvailable (by decide)
  have retNat : (p-8).toNat = p.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ p.toNat; omega)
  have lowNat : (p-8-9768).toNat = p.toNat - 8 - 9768 :=
    by rw [BitVec.toNat_sub_of_le (show 9768 ≤ p-8 by change 9768 ≤ (p-8).toNat; omega),
      retNat] <;> rfl
  have addr (i : Nat) (hi : i ≤ 472) :
      (p+BitVec.ofNat 64 i).toNat = p.toNat+i := by
    have iNat : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [iNat]; omega), iNat]
  let base := stackPtr s - 11192
  have baseNat : base.toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have baseWrite : Writable Extracted.programImage m base 11200 := entry.toMemory.window call
  have stack : Writable Extracted.programImage m (p-8) 80 :=
    baseWrite.sub (by change base.toNat ≤ (p-8).toNat; omega)
      (by change (p-8).toNat + 80 ≤ base.toNat + 11200; omega)
  obtain ⟨b,push,⟨bsp,bsi,bdi,b12⟩,widths,keep⟩ := generatorBlock entry.rsp stack entry.key entry.volatileWidths
  let setupRegions : List MemoryRegion := [⟨(p-8).toNat,40⟩]
  have slot {q : BitVec 64} (lo : (p-8).toNat ≤ q.toNat) (hi : q.toNat + 8 ≤ (p-8).toNat + 40) :
      InRegions setupRegions q 8 := ⟨_, List.mem_singleton_self _, lo, hi, by omega⟩
  have setup : RamWriteFrame m n setupRegions := by
    have at8 : (p+8).toNat = p.toNat + 8 := addr 8 (by decide)
    have at16 : (p+16).toNat = p.toNat + 16 := addr 16 (by decide)
    have at24 : (p+24).toNat = p.toNat + 24 := addr 24 (by decide)
    unfold n generatorInput
    apply RamWriteFrame.memStore _ _ (slot (by omega) (by omega))
    apply RamWriteFrame.memStore _ _ (slot (by omega) (by omega))
    apply RamWriteFrame.memStore _ _ (slot (by omega) (by omega))
    apply RamWriteFrame.memStore _ _ (slot (by omega) (by omega))
    exact (RamWriteFrame.refl m _).memStore _
      (slot (by omega) (by omega))
  have afterSetup : Memory s n := by
    apply preserveSlots call entry.toMemory setup
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (stackPtr s).toNat - 11192 ≤ (p-8).toNat ∧
      (p-8).toNat + 40 ≤ (stackPtr s).toNat - 32
    omega
  have image := afterSetup.image call
  let child : Activation :=
    { original := n, rsp := p-8, ret := 0x102696, low := p-8-9768,
      rcx := b[1].get 64, rdx := b[2].get 64, rbx := s.regValue .rdi, rbp := s.regValue .rbp,
      rsi := p, rdi := p+200, r8 := b[8].get 64, r9 := b[9].get 64, r12 := p+200,
      r13 := s.regValue .r13, r14 := s.regValue .rcx, r15 := s.regValue .rdx,
      mxcsr := a[39].get 32, ftw := a[50].get 16, fcw := a[51].get 16, fs := s.FS }
  have dstNat : child.rdi.toNat = p.toNat+200 := addr 200 (by decide)
  have childStack := baseWrite.of_frame setup
  have ro : Generate.LIR.rodataSection ∈ Extracted.programSections := by
    simp [Extracted.programSections, Generate.LIR.rodataSection]
  have slots := Generate.LIR.Fn10ee80.callSlots_loaded ro image
  obtain ⟨read1, val1⟩ := slots (0x203de0, 0x129770) (by decide)
  obtain ⟨read2, val2⟩ := slots (0x203e20, 0x100a20) (by decide)
  have avoids := (call.separation.2 (Stack.region s signingKeyTrySign.minStackBytes)
    (by simp [writtenRegions])).1
  rw [stackRegion call] at avoids
  have slotsApart := apart_of_avoids (lo := 0x203de0) (hi := 0x203e28) avoids
    (fun x hlo hhi => by
      obtain ⟨v,hv⟩ := Generate.LIR.Fn10ee80.callSlots_span ro x hlo hhi
      exact Or.inl ⟨v, Common.programSections_fetchByte_of_mem hv⟩)
    (by change 0 < 11200; decide) (by decide) (by decide)
  change base.toNat + 11200 ≤ 0x203de0 ∨ 0x203e28 ≤ base.toNat at slotsApart
  have align : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have atoms : Atom.All Extracted.programImage b n (Generate.LIR.Fn10ee80.frameAt .l10ee80 child) := by
    refine ⟨bsp, (keep 22 (by decide)).trans entry.df, valueWidth _ (widths 1 (by decide)),
      valueWidth _ (widths 2 (by decide)), (keep 3 (by decide)).trans entry.output,
      (keep 5 (by decide)).trans entry.rbp, bsi, bdi, valueWidth _ (widths 8 (by decide)),
      valueWidth _ (widths 9 (by decide)), b12, (keep 13 (by decide)).trans entry.r13,
      (keep 14 (by decide)).trans entry.length, (keep 15 (by decide)).trans entry.message,
      (keep 39 (by decide)).trans (valueWidth _ entry.fp.1),
      (keep 50 (by decide)).trans (valueWidth _ entry.fp.2.1),
      (keep 51 (by decide)).trans (valueWidth _ entry.fp.2.2),
      childStack.readable.sub (by change base.toNat ≤ (p-8).toNat; omega)
        (by change (p-8).toNat + 8 ≤ base.toNat + 11200; omega),
      memLoad_memStore_same _ _ _ (by decide) (by decide),
      by change (0x102696#64).toNat < 2^32; decide,
      childStack.sub (by change base.toNat ≤ (p-8-9768).toNat; omega)
        (by change (p-8-9768).toNat + 9768 ≤ base.toNat + 11200; omega),
      by change (p-8-9768).toNat + 9768 ≤ (p-8).toNat; omega,
      by change (p-8).toNat % 16 = 8; omega,
      read1, val1, read2, val2,
      by change 0x206450 ≤ (p-8).toNat ∨ (p-8).toNat ≤ 0x203de0; omega, trivial⟩
  have words : WordsAt n p 64 (scalarWords d) := by
    intro i hi
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
    all_goals simp (disch := store_disch) only [n, generatorInput, wordAddr, Nat.reduceDiv,
      Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, store_norm]
  have valid : 0 < d ∧ d < domain.n := by
    dsimp only [Keys.decodeSecret] at decoded
    split at decoded
    next good =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at good
      obtain rfl := Option.some.inj decoded
      exact ⟨good.1.2, good.2⟩
    next => contradiction
  obtain ⟨out,run,tag,done,_,written,point⟩ := Generator.execution atoms image
    (by change 9768 ≤ (p-8).toNat; omega) rfl
    (by change (p-8).toNat + 352 ≤ 2^32; omega)
    (by change p = p-8+8; bv_omega) (by change p+200 = p-8+208; bv_omega)
    (childStack.readable.sub (by change base.toNat ≤ p.toNat; omega)
      (by change p.toNat + 32 ≤ base.toNat + 11200; omega))
    (childStack.sub (by change base.toNat ≤ child.rdi.toNat; omega)
      (by change child.rdi.toNat + 120 ≤ base.toNat + 11200; omega)) words valid.1 valid.2
  have lifted := Transfer.verifyExec (src := .l10ee80) (dst := .l10ee80)
    (.tail _ (.head _)) (Transfer.generator (src := .l10ee80) (dst := .l10ee80) (.head _) run)
  have reached : Reach (atBlock .l10265c a m) (atBlock .l102696 out.values out.store) := by
    refine .step (b := ⟨⟨.l10ee80,b,n⟩,[resume .l102696 0x102696]⟩) ?_ ?_
    · change (LIR.program.runBlock (dialect Extracted.programImage) ⟨.l10265c,a,m⟩).next _ [] = _
      rw [push] <;> rfl
    · exact ParseSignature.exec_reaches_resume lifted (resume .l102696 0x102696) [] (by rw [tag]; rfl)
  have childLow : child.low.toNat = p.toNat - 8 - 9768 := lowNat
  have childRsp : child.rsp.toNat = p.toNat - 8 := retNat
  have memory : Memory s out.store := by
    apply preserveSlots call afterSetup written
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (stackPtr s).toNat - 11192 ≤ child.low.toNat ∧
        child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ (stackPtr s).toNat - 32
      omega
    · change (stackPtr s).toNat - 11192 ≤ child.rdi.toNat ∧
        child.rdi.toNat + 120 ≤ (stackPtr s).toNat - 32
      omega
  have restore {q : BitVec 64} (bounded : q.toNat + 8 ≤ 2^64)
      (setupEnd : p.toNat + 32 ≤ q.toNat) (destApart : q.toNat+8 ≤ p.toNat+200 ∨ p.toNat+320 ≤ q.toNat) :
      memLoad out.store q 64 = memLoad m q 64 := by
    rw [written.memLoad_eq ⟨bounded, ?_⟩, setup.memLoad_eq ⟨bounded, ?_⟩]
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inr (by change (p-8).toNat + 40 ≤ q.toNat; omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (by change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ q.toNat; omega)
      · change q.toNat + 8 ≤ child.rdi.toNat ∨ child.rdi.toNat + 120 ≤ q.toNat
        omega
  have key : WordsAt out.store (p+40) 64 (scalarWords d) := by
    intro i hi
    have eq : wordAddr (p+40) 64 i = p+BitVec.ofNat 64 (40+8*i) := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [eq, restore]
    · rw [← eq]
      exact entry.key i hi
    all_goals have q := addr (40+8*i) (by omega)
    · omega
    · omega
    · exact Or.inl (by omega)
  change Atom.All _ _ _ (Generate.LIR.Fn10ee80.doneAt child) at done
  obtain ⟨rsp,df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := done
  have pop : child.rsp + 8 = p := by change p-8+8 = p; bv_omega
  rw [pop] at rsp
  exact ⟨out.values,out.store,reached,
    ⟨⟨⟨rsp,bx,bp,r13,r15,r14,congrArg Value.width r12,df,
      ⟨congrArg Value.width mx,congrArg Value.width ft,congrArg Value.width fc⟩⟩,memory,key⟩,r12,point⟩⟩

end K256.Proofs.Signing.Composition.Wrapper
