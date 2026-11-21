import K256.Proofs.Sec1.Affine.Compressed.Tail.Stages
import K256.Proofs.Sec1.Affine.Compressed.Choice
import K256.Proofs.Sec1.Affine.Compressed.NormalizationCall
import K256.Proofs.Sec1.Affine.Compressed.PrepareParity
import K256.Proofs.Sec1.Affine.Compressed.SqrtEntry
import K256.Proofs.Sec1.Affine.Uncompressed.Choice

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field Serialize.Coordinates

private theorem load_spill_apart (mem : Ram) (sp dst src v : Word) (n : Nat)
    (apart : 8 ≤ (src - dst).toNat ∧ n / 8 ≤ (dst - src).toNat) :
    memLoad (memStore mem (sp + dst) v) (sp + src) n = memLoad mem (sp + src) n :=
  memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl apart)

private theorem negationStack_loads (mem : Ram) (sp : Word) (a : Limbs) :
    memLoad (negationStack mem sp a) (sp + 8) 64 = (negated a)[2] ∧
    memLoad (negationStack mem sp a) (sp + 16) 64 = (negated a)[4] ∧
    memLoad (negationStack mem sp a) (sp + 40) 64 = (negated a)[1] ∧
    memLoad (negationStack mem sp a) (sp + 96) 64 = (negated a)[0] ∧
    memLoad (negationStack mem sp a) (sp + 108) 8 = memLoad mem (sp + 108) 8 ∧
    memLoad (negationStack mem sp a) (sp + 32) 8 = memLoad mem (sp + 32) 8 := by
  simp (disch := decide +kernel) only [negationStack, addr_sub sp 8, load_spill_apart,
    memLoad_memStore_same, true_and]

private theorem normalizationInput_flag (mem : Ram) (sp : Word) (a : Limbs) :
    memLoad (normalizationInput mem sp a) (sp + 32) 8 = memLoad mem (sp + 32) 8 := by
  simp (disch := decide +kernel) only [normalizationInput, addr_sub sp 8, load_spill_apart]

private theorem reg8_of_word (v : BitVec 8) :
    ((Value.mk 64 (v.setWidth 64)).get 64).setWidth 8 = v := by
  rw [Value.get_mk, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]

set_option maxHeartbeats 500000 in
theorem chooseRootCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    {fr : Activation} {args : Values Value Reg.count} {mem : Ram} {xs : Limbs}
    {xOK ok : Bool} {want : BitVec 8} (body : BodyAt code fr args mem xs xOK want)
    {a : Limbs} (words : WordsAt mem (workSP fr+224) 64 a)
    (flag : memLoad mem (workSP fr+32) 8 = BitVec.ofNat 8 ok.toNat) :
    ∃ before b next m,
      (program.sem (dialect code)).Reaches ⟨⟨.l120d83,args,mem⟩,[]⟩ ⟨⟨.l120e17,before,b⟩,[]⟩ ∧
      program.runBlock (dialect code) ⟨.l120e17,before,b⟩ =
        .call ⟨.l114930,next,m⟩ (callFrame .l120e9b 0x120e9b) ∧
      NormalizeAt code args next mem m (workSP fr) 0x120e9b 264 392 (selectRoot a want) ok := by
  let sp := workSP fr
  let neg := negationStack mem sp a
  have atoms := body.atoms
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, _, _, _, _, _, _, _, _, _, _, _, read, _, _, stack, room, _, _⟩ := atoms
  have hr := read.low
  have sub (n : Nat) (hn : n ≤ 121) : (sp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - (488 + n) := by
    rw [show sp - BitVec.ofNat 64 n = fr.rsp - BitVec.ofNat 64 (488 + n) by
      simp only [sp, workSP, BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact stackOffset (by omega) _ (by omega)
  have spN : sp.toNat = fr.rsp.toNat - 488 := stackOffset (by omega) 488 (by decide)
  have add (n : Nat) (hn : n ≤ 432) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have startN : (fr.rsp - 1048).toNat = fr.rsp.toNat - 1048 :=
    stackOffset (by omega) 1048 (by decide)
  have below8 : (sp - 8).toNat = fr.rsp.toNat - 496 := sub 8 (by decide)
  have below9 : (sp - 9).toNat = fr.rsp.toNat - 497 := sub 9 (by decide)
  have below121 : (sp - 121).toNat = fr.rsp.toNat - 609 := sub 121 (by decide)
  have h9 : Writable code mem (sp-9) 9 := stack.sub (by omega) (by omega)
  have localWritable : Writable code mem (sp-8) 312 := stack.sub (by omega) (by omega)
  have pushIn : InRegions (selectWrites sp) (sp-8) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (sp-121).toNat ≤ (sp-8).toNat ∧ (sp-8).toNat + 8 ≤ (sp-121).toNat + 121 ∧ _
    omega
  have spillIn {n start size : Nat} (hs : start ≤ 432) (hn : n ≤ 432)
      (within : start ≤ n ∧ n+8 ≤ start+size) (region : ⟨(sp + BitVec.ofNat 64 start).toNat,size⟩ ∈ selectWrites sp) :
      InRegions (selectWrites sp) (sp + BitVec.ofNat 64 n) 8 := by
    refine ⟨_, region, ?_⟩
    unfold InRegion
    simp only [add _ hs, add _ hn]
    omega
  have spill8 : ⟨(sp+8).toNat,16⟩ ∈ selectWrites sp := by simp [selectWrites]
  have spill32 : ⟨(sp+32).toNat,16⟩ ∈ selectWrites sp := by simp [selectWrites]
  have spill96 : ⟨(sp+96).toNat,8⟩ ∈ selectWrites sp := by simp [selectWrites]
  have spill184 : ⟨(sp+184).toNat,248⟩ ∈ selectWrites sp := by simp [selectWrites]
  have negFrame : RamWriteFrame mem neg (selectWrites sp) := by
    dsimp only [neg, negationStack]
    refine (((((RamWriteFrame.refl _ _).memStore _ ?_).memStore _ ?_).memStore _ ?_).memStore _ ?_).memStore _ pushIn
    · exact spillIn (n := 96) (by decide) (by decide) (by decide) spill96
    · exact spillIn (n := 40) (by decide) (by decide) (by decide) spill32
    · exact spillIn (n := 8) (by decide) (by decide) (by decide) spill8
    · exact spillIn (n := 16) (by decide) (by decide) (by decide) spill8
  have retNeg : memLoad neg (sp-8) 64 = 0x120dff :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have w9 := h9.of_frame negFrame
  have rspGet : args[4].get 64 = sp := (congrArg (Value.get 64) rsp).trans (Value.get_mk 64 sp)
  obtain ⟨prep, prepCall, prepSP, prepX, prep14, prep15, prep12, prep13, prep5, prep3,
    prep22, prep39, prep50, prep51⟩ := prepareParity code args mem sp a
      rspGet (localWritable.sub (Nat.le_refl _) (by omega)) words
      (fun e he => cover e (code_l120d83 e he))
  obtain ⟨first, m₁, reach₁, sp₁, ax₁, frame₁, keep₁⟩ :=
    Uncompressed.resumeChoice cover prepCall (by rw [prepSP, Value.get_mk]) w9 retNeg (by decide)
  have loadParity : LoadOk m₁ (sp+108) 1 := by
    have hw := (localWritable.of_frame negFrame).of_frame frame₁
    exact LoadOk.of_offsets hw.readable rfl (addr_sub sp 8) (by decide)
  obtain ⟨second, m₂, reach₂, ax₂, sp₂, frame₂, keep₂⟩ :=
    ChoiceSite.pass .xorParity code first m₁ sp cover (by rw [sp₁, Value.get_mk]) (w9.of_frame frame₁)
      (fun _ => loadParity)
  obtain ⟨third, m₃, reach₃, ax₃, sp₃, frame₃, keep₃⟩ :=
    ChoiceSite.pass .equalParity code second m₂ sp cover (by rw [sp₂, Value.get_mk])
      ((w9.of_frame frame₁).of_frame frame₂) (by intro h; cases h)
  have stackWithin {n : Nat} (hn : n ≤ 9) :
      RegionsWithin [⟨(sp-9).toNat,n⟩] [⟨(sp-9).toNat,9⟩] := by
    intro r h
    rcases List.mem_singleton.mp h with rfl
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left hn _⟩
  have passFrame : RamWriteFrame neg m₃ [⟨(sp-9).toNat,9⟩] := by
    have initial := RamWriteFrame.refl neg [⟨(sp-9).toNat,9⟩]
    exact ((initial.trans frame₁ (stackWithin (n := 1) (by decide))).trans
      frame₂ (stackWithin (n := 9) (by decide))).trans frame₃ (stackWithin (n := 9) (by decide))
  have load_unchanged {m' : Ram} {n : Nat}
      (hf : RamWriteFrame neg m' [⟨(sp-9).toNat,n⟩]) (hn : n ≤ 9)
      (off bits : Nat) (ho : off ≤ 432) (hb : bits / 8 ≤ 8) :
      memLoad m' (sp+BitVec.ofNat 64 off) bits = memLoad neg (sp+BitVec.ofNat 64 off) bits := by
    apply hf.memLoad_eq
    refine ⟨?_, fun r h => ?_⟩
    · rw [add off ho]
      omega
    · rcases List.mem_singleton.mp h with rfl
      right
      change (sp-9).toNat+n ≤ (sp+BitVec.ofNat 64 off).toNat
      rw [add off ho]
      omega
  obtain ⟨neg8, neg16, neg40, neg96, neg108, neg32⟩ := negationStack_loads mem sp a
  have want₁ : memLoad m₁ (sp + 108) 8 = want := (load_unchanged frame₁ (by decide) 108 8 (by decide) (by decide)).trans
    (neg108.trans body.parity)
  have mask : -((third[0].get 64).setWidth 8).setWidth 64 = parityMask a[0] want := by
    rw [ax₃, reg8_of_word]
    change -((~~~((second[0].get 64).setWidth 8)) &&& 1).setWidth 64 = _
    rw [ax₂, reg8_of_word]
    change -((~~~(((first[0].get 64).setWidth 8) ^^^ memLoad m₁ (sp + 108) 8)) &&& 1).setWidth 64 = _
    rw [want₁, ax₁, reg8_of_word, prepX,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
    rfl
  have keep (i : Fin 53) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) : third[i] = prep[i] := by
    refine (keep₃ i hi).trans ((keep₂ i hi).trans (keep₁ i ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with h|h|h|h|h|h|h|h|h|h <;> simp [h]
  have reg (i : Fin 53) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) (v : Word)
      (h : prep[i] = ⟨64,v⟩) : third[i].get 64 = v := by
    rw [keep i hi, h, Value.get_mk]
  have load₃ (off bits : Nat) (ho : off ≤ 432) (hb : bits / 8 ≤ 8) :=
    load_unchanged passFrame (by decide) off bits ho hb
  have w₃ := (localWritable.of_frame negFrame).of_frame passFrame
  obtain ⟨next, nextCall, nextSP, nextSI, nextDI, next22, next39, next50, next51, next3, nextWide⟩ :=
    normalizationCall code third m₃ a want sp (fun e he => cover e (code_l120e17 e he))
      (by rw [sp₃, Value.get_mk]) mask
      (reg 14 (by decide) _ prep14) ((load₃ 96 64 (by decide) (by decide)).trans neg96)
      (reg 15 (by decide) _ prep15) ((load₃ 40 64 (by decide) (by decide)).trans neg40)
      (reg 12 (by decide) _ prep12) ((load₃ 8 64 (by decide) (by decide)).trans neg8)
      (reg 13 (by decide) _ prep13) (reg 3 (by decide) _ prep3)
      (reg 5 (by decide) _ prep5) ((load₃ 16 64 (by decide) (by decide)).trans neg16) w₃
  let chosen := selectRoot a want
  let m := normalizationInput m₃ sp chosen
  refine ⟨third, m₃, next, m, (reach₁.trans reach₂).trans reach₃, nextCall,
    ⟨nextSP, nextSI, nextDI, ?_, ?_, ?_, normalizationInput_words _ _ _,
      (normalizationInput_flag _ _ _).trans ((load₃ 32 8 (by decide) (by decide)).trans (neg32.trans flag)), ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h
    · have eq : i = 3 := Fin.ext h
      subst i
      change next[(3 : Nat)] = ⟨64, next[(3 : Nat)].get 64⟩
      have val : next[(3 : Nat)] = ⟨64, (negated a)[3]⟩ :=
        next3.trans ((keep 3 (by decide)).trans prep3)
      rw [val, Value.get_mk]
    · apply nextWide
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  · intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact next22.trans ((keep 22 (by decide)).trans prep22)
    · exact next39.trans ((keep 39 (by decide)).trans prep39)
    · exact next50.trans ((keep 50 (by decide)).trans prep50)
    · exact next51.trans ((keep 51 (by decide)).trans prep51)
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · have frame := negFrame.trans passFrame (by
      intro r h
      rcases List.mem_singleton.mp h with rfl
      refine ⟨_, List.mem_cons_self, ?_⟩
      change (sp-121).toNat ≤ (sp-9).toNat ∧ (sp-9).toNat + 9 ≤ (sp-121).toNat + 121
      omega)
    have selectedIn (n : Nat) (hn : 184 ≤ n ∧ n ≤ 424) :
        InRegions (selectWrites sp) (sp+BitVec.ofNat 64 n) 8 :=
      spillIn (start := 184) (size := 248) (by decide) (by omega) (by omega) spill184
    dsimp only [m, normalizationInput]
    exact frame
      |>.memStore _ (selectedIn 264 (by decide))
      |>.memStore _ (selectedIn 272 (by decide))
      |>.memStore _ (selectedIn 280 (by decide))
      |>.memStore _ (selectedIn 288 (by decide))
      |>.memStore _ (selectedIn 296 (by decide))
      |>.memStore _ pushIn

end K256.Proofs.Sec1.Affine.Compressed
