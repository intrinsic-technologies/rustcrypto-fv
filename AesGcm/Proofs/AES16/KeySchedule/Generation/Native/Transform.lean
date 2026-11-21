import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Evaluation
import AesGcm.Proofs.AES16.KeySchedule.Generation.Words
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Memory

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

attribute [local irreducible] memLoad memStore

def notsMemory (mem : Ram) (a : BitVec 64) : Ram :=
  let m0 := memStore mem (wordAddr a 16 0) (~~~(memLoad mem (wordAddr a 16 0) 16))
  let m1 := memStore m0 (wordAddr a 16 1) (~~~(memLoad m0 (wordAddr a 16 1) 16))
  let m2 := memStore m1 (wordAddr a 16 5) (~~~(memLoad m1 (wordAddr a 16 5) 16))
  memStore m2 (wordAddr a 16 6) (~~~(memLoad m2 (wordAddr a 16 6) 16))

def transformMemory (use256 : Bool) (round : Nat) (mem : Ram) (sp : BitVec 64) : Ram :=
  let a := base use256 sp + BitVec.ofNat 64 (16 * round)
  let m := notsMemory mem a
  if (4 * round) % (variant use256).Nk = 0 then
    rconStores m a ⟨((4 * round) / (variant use256).Nk - 1) % 10, Nat.mod_lt _ (by decide)⟩
  else m

set_option maxHeartbeats 1000000 in
theorem transformMemory_words (use256 : Bool) (round : Nat)
    (hr : (variant use256).Nk / 4 ≤ round) (hrLast : round ≤ (variant use256).Nr)
    (mem : Ram) (sp : BitVec 64) (code : CodeMap)
    (hmemory : MemoryReady use256 code mem sp) (x : Fixslice16.Planes16)
    (hwords : WordsAt mem (base use256 sp + BitVec.ofNat 64 (16 * round))
      16 (Vector.ofFn x)) :
    WordsAt (transformMemory use256 round mem sp)
      (base use256 sp + BitVec.ofNat 64 (16 * round)) 16
      (Vector.ofFn (substitutedRound use256 round x)) := by
  have hn : WordsAt (notsMemory mem (base use256 sp + BitVec.ofNat 64 (16 * round)))
      (base use256 sp + BitVec.ofNat 64 (16 * round)) 16
      (Vector.ofFn (Fixslice16.subBytesNots x)) := by
    apply subBytesNots_store_words mem _ x hwords
    have hl := stack_limit hmemory
    rw [address_toNat hmemory (16 * round) (by
      have := Native.round_bound use256 round hrLast; omega)]
    cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have hq : 1 ≤ 4 * round / (variant use256).Nk ∧
      4 * round / (variant use256).Nk ≤ 10 := by
    cases use256 <;> simp only [variant, Variant.Nk, Variant.Nr, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  unfold transformMemory substitutedRound
  split
  next he =>
    have hm : ((4 * round / (variant use256).Nk - 1) % 10) + 1 =
        4 * round / (variant use256).Nk := by omega
    have hw := rcon_words
      (notsMemory mem (base use256 sp + BitVec.ofNat 64 (16 * round)))
      (base use256 sp + BitVec.ofNat 64 (16 * round)) (Fixslice16.subBytesNots x)
      ⟨((4 * round) / (variant use256).Nk - 1) % 10, Nat.mod_lt _ (by decide)⟩ hn
    rw [hm] at hw
    have he' : Nat.mod (4 * round) (variant use256).Nk = 0 := he
    have hd : Nat.div (4 * round) (variant use256).Nk =
        (4 * round) / (variant use256).Nk := rfl
    simp only [he', ite_true, hd]
    exact hw
  next he =>
    have he' : ¬Nat.mod (4 * round) (variant use256).Nk = 0 := he
    simp only [he', ite_false, UInt8.toBitVec_zero, BitVec.getLsbD_zero,
      Bool.false_eq_true, ite_false]
    have hv : (Vector.ofFn fun p ↦ Fixslice16.subBytesNots x p ^^^ (0 : BitVec 16)) =
        Vector.ofFn (Fixslice16.subBytesNots x) := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      exact BitVec.xor_zero
    rw [hv]
    exact hn

theorem round_store_inside {use256 : Bool} {round : Nat} {mem : Ram}
    {sp : BitVec 64} {code : CodeMap} (hmemory : MemoryReady use256 code mem sp)
    (hrLast : round ≤ (variant use256).Nr) (off len : Nat) (hoff : off + len ≤ 16) :
    InRegions (roundRegions use256 sp round)
      ((base use256 sp + BitVec.ofNat 64 (16 * round)) + BitVec.ofNat 64 off) len := by
  have hb := Native.round_bound use256 round hrLast
  have ha := address_toNat hmemory (16 * round + off) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ha
  refine ⟨span (base use256 sp + BitVec.ofNat 64 (16 * round)) 16,
    List.Mem.tail _ (List.Mem.head _), ?_, ?_, ?_⟩
  · simp only [span, ha, address_toNat hmemory (16 * round) (by omega)]
    omega
  · simp only [span, ha, address_toNat hmemory (16 * round) (by omega)]
    omega
  · rw [ha]
    have hl := stack_limit hmemory
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem notsMemory_frame {use256 : Bool} {round : Nat} {mem : Ram}
    {sp : BitVec 64} {code : CodeMap} (hmemory : MemoryReady use256 code mem sp)
    (hrLast : round ≤ (variant use256).Nr) :
    RamWriteFrame mem
      (notsMemory mem (base use256 sp + BitVec.ofNat 64 (16 * round)))
      (roundRegions use256 sp round) := by
  unfold notsMemory
  apply RamWriteFrame.memStore
  · apply RamWriteFrame.memStore
    · apply RamWriteFrame.memStore
      · apply RamWriteFrame.memStore
        · exact RamWriteFrame.refl _ _
        · exact round_store_inside hmemory hrLast 0 2 (by decide)
      · exact round_store_inside hmemory hrLast 2 2 (by decide)
    · exact round_store_inside hmemory hrLast 10 2 (by decide)
  · exact round_store_inside hmemory hrLast 12 2 (by decide)

theorem rconStore_frame {use256 : Bool} {round : Nat} {mem prior : Ram}
    {sp : BitVec 64} {code : CodeMap} (hmemory : MemoryReady use256 code prior sp)
    (hrLast : round ≤ (variant use256).Nr) (i : Nat) (hi : i < 8)
    (hf : RamWriteFrame prior mem (roundRegions use256 sp round)) :
    RamWriteFrame prior
      (rconStore mem (base use256 sp + BitVec.ofNat 64 (16 * round)) i)
      (roundRegions use256 sp round) := by
  exact hf.memStore _ (round_store_inside hmemory hrLast (2 * i) 1 (by omega))

theorem transformMemory_frame {use256 : Bool} {round : Nat} {mem : Ram}
    {sp : BitVec 64} {code : CodeMap} (hmemory : MemoryReady use256 code mem sp)
    (hrLast : round ≤ (variant use256).Nr) :
    RamWriteFrame mem (transformMemory use256 round mem sp)
      (roundRegions use256 sp round) := by
  have hn := notsMemory_frame hmemory hrLast
  unfold transformMemory
  split
  · unfold rconStores
    split
    next h => exact rconStore_frame hmemory hrLast _ h hn
    next h =>
      have hk := Nat.mod_lt (4 * round / (variant use256).Nk - 1) (by decide : 0 < 10)
      exact rconStore_frame hmemory hrLast _ (by omega)
        (rconStore_frame hmemory hrLast _ (by omega)
          (rconStore_frame hmemory hrLast _ (by omega)
            (rconStore_frame hmemory hrLast _ (by omega) hn)))
  · exact hn

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1800000 in
theorem transform_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (round : Nat) (hr : (variant use256).Nk / 4 ≤ round)
    (hrLast : round ≤ (variant use256).Nr)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hready : Ready use256 round sp args)
    (hmemory : MemoryReady use256 code mem sp)
    (x : Fixslice16.Planes16)
    (hwords : WordsAt mem (base use256 sp + BitVec.ofNat 64 (16 * round))
      16 (Vector.ofFn x)) :
    ∃ (nextArgs : Values Value Reg.count) (nextMem : Ram),
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨notLabel use256 (oddRound round), args, mem⟩, []⟩
        ⟨⟨.l104010, nextArgs,
            memStore nextMem (sp - 8) (afterReturn use256 (oddRound round))⟩,
          [callFrame (afterLabel use256 (oddRound round))
            (afterReturn use256 (oddRound round))]⟩ ∧
      nextArgs[4] = ⟨64, sp - 8⟩ ∧
      nextArgs[7] = ⟨64, base use256 sp⟩ ∧
      nextArgs[6] = ⟨64, if use256 then 120 else 88⟩ ∧
      nextArgs[2] = ⟨64, BitVec.ofNat 64 (8 * round)⟩ ∧
      nextArgs[15] = ⟨64, BitVec.ofNat 64 (8 * round)⟩ ∧
      nextArgs[1] = ⟨64, if use256 then 16 else 8⟩ ∧
      nextArgs[8] = ⟨64, if use256 && oddRound round then 3 else 7⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs ∧
      RamWriteFrame mem nextMem (roundRegions use256 sp round) ∧
      WordsAt nextMem (base use256 sp + BitVec.ofNat 64 (16 * round))
        16 (Vector.ofFn (substitutedRound use256 round x)) := by
  have hsp := hready.hsp
  have hindex := hready.hindex
  have hbuffer := hready.hbuffer
  have hTypes := hready.hTypes
  have hcontrol := hready.hcontrol
  have hstack := hmemory.hstack
  have hstackRead := hstack.readable
  have hwordsFinal := transformMemory_words use256 round hr hrLast mem sp code hmemory x hwords
  have hframeFinal := transformMemory_frame hmemory hrLast
  cases use256
  · change 1 ≤ round at hr
    change round ≤ 10 at hrLast
    have hrounds : round = 1 ∨ round = 2 ∨ round = 3 ∨ round = 4 ∨ round = 5 ∨ round = 6 ∨
      round = 7 ∨ round = 8 ∨ round = 9 ∨ round = 10 := by omega
    rcases hrounds with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (
      change args[5].get 64 = _ ∧ args[12].get 64 = _ ∧ args[13].get 64 = _ at hcontrol
      have h5 := hcontrol.1
      have h12 := hcontrol.2.1
      have h13 := hcontrol.2.2
      change Writable code mem (sp - 248) 512 at hstack
      change Readable mem (sp - 248) 512 at hstackRead
      refine ⟨?_, transformMemory false _ mem sp, ?execution, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hframeFinal, hwordsFinal⟩
      case execution =>
        apply Star.step
        · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
              (h : Writable code m a n) : RangeApart a n 0x104446 34 := by
            exact (storeOk_of_codeRange h
              (fun x hx ↦ hcode x (LIR.code_l104446 x hx))).apart
          change LIR.program.step (dialect code) ⟨⟨.l104446, args, mem⟩, []⟩ = Outcome.next _
          cfg_eval [base, hsp, hindex, hbuffer, h5, h12, h13]
          refine_norm [base, hsp, hindex, hbuffer, h5, h12, h13]
          runtime_guards next
          rfl
        apply Star.step
        · first
          | (have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
                 (h : Writable code m a n) : RangeApart a n 0x104468 7 := by
               exact (storeOk_of_codeRange h
                 (fun x hx ↦ hcode x (LIR.code_l104468 x hx))).apart
             change LIR.program.step (dialect code) ⟨⟨.l104468, _, _⟩, []⟩ = Outcome.next _
             cfg_eval [base, hsp, hindex, hbuffer, h5, h12, h13]
             refine_norm [base, hsp, hindex, hbuffer, h5, h12, h13]
             runtime_guards next
             rfl)
          | (have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
                 (h : Writable code m a n) : RangeApart a n 0x1043e0 20 := by
               exact (storeOk_of_codeRange h
                 (fun x hx ↦ hcode x (LIR.code_l1043e0 x hx))).apart
             change LIR.program.step (dialect code) ⟨⟨.l1043e0, _, _⟩, []⟩ = Outcome.next _
             cfg_eval [base, hsp, hindex, hbuffer, h5, h12, h13]
             refine_norm [base, hsp, hindex, hbuffer, h5, h12, h13]
             runtime_guards next
             rfl)
        apply Semantics.Reaches.single
        have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
            (h : Writable code m a n) : RangeApart a n 0x1043f4 31 := by
          exact (storeOk_of_codeRange h
            (fun x hx ↦ hcode x (LIR.code_l1043f4 x hx))).apart
        change LIR.program.step (dialect code) ⟨⟨.l1043f4, _, _⟩, []⟩ = Outcome.next _
        cfg_eval [base, hsp, hindex, hbuffer, h5, h12, h13]
        refine_norm [base, hsp, hindex, hbuffer, h5, h12, h13]
        runtime_guards next
        simp only [afterLabel, afterReturn, oddRound, transformMemory, notsMemory, base,
          variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte, Nat.reduceMul,
          Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT, wordAddr,
          rconStores, rconStore, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        rfl
      all_goals first
        | rfl
        | runtime_typed
        | (rintro ⟨r, hr⟩ hin
           simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
           rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hsp, hindex, hbuffer, h5, h12, h13, base])
  · change 2 ≤ round at hr
    change round ≤ 14 at hrLast
    have hrounds : round = 2 ∨ round = 3 ∨ round = 4 ∨ round = 5 ∨ round = 6 ∨
      round = 7 ∨ round = 8 ∨ round = 9 ∨ round = 10 ∨ round = 11 ∨
      round = 12 ∨ round = 13 ∨ round = 14 := by omega
    rcases hrounds with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (
      change args[3].get 64 = _ ∧ args[12].get 64 = _ ∧ args[13].get 64 = _ at hcontrol
      have h3 := hcontrol.1
      have h12 := hcontrol.2.1
      have h13 := hcontrol.2.2
      change Writable code mem (sp - 248) 608 at hstack
      change Readable mem (sp - 248) 608 at hstackRead
      refine ⟨?_, transformMemory true _ mem sp, ?execution, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hframeFinal, hwordsFinal⟩
      case execution =>
        first
        | (apply Semantics.Reaches.single
           have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
               (h : Writable code m a n) : RangeApart a n 0x105892 57 := by
             exact (storeOk_of_codeRange h
               (fun x hx ↦ hcode x (LIR.code_l105892 x hx))).apart
           change LIR.program.step (dialect code) ⟨⟨.l105892, args, mem⟩, []⟩ = Outcome.next _
           cfg_eval [base, hsp, hindex, hbuffer, h3, h12, h13]
           refine_norm [base, hsp, hindex, hbuffer, h3, h12, h13]
           runtime_guards next
           simp only [afterLabel, afterReturn, oddRound, transformMemory, notsMemory, base,
             variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte, Nat.reduceMul,
             Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT, wordAddr,
             rconStores, rconStore, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
           rfl)
        | (apply Semantics.Reaches.single
           have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
               (h : Writable code m a n) : RangeApart a n 0x1058f6 51 := by
             exact (storeOk_of_codeRange h
               (fun x hx ↦ hcode x (LIR.code_l1058f6 x hx))).apart
           change LIR.program.step (dialect code) ⟨⟨.l1058f6, args, mem⟩, []⟩ = Outcome.next _
           cfg_eval [base, hsp, hindex, hbuffer, h3, h12, h13]
           refine_norm [base, hsp, hindex, hbuffer, h3, h12, h13]
           runtime_guards next
           simp only [afterLabel, afterReturn, oddRound, transformMemory, notsMemory, base,
             variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte, Nat.reduceMul,
             Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT, wordAddr,
             rconStores, rconStore, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
           rfl)
      all_goals first
        | rfl
        | runtime_typed
        | (rintro ⟨r, hr⟩ hin
           simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
           rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hsp, hindex, hbuffer, h3, h12, h13, base])

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
