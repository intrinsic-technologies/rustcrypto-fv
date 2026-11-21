import K256.Proofs.ParseSignature.Pair.Nonzero.Frame
import K256.Proofs.LIR.Fn103ac0
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private abbrev copySecondScalar (p : BitVec 64) (m : Ram) : Ram :=
  let m1 := memStore m (p + 152) (memLoad m (p + 32) 64)
  let m2 := memStore m1 (p + 160) (memLoad m1 (p + 40) 64)
  let m3 := memStore m2 (p + 136) (memLoad m (p + 16) 64)
  memStore m3 (p + 144) (memLoad m (p + 24) 64)

private abbrev clearCompareWords (p : BitVec 64) (m : Ram) : Ram :=
  let m := memStore m (p + 32) (0 : BitVec 64)
  let m := memStore m (p + 24) (0 : BitVec 64)
  let m := memStore m (p + 16) (0 : BitVec 64)
  memStore m (p + 8) (0 : BitVec 64)

private abbrev compareMemory (p : BitVec 64) (m : Ram) (second : Bool) : Ram :=
  memStore (clearCompareWords p (if second then m else copySecondScalar p m)) (p - 8)
    (if second then (0x103c3f : BitVec 64) else 0x103bf1)

private abbrev comparePreserved : List Nat := [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51]

private theorem compareStackAddr {fr : Activation} (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (off : Nat) (h : off ≤ 184) :
    (sp fr + BitVec.ofNat 64 off).toNat = fr.rsp.toNat - 184 + off := by
  change (fr.rsp - 184 + BitVec.ofNat 64 off).toNat = _
  have nat := stackSub_toNat room 184 (by decide)
  change (fr.rsp - 184).toNat = _ at nat
  have := fr.rsp.isLt
  rw [BitVec.toNat_add, nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem runZeroCompareBlock {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (second : Bool)
    (rsp : args[4] = ⟨64, sp fr⟩)
    (win : Writable code mem (fr.rsp - 560) 560)
    (room : fr.low.toNat + 560 ≤ fr.rsp.toNat) :
    let ret : BitVec 64 := if second then 0x103c3f else 0x103bf1
    ∃ regs,
      program.runBlock (dialect code) ⟨if second then .l103bff else .l103b80, args, mem⟩ =
        .call ⟨.l127f50, regs, compareMemory (sp fr) mem second⟩
          (resumeAt (if second then .l103c3f else .l103bf1) ret) ∧
      regs[4] = ⟨64, sp fr - 8⟩ ∧ regs[7] = ⟨64, sp fr + (if second then 136 else 104)⟩ ∧
      regs[6] = ⟨64, 4⟩ ∧ regs[2] = ⟨64, sp fr + 8⟩ ∧ regs[1] = ⟨64, 4⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ comparePreserved → regs[i] = args[i]) := by
  let p := sp fr
  have spGet : args[4].get 64 = p := congrArg (Value.get 64) rsp
  have bottom := stackSub_toNat room 560 (by decide)
  change (fr.rsp - 560).toNat = _ at bottom
  have word (off : Nat) (h : off + 8 ≤ 184) : Writable code mem (p + BitVec.ofNat 64 off) 8 := by
    have addr := compareStackAddr room off (by omega)
    exact win.sub (by change (fr.rsp - 560).toNat ≤ _; rw [bottom, addr]; omega)
      (by change _ ≤ (fr.rsp - 560).toNat + _; rw [bottom, addr]; omega)
  have read (off : Nat) (h : off + 8 ≤ 184) : LoadOk mem (p + BitVec.ofNat 64 off) 8 :=
    ⟨(word off h).readable.low, (word off h).readable.present⟩
  have slot : Writable code mem (p - 8) 8 := by
    have eq : p - 8 = fr.rsp - 192 := by change fr.rsp - 184 - 8 = _; bv_omega
    rw [eq]
    exact win.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have copyCode := fun x hx => hcode x (code_l103b80 x hx)
  have clearCode := fun x hx => hcode x (code_l103bff x hx)
  cases second
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    let c1 := memStore mem (p + 152) (memLoad mem (p + 32) 64)
    let c2 := memStore c1 (p + 160) (memLoad c1 (p + 40) 64)
    let c3 := memStore c2 (p + 136) (memLoad mem (p + 16) 64)
    let copied := copySecondScalar p mem
    let c5 := memStore copied (p + 32) (0 : BitVec 64)
    let c6 := memStore c5 (p + 24) (0 : BitVec 64)
    let c7 := memStore c6 (p + 16) (0 : BitVec 64)
    have read40 : LoadOk c1 (p + 40) 8 := by
      have h := (word 40 (by decide)).readable.memStore (p + 152) (memLoad mem (p + 32) 64)
      exact ⟨h.low, h.present⟩
    have s1 : StoreOk code mem (p + 152) 8 0x103b8f 8 :=
      storeOk_of_codeRange (off := 15) (word 152 (by decide)) copyCode (by decide)
    have s2 : StoreOk code c1 (p + 160) 8 0x103b9c 8 :=
      storeOk_of_codeRange (off := 28)
        (by
          repeat' apply Writable.memStore
          exact word 160 (by decide)) copyCode (by decide)
    have s3 : StoreOk code c2 (p + 136) 8 0x103ba4 8 :=
      storeOk_of_codeRange (off := 36)
        (by
          repeat' apply Writable.memStore
          exact word 136 (by decide)) copyCode (by decide)
    have s4 : StoreOk code c3 (p + 144) 8 0x103bac 8 :=
      storeOk_of_codeRange (off := 44)
        (by
          repeat' apply Writable.memStore
          exact word 144 (by decide)) copyCode (by decide)
    have s5 : StoreOk code copied (p + 32) 8 0x103bb4 9 :=
      storeOk_of_codeRange (off := 52)
        (by
          repeat' apply Writable.memStore
          exact word 32 (by decide)) copyCode (by decide)
    have s6 : StoreOk code c5 (p + 24) 8 0x103bbd 9 :=
      storeOk_of_codeRange (off := 61)
        (by
          repeat' apply Writable.memStore
          exact word 24 (by decide)) copyCode (by decide)
    have s7 : StoreOk code c6 (p + 16) 8 0x103bc6 9 :=
      storeOk_of_codeRange (off := 70)
        (by
          repeat' apply Writable.memStore
          exact word 16 (by decide)) copyCode (by decide)
    have s8 : StoreOk code c7 (p + 8) 8 0x103bcf 9 :=
      storeOk_of_codeRange (off := 79)
        (by
          repeat' apply Writable.memStore
          exact word 8 (by decide)) copyCode (by decide)
    have s9 : StoreOk code (clearCompareWords p copied) (p - 8) 8 0x103bec 5 :=
      storeOk_of_codeRange (off := 108)
        (by
          repeat' apply Writable.memStore
          exact slot) copyCode (by decide)
    refine ⟨?regs, ?run, ?post⟩
    case run =>
      cfg_eval [spGet]
      refine (ite_eq_left (read 16 (by decide))).trans ?_
      refine (ite_eq_left (read 24 (by decide))).trans ?_
      refine (ite_eq_left (read 32 (by decide))).trans ?_
      rw [ite_eq_left s1, ite_eq_left read40, ite_eq_left s2, ite_eq_left s3, ite_eq_left s4,
        ite_eq_left s5, ite_eq_left s6, ite_eq_left s7, ite_eq_left s8, ite_eq_left s9]
      rfl
    case post =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro ⟨i, bound⟩ hi
      simp only [comparePreserved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [↓reduceIte]
    let c1 := memStore mem (p + 32) (0 : BitVec 64)
    let c2 := memStore c1 (p + 24) (0 : BitVec 64)
    let c3 := memStore c2 (p + 16) (0 : BitVec 64)
    have s1 : StoreOk code mem (p + 32) 8 0x103bff 9 :=
      storeOk_of_codeRange (off := 0) (word 32 (by decide)) clearCode (by decide)
    have s2 : StoreOk code c1 (p + 24) 8 0x103c08 9 :=
      storeOk_of_codeRange (off := 9)
        (by
          repeat' apply Writable.memStore
          exact word 24 (by decide)) clearCode (by decide)
    have s3 : StoreOk code c2 (p + 16) 8 0x103c11 9 :=
      storeOk_of_codeRange (off := 18)
        (by
          repeat' apply Writable.memStore
          exact word 16 (by decide)) clearCode (by decide)
    have s4 : StoreOk code c3 (p + 8) 8 0x103c1a 9 :=
      storeOk_of_codeRange (off := 27)
        (by
          repeat' apply Writable.memStore
          exact word 8 (by decide)) clearCode (by decide)
    have s5 : StoreOk code (clearCompareWords p mem) (p - 8) 8 0x103c3a 5 :=
      storeOk_of_codeRange (off := 59)
        (by
          repeat' apply Writable.memStore
          exact slot) clearCode (by decide)
    refine ⟨?secondRegs, ?secondRun, ?secondPost⟩
    case secondRun =>
      cfg_eval [spGet]
      rw [ite_eq_left s1, ite_eq_left s2, ite_eq_left s3, ite_eq_left s4, ite_eq_left s5]
      rfl
    case secondPost =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro ⟨i, bound⟩ hi
      simp only [comparePreserved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem compareWordAddr (p : BitVec 64) (off i : Nat) :
    wordAddr (p + BitVec.ofNat 64 off) 64 i = p + BitVec.ofNat 64 (off + 8 * i) := by
  simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc]

private theorem compareWordStore {m : Ram} {p : BitVec 64} {v : Vector (BitVec 64) 4}
    (words : WordsAt m p 64 v) (bound : p.toNat + 32 ≤ 2 ^ 64) (i : Nat) (hi : i < 4)
    (a x : BitVec 64) (addr : a = wordAddr p 64 i) :
    WordsAt (memStore m a x) p 64 (v.set i x) :=
  words.write_set' hi addr rfl (by decide) (by decide) (by decide) bound

private theorem copiedScalarLimbs {fr : Activation} {m : Ram}
    (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (s : scalarLimbsAt m (sp fr + 16) fr.original (fr.rsi + 32)) :
    scalarLimbsAt (copySecondScalar (sp fr) m) (sp fr + 136) fr.original (fr.rsi + 32) := by
  let p := sp fr
  let first := memStore m (p + 152) (memLoad m (p + 32) 64)
  let v := Vector.ofFn (n := 4) fun i => memLoad m (wordAddr (p + 136) 64 i.val) 64
  let src (i : Nat) := scalarWord fr.original (fr.rsi + 32) i
  have init : WordsAt m (p + 136) 64 v := by intro i hi; simp only [v, Vector.getElem_ofFn]
  have read (i : Nat) (hi : i < 4) : memLoad m (p + BitVec.ofNat 64 (16 + 8 * i)) 64 = src i := by
    have h := s i hi
    change memLoad m (wordAddr (p + BitVec.ofNat 64 16) 64 i) 64 = src i at h
    rwa [compareWordAddr] at h
  have readLast : memLoad first (p + 40) 64 = src 3 := by
    change memLoad (memStore m (p + 152) (memLoad m (p + 32) 64)) (p + 40) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide))]
    exact read 3 (by decide)
  have bound : (p + 136).toNat + 32 ≤ 2 ^ 64 := by
    have h := compareStackAddr room 136 (by decide)
    change (p + 136).toNat = _ at h
    have := fr.rsp.isLt
    omega
  have addr (i : Nat) : p + BitVec.ofNat 64 (136 + 8 * i) = wordAddr (p + 136) 64 i :=
    (compareWordAddr p 136 i).symm
  have h2 := compareWordStore init bound 2 (by decide) (p + 152) (memLoad m (p + 32) 64) (addr 2)
  have h3 := compareWordStore h2 bound 3 (by decide) (p + 160) (memLoad first (p + 40) 64) (addr 3)
  have h0 := compareWordStore h3 bound 0 (by decide) (p + 136) (memLoad m (p + 16) 64) (addr 0)
  have h1 := compareWordStore h0 bound 1 (by decide) (p + 144) (memLoad m (p + 24) 64) (addr 1)
  intro i hi
  have atI := h1 i hi
  change memLoad (copySecondScalar p m) (wordAddr (p + 136) 64 i) 64 = _ at atI
  rw [atI]
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases indices with rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_set, ↓reduceIte]
  · exact read 0 (by decide)
  · exact read 1 (by decide)
  · exact read 2 (by decide)
  · exact readLast

private theorem clearCompareWords_zero (m : Ram) (p : BitVec 64)
    (bound : (p + 8).toNat + 32 ≤ 2 ^ 64) :
    WordsAt (clearCompareWords p m) (p + 8) 64 (Vector.replicate 4 0) := by
  let v := Vector.ofFn (n := 4) fun i => memLoad m (wordAddr (p + 8) 64 i.val) 64
  have init : WordsAt m (p + 8) 64 v := by intro i hi; simp only [v, Vector.getElem_ofFn]
  have addr (i : Nat) : p + BitVec.ofNat 64 (8 + 8 * i) = wordAddr (p + 8) 64 i :=
    (compareWordAddr p 8 i).symm
  have h3 := compareWordStore init bound 3 (by decide) (p + 32) 0 (addr 3)
  have h2 := compareWordStore h3 bound 2 (by decide) (p + 24) 0 (addr 2)
  have h1 := compareWordStore h2 bound 1 (by decide) (p + 16) 0 (addr 1)
  have h0 := compareWordStore h1 bound 0 (by decide) (p + 8) 0 (addr 0)
  intro i hi
  have atI := h0 i hi
  change memLoad (clearCompareWords p m) (wordAddr (p + 8) 64 i) 64 = _ at atI
  rw [atI]
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases indices with rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_set, Vector.getElem_replicate, ↓reduceIte, ite_self]

private theorem compareStackStore {fr : Activation} {o m : Ram} {regions : List MemoryRegion}
    {r : MemoryRegion} (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (frame : RamWriteFrame o m regions) (inRegions : r ∈ regions)
    (off : Nat) (value : BitVec 64) (hoff : off + 8 ≤ 184)
    (lo : r.start ≤ fr.rsp.toNat - 184 + off)
    (hi : fr.rsp.toNat - 184 + off + 8 ≤ r.start + r.size) :
    RamWriteFrame o (memStore m (sp fr + BitVec.ofNat 64 off) value) regions := by
  apply frame.memStore
  refine ⟨r, inRegions, ?_⟩
  change r.start ≤ _ ∧ _ + 8 ≤ r.start + r.size ∧ _ + 8 ≤ 2 ^ 64
  rw [compareStackAddr room off (by omega)]
  have := fr.rsp.isLt
  omega

theorem prepareZeroCompare {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (second : Bool)
    (active : Active code fr false args mem)
    (r : scalarLimbsAt mem (sp fr + 104) fr.original fr.rsi)
    (s : scalarLimbsAt mem (sp fr + (if second then 136 else 16)) fr.original (fr.rsi + 32)) :
    let ret : BitVec 64 := if second then 0x103c3f else 0x103bf1
    ∃ regs after,
      program.runBlock (dialect code) ⟨if second then .l103bff else .l103b80, args, mem⟩ =
        .call ⟨.l127f50, regs, after⟩ (resumeAt (if second then .l103c3f else .l103bf1) ret) ∧
      Active code fr false args after ∧ pairLimbs fr after ∧
      (∀ i < 4, memLoad after (wordAddr (sp fr + 8) 64 i) 64 = 0) ∧
      Atom.All code regs after (Fn127f50.frameInfo.entryAtoms (zeroChild fr regs after ret)) ∧
      regs[7].get 64 = sp fr + (if second then 136 else 104) ∧ regs[6].get 64 = 4 ∧
      regs[2].get 64 = sp fr + 8 ∧ regs[1].get 64 = 4 := by
  let p := sp fr
  let ret : BitVec 64 := if second then 0x103c3f else 0x103bf1
  let copied := if second then mem else copySecondScalar p mem
  let cleared := clearCompareWords p copied
  let after := compareMemory p mem second
  have caller := active.atoms
  change Atom.All code args mem (Fn103ac0.frameAt .l103b80 fr) at caller
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at caller
  obtain ⟨rsp, df, bx, bp, r12, r13, r14, r15, mxcsr, ftw, fcw, _, _, _, _, _, win, room,
    aligned, _⟩ := caller
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  obtain ⟨regs, run, calleeRsp, di, si, dx, cx, preserve⟩ :=
    runZeroCompareBlock hcode fr args mem second rsp win room
  have addr (off : Nat) (h : off ≤ 184) :
      (p + BitVec.ofNat 64 off).toNat = fr.rsp.toNat - 184 + off := compareStackAddr room off h
  have slotNat : (p - 8).toNat = fr.rsp.toNat - 192 := by
    rw [show p - 8 = fr.rsp - 192 by change fr.rsp - 184 - 8 = _; bv_omega]
    exact stackSub_toNat room 192 (by decide)
  have copyNat : (p + 136).toNat = fr.rsp.toNat - 184 + 136 := addr 136 (by decide)
  have limit := fr.rsp.isLt
  let copyRange := buffer (p + 136) 32
  have copiedFrame : RamWriteFrame mem copied [copyRange] := by
    have save {m : Ram} (frame : RamWriteFrame mem m [copyRange]) (off : Nat)
        (value : BitVec 64) (lo : 136 ≤ off) (hi : off + 8 ≤ 168) :
        RamWriteFrame mem (memStore m (p + BitVec.ofNat 64 off) value) [copyRange] := by
      apply compareStackStore room frame (List.mem_singleton_self _) off value (by omega)
      · change (p + 136).toNat ≤ _
        omega
      · change _ ≤ (p + 136).toNat + 32
        omega
    cases second
    · change RamWriteFrame mem (copySecondScalar p mem) [copyRange]
      unfold copySecondScalar
      iterate 4 apply save _ _ _ (by decide) (by decide)
      exact RamWriteFrame.refl _ _
    · exact RamWriteFrame.refl _ _
  let clearRange := buffer (p - 8) 48
  have clearFrame : RamWriteFrame copied cleared [clearRange] := by
    have save {m : Ram} (frame : RamWriteFrame copied m [clearRange]) (off : Nat)
        (lo : 8 ≤ off) (hi : off + 8 ≤ 40) :
        RamWriteFrame copied (memStore m (p + BitVec.ofNat 64 off) (0 : BitVec 64)) [clearRange] := by
      apply compareStackStore room frame (List.mem_singleton_self _) off (0 : BitVec 64) (by omega)
      · change (p - 8).toNat ≤ _
        omega
      · change _ ≤ (p - 8).toNat + 48
        omega
    change RamWriteFrame copied (clearCompareWords p copied) [clearRange]
    unfold clearCompareWords
    iterate 4 apply save _ _ (by decide) (by decide)
    exact RamWriteFrame.refl _ _
  have pushedFrame : RamWriteFrame copied after [clearRange] := by
    change RamWriteFrame copied (memStore cleared (p - 8) ret) [clearRange]
    apply clearFrame.memStore
    refine ⟨clearRange, List.mem_singleton_self _, ?_⟩
    change (p - 8).toNat ≤ (p - 8).toNat ∧
      (p - 8).toNat + 8 ≤ (p - 8).toNat + 48 ∧ (p - 8).toNat + 8 ≤ 2 ^ 64
    omega
  have copyCaller : Active code fr false args copied := by
    apply active.ofScratchFrame copiedFrame
    intro region hr
    obtain rfl := List.mem_singleton.mp hr
    change fr.low.toNat ≤ (p + 136).toNat ∧
      (p + 136).toNat + 32 ≤ (fr.rsp - 16).toNat
    have h := stackSub_toNat room 16 (by decide)
    change (fr.rsp - 16).toNat = _ at h
    omega
  have afterCaller : Active code fr false args after := by
    apply copyCaller.ofScratchFrame pushedFrame
    intro region hr
    obtain rfl := List.mem_singleton.mp hr
    change fr.low.toNat ≤ (p - 8).toNat ∧
      (p - 8).toNat + 48 ≤ (fr.rsp - 16).toNat
    have h := stackSub_toNat room 16 (by decide)
    change (fr.rsp - 16).toNat = _ at h
    omega
  have copiedLimbs : pairLimbs fr copied := by
    cases second
    · change pairLimbs fr (copySecondScalar p mem)
      refine ⟨?_, copiedScalarLimbs room s⟩
      intro i hi
      have h := addr (104 + 8 * i) (by omega)
      have keep : memLoad copied (wordAddr (p + 104) 64 i) 64 =
          memLoad mem (wordAddr (p + 104) 64 i) 64 := by
        apply copiedFrame.memLoad_eq
        have addrI : (wordAddr (p + 104) 64 i).toNat = fr.rsp.toNat - 184 + (104 + 8 * i) := by
          rw [show wordAddr (p + 104) 64 i = p + BitVec.ofNat 64 (104 + 8 * i) from compareWordAddr p 104 i, h]
        refine ⟨by rw [addrI]; omega, fun region hr => ?_⟩
        obtain rfl := List.mem_singleton.mp hr
        left
        change (wordAddr (p + 104) 64 i).toNat + 8 ≤ (p + 136).toNat
        rw [addrI]
        omega
      exact keep.trans (r i hi)
    · exact ⟨r, s⟩
  have limbs : pairLimbs fr after := by
    apply pairLimbs_of_frame copyCaller copiedLimbs pushedFrame
    intro region hr
    obtain rfl := List.mem_singleton.mp hr
    change (p - 8).toNat + 48 ≤ (p + 104).toNat
    have h : (p + 104).toNat = _ := addr 104 (by decide)
    omega
  have zeros : ∀ i < 4, memLoad after (wordAddr (p + 8) 64 i) 64 = 0 := by
    have h : (p + 8).toNat = _ := addr 8 (by decide)
    have zs := clearCompareWords_zero copied p (by omega)
    have zs' := zs.write_apart (p - 8) ret (RangeApart.of_offsets (addr_sub _ _) rfl (by decide))
    intro i hi
    simpa only [Vector.getElem_replicate] using zs' i hi
  have nextWidths : ArgumentWidths regs := by
    intro ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width di
    · exact congrArg Value.width si
    · exact congrArg Value.width dx
    · exact congrArg Value.width cx
    · exact (congrArg Value.width (preserve 8 (by decide))).trans (active.widths 8 (by decide))
    · exact (congrArg Value.width (preserve 9 (by decide))).trans (active.widths 9 (by decide))
  have returnReadable : Readable after (p - 8) 8 := by
    have win' : Writable code after (fr.rsp - 560) 560 :=
      (win.of_frame copiedFrame).of_frame pushedFrame
    have h := stackSub_toNat room 560 (by decide)
    change (fr.rsp - 560).toNat = _ at h
    exact win'.readable.sub (by rw [h, slotNat]; omega) (by rw [h, slotNat]; omega)
  have pushedRet : memLoad after (p - 8) 64 = ret :=
    memLoad_memStore_same cleared _ ret (by decide) (by decide)
  have entry : Atom.All code regs after (Fn127f50.frameInfo.entryAtoms (zeroChild fr regs after ret)) := by
    change Atom.All code regs after (Fn127f50.frameAt .l127f50 (zeroChild fr regs after ret))
    simp only [Fn127f50.frameAt, Fn127f50.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨calleeRsp, (preserve 22 (by decide)).trans df, entryArgument nextWidths fr 1 (by decide),
      entryArgument nextWidths fr 2 (by decide), (preserve 3 (by decide)).trans bx,
      (preserve 5 (by decide)).trans bp, entryArgument nextWidths fr 6 (by decide),
      entryArgument nextWidths fr 7 (by decide), entryArgument nextWidths fr 8 (by decide),
      entryArgument nextWidths fr 9 (by decide), (preserve 12 (by decide)).trans r12,
      (preserve 13 (by decide)).trans r13, (preserve 14 (by decide)).trans r14,
      (preserve 15 (by decide)).trans r15, (preserve 39 (by decide)).trans mxcsr,
      (preserve 50 (by decide)).trans ftw, (preserve 51 (by decide)).trans fcw,
      returnReadable, pushedRet, ?_, ?_, ?_, trivial⟩
    · change ret.toNat < 2 ^ 32
      cases second <;> decide
    · change (p - 9).toNat ≤ (p - 8).toNat
      rw [show p - 9 = fr.rsp - 193 by change fr.rsp - 184 - 9 = _; bv_omega, slotNat]
      have h := stackSub_toNat room 193 (by decide)
      change (fr.rsp - 193).toNat = _ at h
      omega
    · change (p - 8).toNat % 16 = 8
      rw [slotNat]
      change fr.rsp.toNat % 16 = 8 at aligned
      omega
  exact ⟨regs, after, run, afterCaller, limbs, zeros, entry,
    congrArg (Value.get 64) di, congrArg (Value.get 64) si,
    congrArg (Value.get 64) dx, congrArg (Value.get 64) cx⟩

end K256.Proofs.ParseSignature.Pair
