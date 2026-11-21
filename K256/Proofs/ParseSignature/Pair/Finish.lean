import K256.Proofs.ParseSignature.Pair.Frame
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
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.ParseSignature.Pair

open Prelude Standards.SECG.DomainParameters K256.Proofs.Common X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private abbrev exitRegions (fr : Activation) := [buffer (sp fr) 72, buffer fr.rdi 72]

private abbrev preservedAtReturn (regs next : Values Value Reg.count) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51] → next[i] = regs[i]

private theorem exitAddress {m : Ram} {base : BitVec 64} {len : Nat}
    (hr : Readable m base len) {off n : Nat} (h : off + n ≤ len) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  have hl := hr.low
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem exitStoreWithin {mem : Ram} {regions : List MemoryRegion}
    {base : BitVec 64} {len : Nat}
    (hr : Readable mem base len) (hmem : buffer base len ∈ regions) {off : Nat}
    (hoff : off + 8 ≤ len) : InRegions regions (base + BitVec.ofNat 64 off) 8 := by
  refine ⟨_, hmem, ?_⟩
  change base.toNat ≤ _ ∧ _ + 8 ≤ base.toNat + len ∧ _ + 8 ≤ 2 ^ 64
  rw [exitAddress hr hoff]
  have := hr.low
  omega

private theorem pairReturn {code : CodeMap} (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (atoms : Atom.All code args mem (Fn103ac0.frameAt .l103c5c fr))
    (widths : ArgumentWidths args) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l103c5c, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code out.values out.store (Fn103ac0.frameInfo.doneAtoms fr) ∧
      out.store = mem ∧ ArgumentWidths out.values := by
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨hsp, hdf, _, hbp, h12, h13, _, h15, hmxcsr, hftw, hfcw,
    hbx, h14, hretRead, hret, hretLow, hstack, _, _⟩ := atoms
  have hspBits : Value.get 64 args[4] = fr.rsp - 184 := congrArg (Value.get 64) hsp
  have hpop : fr.rsp - 184 + 168 = fr.rsp - 16 := by bv_omega
  have hpop₂ : fr.rsp - 184 + 176 = fr.rsp - 8 := by bv_omega
  have hpop₃ : fr.rsp - 184 + 184 = fr.rsp := by bv_omega
  have hspDone : fr.rsp - 184 + 192 = fr.rsp + 8 := by bv_omega
  have hb : LoadOk mem (fr.rsp - 16) 8 :=
    LoadOk.of_offsets hstack.readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have hside : LoadOk mem (fr.rsp - 8) 8 :=
    LoadOk.of_offsets hstack.readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have hretOk : LoadOk mem fr.rsp 8 := ⟨hretRead.low, hretRead.present⟩
  have evaluate : ∃ out,
      program.runBlock (dialect code) ⟨.l103c5c, args, mem⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code out.values out.store (Fn103ac0.frameInfo.doneAtoms fr) ∧
      out.store = mem ∧ ArgumentWidths out.values := by
    refine ⟨?_, ?eval, ?tag, ?atoms, ?memEq, ?widths⟩
    case eval =>
      cfg_eval
      simp only [hspBits, hpop, hpop₂, hpop₃, hspDone, hb, hside, hretOk, hretLow,
        hbx, h14, hret, and_self, ↓reduceIte]
      rfl
    case tag => rfl
    case memEq => rfl
    case atoms =>
      simp only [Fn103ac0.frameInfo, FrameInfo.doneAtoms, Activation.entryReg,
        Activation.entryValue, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        Atom.All, Atom.Holds]
      exact ⟨rfl, hdf, rfl, hbp, h12, h13, rfl, h15, hmxcsr, hftw, hfcw, trivial⟩
    case widths =>
      intro ⟨i, hi⟩ harg
      have hwidth := widths ⟨i, hi⟩ harg
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at harg
      rcases harg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwidth
  obtain ⟨out, heval, htag, hdone, hstore, hwidths⟩ := evaluate
  refine ⟨out, Program.Exec.done ?_, htag, hdone, hstore, hwidths⟩
  simp only [Program.step, heval, Transfer.next]

private theorem pairReject {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hdst : args[3] = ⟨64, fr.rdi⟩) (hw : Writable code mem fr.rdi 72)
    (widths : ArgumentWidths args) :
    ∃ next after,
      program.runBlock (dialect code) ⟨.l103c4d, args, mem⟩ = .jump ⟨.l103c5c, next, after⟩ ∧
      preservedAtReturn args next ∧ ArgumentWidths next ∧
      RamWriteFrame mem after (exitRegions fr) ∧
      memLoad after fr.rdi 64 = 1 ∧ memLoad after (fr.rdi + 8) 64 = 0 := by
  let first := memStore mem (fr.rdi + 8) (0 : BitVec 64)
  let after := memStore first fr.rdi (1 : BitVec 64)
  have hdi : Value.get 64 args[3] = fr.rdi := congrArg (Value.get 64) hdst
  have included : ∀ x ∈ codeRange 0x103c4d bytes_l103c4d, x ∈ code :=
    fun x hx => hcode x (code_l103c4d x hx)
  have firstOk : StoreOk code mem (fr.rdi + 8) 8 0x103c4d 8 :=
    storeOk_of_codeRange (off := 0) (hw.of_offsets rfl (addr_self _) (by decide)) included (by decide)
  have afterOk : StoreOk code first fr.rdi 8 0x103c55 7 :=
    storeOk_of_codeRange (off := 8)
      ((hw.memStore (fr.rdi + 8) (0 : BitVec 64)).of_offsets (addr_self _) (addr_self _) (by decide))
      included (by decide)
  have hout : buffer fr.rdi 72 ∈ exitRegions fr := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have firstIn : InRegions (exitRegions fr) (fr.rdi + 8) 8 :=
    exitStoreWithin hw.readable hout (by decide : 8 + 8 ≤ 72)
  have secondIn : InRegions (exitRegions fr) fr.rdi 8 := by
    rw [addr_self fr.rdi]
    exact exitStoreWithin hw.readable hout (by decide : 0 + 8 ≤ 72)
  have writes : RamWriteFrame mem after (exitRegions fr) :=
    (((RamWriteFrame.refl _ _).memStore (0 : BitVec 64) firstIn).memStore (1 : BitVec 64) secondIn)
  refine ⟨?next, after, ?eval, ?preserved, ?widths, writes, ?tag, ?zero⟩
  case eval =>
    cfg_eval
    rw [hdi, ite_eq_left firstOk]
    rw [ite_eq_left afterOk]
  case preserved =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case widths =>
    intro ⟨i, hi⟩ harg
    have hwidth := widths ⟨i, hi⟩ harg
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwidth
  case tag => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case zero =>
    change memLoad (memStore first fr.rdi (1 : BitVec 64)) (fr.rdi + 8) 64 = 0
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (addr_self _) rfl (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

private def writeWords (base : BitVec 64) (index : Nat → Nat) (word : Nat → BitVec 64)
    (start : Ram) : Nat → Ram
  | 0 => start
  | i + 1 => memStore (writeWords base index word start i) (wordAddr base 64 (index i)) (word (index i))

private theorem writeWords_frame {base : BitVec 64} {index : Nat → Nat} {word : Nat → BitVec 64}
    {original start : Ram} {regions : List MemoryRegion}
    (h : RamWriteFrame original start regions) (n : Nat)
    (within : ∀ i < n, InRegions regions (wordAddr base 64 (index i)) 8) :
    RamWriteFrame original (writeWords base index word start n) regions := by
  induction n with
  | zero => exact h
  | succ n ih => exact (ih fun i hi => within i (by omega)).memStore _ (within n (by omega))

private theorem descendingWords {base : BitVec 64} {word : Nat → BitVec 64}
    {start : Ram} (hr : Readable start base 72) (n i : Nat) (hn : n ≤ 8)
    (hi : 9 - n ≤ i) (hi' : i ≤ 8) :
    memLoad (writeWords base (fun j => 8 - j) word start n) (wordAddr base 64 i) 64 = word i := by
  induction n with
  | zero => omega
  | succ n ih =>
    change memLoad (memStore (writeWords base (fun j => 8 - j) word start n)
      (wordAddr base 64 (8 - n)) (word (8 - n))) (wordAddr base 64 i) 64 = word i
    by_cases he : i = 8 - n
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · have h1 : (wordAddr base 64 (8 - n)).toNat = base.toNat + 8 * (8 - n) :=
        exitAddress hr (by omega : 8 * (8 - n) + 8 ≤ 72)
      have h2 : (wordAddr base 64 i).toNat = base.toNat + 8 * i :=
        exitAddress hr (by omega : 8 * i + 8 ≤ 72)
      have low := hr.low
      have apart : RangeApart (wordAddr base 64 (8 - n)) 8 (wordAddr base 64 i) 8 := by
        apply RangeApart.of_toNat <;> simp only [h1, h2] <;> omega
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart]
      exact ih (by omega) (by omega)

set_option maxRecDepth 2048 in
private theorem pairAccept {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hsp : args[4] = ⟨64, sp fr⟩) (hdst : args[3] = ⟨64, fr.rdi⟩)
    (hwStack : Writable code mem (sp fr) 168) (hwOut : Writable code mem fr.rdi 72)
    (limbsR : scalarLimbsAt mem (sp fr + 104) fr.original fr.rsi)
    (limbsS : scalarLimbsAt mem (sp fr + 136) fr.original (fr.rsi + 32)) :
    ∃ next after,
      program.runBlock (dialect code) ⟨.l103c6a, args, mem⟩ = .jump ⟨.l103c5c, next, after⟩ ∧
      preservedAtReturn args next ∧ ArgumentWidths next ∧
      RamWriteFrame mem after (exitRegions fr) ∧
      memLoad after fr.rdi 64 = 0 ∧
      scalarLimbsAt after (fr.rdi + 8) fr.original fr.rsi ∧
      scalarLimbsAt after (fr.rdi + 40) fr.original (fr.rsi + 32) := by
  let word (i : Nat) := memLoad mem (sp fr + BitVec.ofNat 64 (96 + 8 * i)) 64
  let order (i : Nat) := if i < 4 then 4 - i else i + 1
  let stage := writeWords (sp fr) order word mem
  let dest := writeWords fr.rdi (fun j => 8 - j) word (stage 8)
  let after := memStore (dest 8) fr.rdi (0 : BitVec 64)
  have stageRead := hwStack.readable.sub (Nat.le_refl _) (show (sp fr).toNat + 72 ≤ _ by omega)
  have stageWrites (n : Nat) (hn : n ≤ 8) :
      RamWriteFrame mem (stage n) [buffer (sp fr) 72] := by
    refine writeWords_frame (RamWriteFrame.refl _ _) n (fun i hi => ?_)
    exact exitStoreWithin stageRead (List.mem_singleton_self _) (show 8 * order i + 8 ≤ 72 by
      dsimp only [order]
      split <;> omega)
  have stageTotal : RamWriteFrame mem (stage 8) (exitRegions fr) := by
    refine (RamWriteFrame.refl _ _).trans (stageWrites 8 (by decide)) ?_
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have outMember : buffer fr.rdi 72 ∈ exitRegions fr :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have destWrites (n : Nat) : RamWriteFrame mem (dest n) (exitRegions fr) := by
    refine writeWords_frame stageTotal n (fun i hi => ?_)
    exact exitStoreWithin hwOut.readable outMember (by omega : 8 * (8 - i) + 8 ≤ 72)
  have statusIn : InRegions (exitRegions fr) fr.rdi 8 := by
    rw [addr_self fr.rdi]
    exact exitStoreWithin hwOut.readable outMember (by decide : 0 + 8 ≤ 72)
  have total := (destWrites 8).memStore (0 : BitVec 64) statusIn
  have included : ∀ x ∈ codeRange 0x103c6a bytes_l103c6a, x ∈ code :=
    fun x hx => hcode x (code_l103c6a x hx)
  have load (n i : Nat) (hn : n ≤ 8) (hi : 1 ≤ i ∧ i ≤ 8) :
      LoadOk (stage n) (sp fr + BitVec.ofNat 64 (96 + 8 * i)) 8 := by
    have addr := exitAddress hwStack.readable (by omega : 96 + 8 * i + 8 ≤ 168)
    exact LoadOk.of_region (hwStack.readable.of_frame (stageWrites n hn))
      (by rw [addr]; omega) (by rw [addr]; omega)
  have read (n i : Nat) (hn : n ≤ 8) (hi : 1 ≤ i ∧ i ≤ 8) :
      memLoad (stage n) (sp fr + BitVec.ofNat 64 (96 + 8 * i)) 64 = word i := by
    have addr := exitAddress hwStack.readable (by omega : 96 + 8 * i + 8 ≤ 168)
    have low := hwStack.readable.low
    apply (stageWrites n hn).memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (sp fr).toNat + 72 ≤ _; omega)
  have stageOk (i off len : Nat) (hi : i < 8) (within : off + len ≤ bytes_l103c6a.length) :
      StoreOk code (stage i) (wordAddr (sp fr) 64 (order i)) 8
        (0x103c6a + BitVec.ofNat 64 off) len := by
    have bound : 8 * order i + 8 ≤ 168 := by
      dsimp only [order]
      split <;> omega
    have addr : (wordAddr (sp fr) 64 (order i)).toNat = (sp fr).toNat + 8 * order i :=
      exitAddress hwStack.readable bound
    exact storeOk_of_codeRange ((hwStack.of_frame (stageWrites i (by omega))).sub
      (by rw [addr]; omega) (by rw [addr]; omega)) included within
  have destOk (i off len : Nat) (hi : i < 8) (within : off + len ≤ bytes_l103c6a.length) :
      StoreOk code (dest i) (wordAddr fr.rdi 64 (8 - i)) 8
        (0x103c6a + BitVec.ofNat 64 off) len := by
    have addr := exitAddress hwOut.readable (by omega : 8 * (8 - i) + 8 ≤ 72)
    exact storeOk_of_codeRange ((hwOut.of_frame (destWrites i)).sub
      (by change fr.rdi.toNat ≤ (fr.rdi + BitVec.ofNat 64 (8 * (8 - i))).toNat; rw [addr]; omega)
      (by change (fr.rdi + BitVec.ofNat 64 (8 * (8 - i))).toNat + 8 ≤ _; rw [addr]; omega))
      included within
  have statusOk : StoreOk code (dest 8) fr.rdi 8 0x103ce9 7 :=
    storeOk_of_codeRange (off := 127)
      ((hwOut.of_frame (destWrites 8)).of_offsets (addr_self _) (addr_self _) (by decide))
      included (by decide)
  have slice (first : Nat) (hf : 1 ≤ first ∧ first + 3 ≤ 8) {src : BitVec 64}
      (h : scalarLimbsAt mem (sp fr + BitVec.ofNat 64 (96 + 8 * first)) fr.original src) :
      scalarLimbsAt after (fr.rdi + BitVec.ofNat 64 (8 * first)) fr.original src := by
    intro i hi
    have outAddr : wordAddr (fr.rdi + BitVec.ofNat 64 (8 * first)) 64 i =
        wordAddr fr.rdi 64 (first + i) := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    have inAddr : sp fr + BitVec.ofNat 64 (96 + 8 * (first + i)) =
        wordAddr (sp fr + BitVec.ofNat 64 (96 + 8 * first)) 64 i := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    have hap : RangeApart fr.rdi 8 (wordAddr fr.rdi 64 (first + i)) 8 := by
      have low := hwOut.readable.low
      have adr : (wordAddr fr.rdi 64 (first + i)).toNat = fr.rdi.toNat + 8 * (first + i) :=
        exitAddress hwOut.readable (by omega : 8 * (first + i) + 8 ≤ 72)
      apply RangeApart.of_toNat <;> (try rw [adr]) <;> omega
    change memLoad (memStore (dest 8) fr.rdi (0 : BitVec 64)) _ 64 = _
    rw [outAddr, memLoad_memStore_of_rangeApart _ _ _ _ _ hap]
    have wordEq := descendingWords (word := word) (hwOut.readable.of_frame stageTotal) 8 (first + i)
      (by decide) (by omega) (by omega)
    exact wordEq.trans ((congrArg (fun a => memLoad mem a 64) inAddr).trans (h i hi))
  have hspBits : Value.get 64 args[4] = sp fr := congrArg (Value.get 64) hsp
  have hdstBits : Value.get 64 args[3] = fr.rdi := congrArg (Value.get 64) hdst
  refine ⟨?next, after, ?eval, ?regs, ?widths, total, ?tag, ?rWords, ?sWords⟩
  case eval =>
    have read3 := read 1 3 (by decide) (by decide)
    have read1 := read 2 1 (by decide) (by decide)
    have read2 := read 2 2 (by decide) (by decide)
    have read5 := read 4 5 (by decide) (by decide)
    have read6 := read 4 6 (by decide) (by decide)
    have read7 := read 6 7 (by decide) (by decide)
    have read8 := read 7 8 (by decide) (by decide)
    simp only [stage, writeWords, order, word, wordAddr, Nat.reduceDiv,
      Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, ↓reduceIte] at read3 read1 read2 read5 read6 read7 read8
    simp only [← BitVec.ofNat_eq_ofNat] at read3 read1 read2 read5 read6 read7 read8
    cfg_eval [b_l103c6a_1, hspBits, hdstBits]
    refine (ite_eq_left (load 0 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (stageOk 0 8 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (load 1 3 (by decide) (by decide))).trans ?_
    rw [read3]
    refine (ite_eq_left (stageOk 1 18 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (load 2 1 (by decide) (by decide))).trans ?_
    rw [read1]
    refine (ite_eq_left (load 2 2 (by decide) (by decide))).trans ?_
    rw [read2]
    refine (ite_eq_left (stageOk 2 33 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (stageOk 3 38 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (load 4 5 (by decide) (by decide))).trans ?_
    rw [read5]
    refine (ite_eq_left (load 4 6 (by decide) (by decide))).trans ?_
    rw [read6]
    refine (ite_eq_left (stageOk 4 59 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (stageOk 5 64 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (load 6 7 (by decide) (by decide))).trans ?_
    rw [read7]
    refine (ite_eq_left (stageOk 6 77 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (load 7 8 (by decide) (by decide))).trans ?_
    rw [read8]
    refine (ite_eq_left (stageOk 7 90 5 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 0 95 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 1 99 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 2 103 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 3 107 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 4 111 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 5 115 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 6 119 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (destOk 7 123 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left statusOk).trans ?_
    rfl
  case regs =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case widths =>
    intro ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case tag => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case rWords => exact slice 1 (by decide) limbsR
  case sWords => exact slice 5 (by decide) limbsS

theorem finishPair {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (valid : Bool)
    (active : Active code fr false args mem)
    (hw : Writable code fr.original fr.rdi 72) (hout : Outside [callStack fr] fr.rdi 72)
    (limbs : valid = true → scalarLimbsAt mem (sp fr + 104) fr.original fr.rsi ∧
      scalarLimbsAt mem (sp fr + 136) fr.original (fr.rsi + 32)) :
    ∃ out, program.Exec (dialect code)
        ⟨⟨if valid then .l103c6a else .l103c4d, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn103ac0.frameInfo.doneAtoms fr) ∧
      RamWriteFrame fr.original out.store [fr.region, buffer fr.rdi 72] ∧ ArgumentWidths out.values ∧
      (if valid then memLoad out.store fr.rdi 64 = 0 ∧
        scalarLimbsAt out.store (fr.rdi + 8) fr.original fr.rsi ∧
        scalarLimbsAt out.store (fr.rdi + 40) fr.original (fr.rsi + 32)
      else memLoad out.store fr.rdi 64 = 1 ∧ memLoad out.store (fr.rdi + 8) 64 = 0) := by
  have atoms := active.atoms
  change Atom.All code args mem (Fn103ac0.frameAt .l103b80 fr) at atoms
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨hsp, hdf, hdi, hbp, h12, h13, hsi, h15, hmxcsr, hftw, hfcw, hbxMem, h14Mem,
    hretRead, hret, hretLow, hstack, hroom, halign, _⟩ := atoms
  have hstackWindow : Writable code mem (sp fr) 168 :=
    hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have localSP : (sp fr).toNat = fr.rsp.toNat - 184 := stackSub_toNat hroom 184 (by decide)
  have outside (off : Nat) (hb : off ≤ 16) :
      Outside (exitRegions fr) (fr.rsp - BitVec.ofNat 64 off) 8 := by
    have nat := stackSub_toNat hroom off (by omega)
    have low := hretRead.low
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (sp fr).toNat + 72 ≤ _
      omega
    · have disjoint := hout.2 _ (List.mem_singleton_self _)
      change fr.rdi.toNat + 72 ≤ fr.low.toNat ∨
        fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at disjoint
      change _ ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 72 ≤ _
      omega
  have keepReturnRead : Outside (exitRegions fr) fr.rsp 8 := by
    have h := outside 0 (by decide)
    change Outside (exitRegions fr) (fr.rsp - 0) 8 at h
    have zero : fr.rsp - 0 = fr.rsp := BitVec.sub_zero _
    rwa [zero] at h
  have keep {args' : Values Value Reg.count} {mem' : Ram}
      (preserved : preservedAtReturn args args') (writes : RamWriteFrame mem mem' (exitRegions fr)) :
      Atom.All code args' mem' (Fn103ac0.frameAt .l103c5c fr) := by
    simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds]
    exact ⟨(preserved 4 (by decide)).trans hsp, (preserved 22 (by decide)).trans hdf,
      (preserved 3 (by decide)).trans hdi, (preserved 5 (by decide)).trans hbp,
      (preserved 12 (by decide)).trans h12, (preserved 13 (by decide)).trans h13,
      (preserved 14 (by decide)).trans hsi, (preserved 15 (by decide)).trans h15,
      (preserved 39 (by decide)).trans hmxcsr, (preserved 50 (by decide)).trans hftw,
      (preserved 51 (by decide)).trans hfcw,
      (writes.memLoad_eq (outside 16 (by decide))).trans hbxMem,
      (writes.memLoad_eq (outside 8 (by decide))).trans h14Mem,
      hretRead.of_frame writes, (writes.memLoad_eq keepReturnRead).trans hret,
      hretLow, hstack.of_frame writes, hroom, halign, trivial⟩
  have frame : RamWriteFrame fr.original mem [fr.region, buffer fr.rdi 72] := by
    refine (RamWriteFrame.refl _ _).trans active.writes ?_
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have subset : RegionsWithin (exitRegions fr) [fr.region, buffer fr.rdi 72] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region, List.mem_cons_self, ?_⟩
      change fr.low.toNat ≤ (sp fr).toNat ∧
        (sp fr).toNat + 72 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
  have advance : ∃ next after,
      program.runBlock (dialect code) ⟨if valid then .l103c6a else .l103c4d, args, mem⟩ =
        .jump ⟨.l103c5c, next, after⟩ ∧
      preservedAtReturn args next ∧ ArgumentWidths next ∧ RamWriteFrame mem after (exitRegions fr) ∧
      (if valid then memLoad after fr.rdi 64 = 0 ∧
        scalarLimbsAt after (fr.rdi + 8) fr.original fr.rsi ∧
        scalarLimbsAt after (fr.rdi + 40) fr.original (fr.rsi + 32)
      else memLoad after fr.rdi 64 = 1 ∧ memLoad after (fr.rdi + 8) 64 = 0) := by
    cases valid
    · exact pairReject hcode fr args mem hdi (hw.of_frame active.writes) active.widths
    · obtain ⟨hr, hs⟩ := limbs rfl
      exact pairAccept hcode fr args mem hsp hdi hstackWindow (hw.of_frame active.writes) hr hs
  obtain ⟨next, after, evaluate, preserved, nextWidths, writes, result⟩ := advance
  obtain ⟨out, exec, tag, done, finalMem, widths⟩ :=
    pairReturn fr next after (keep preserved writes) nextWidths
  refine ⟨out, Program.Exec.next (next := ⟨⟨.l103c5c, next, after⟩, []⟩) ?_ exec,
    tag, done, finalMem ▸ frame.trans writes subset, widths, finalMem ▸ result⟩
  simp only [Program.step, evaluate, Transfer.next]


end K256.Proofs.ParseSignature.Pair
