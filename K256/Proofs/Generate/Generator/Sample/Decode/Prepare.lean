import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.Generator.Sample.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.LIR.Fn109e60.Frame

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def prepareRegions (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 400).toNat, 8⟩, ⟨(fr.rsp - 288).toNat, 32⟩, ⟨fr.rsi.toNat, 16⟩]

def decodeActivation (fr : Activation) (s : RamState) (random : ByteArray) (i : Nat)
    (b : Registers) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := fr.rsp - 400, low := fr.rsp - 465, ret := 0x10605d,
    rbx := remaining random (i+1), rbp := cursor s i, r12 := fr.rsp - 288,
    r13 := remaining random i, r14 := fr.rsi, r15 := fr.rsp - 168,
    rsi := fr.rsp - 288, rdi := fr.rsp - 168, rdx := b[2].get 64, rcx := b[1].get 64,
    r8 := b[8].get 64, r9 := b[9].get 64 }

private def copyMemory (mem : Ram) (sp desc cur len : BitVec 64) : Ram :=
  let m := memStore mem desc cur
  let m := memStore m (desc + 8) (len - 32)
  let m := memStore m (sp + 128) (memLoad mem (cur - 8) 64)
  let m := memStore m (sp + 120) (memLoad mem (cur - 16) 64)
  let m := memStore m (sp + 112) (memLoad mem (cur - 24) 64)
  let m := memStore m (sp + 104) (memLoad mem (cur - 32) 64)
  memStore m (sp - 8) (0x10605d : BitVec 64)

set_option maxHeartbeats 2000000 in
private theorem prepareBlock {code : CodeMap} (inc : ∀ x ∈ codeRange 0x106020 bytes_l106020, x ∈ code)
    {b : Registers} {mem : Ram} {sp desc cur len : BitVec 64}
    (h4 : b[4].get 64 = sp) (h14 : b[14].get 64 = desc)
    (h5 : b[5].get 64 = cur) (h13 : b[13].get 64 = len)
    (src : Readable mem (cur - 32) 32)
    (dest : Writable code mem (sp - 8) 144)
    (hdr : Writable code mem desc 16)
    (apart₁ : (cur - 32).toNat + 32 ≤ (sp - 8).toNat ∨ (sp - 8).toNat + 144 ≤ (cur - 32).toNat)
    (apart₂ : (cur - 32).toNat + 32 ≤ desc.toNat ∨ desc.toNat + 16 ≤ (cur - 32).toNat) :
    let c := (b.set 0 ⟨64, memLoad mem (cur - 32) 64⟩).set 1 ⟨64, memLoad mem (cur - 24) 64⟩
    let c := (c.set 3 ⟨64, len - 32⟩).set 4 ⟨64, sp - 8⟩
    let c := (c.set 6 ⟨64, b[12].get 64⟩).set 7 ⟨64, b[15].get 64⟩
    program.runBlock (dialect code) ⟨.l106020, b, mem⟩ =
      .call ⟨.l109e60, c, copyMemory mem sp desc cur len⟩ (callFrame .l10605d 0x10605d) := by
  dsimp only
  cfg_eval
  simp only [h4, h14, h5, h13]
  repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using inc)
  simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun he => Vector.ext fun i hi => he ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [Vector.getElem_set] <;> rfl
private theorem copiedWord (m : Ram) (sp desc cur len : BitVec 64) (j : Nat) (hj : j < 4) :
    Common.scalarWord (copyMemory m sp desc cur len) (sp + 104) j =
      bswapSpec (memLoad m (cur - BitVec.ofNat 64 (8 * (j + 1))) 64) := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;>
    simp (disch := first | store_disch | decide) only [Common.scalarWord, copyMemory,
      Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, reduceAddOffset,
      BitVec.add_zero, memLoad_memStore_of_rangeApart, memLoad_memStore_same] <;> rfl

private theorem copyFrame (m : Ram) (sp cur len : BitVec 64)
    (room : 688 ≤ sp.toNat) (low : sp.toNat < 2^32 + 208) :
    RamWriteFrame m (copyMemory m (sp - 680) (sp - 208) cur len)
      [⟨(sp - 688).toNat, 8⟩, ⟨(sp - 576).toNat, 32⟩, ⟨(sp - 208).toNat, 16⟩] := by
  have off (k : BitVec 64) (h : k.toNat ≤ 688) :
      (sp - k).toNat = sp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  simp only [copyMemory, reduceAddOffset, reduceSubOffset]
  repeat' (apply RamWriteFrame.memStore; rotate_left
           simp (disch := decide) only [InRegions, InRegion, List.mem_cons, List.not_mem_nil,
             or_false, exists_eq_or_imp, exists_eq_left, off, BitVec.reduceToNat, Nat.reduceDiv]
           omega)
  exact RamWriteFrame.refl _ _

private theorem valueAtWidth (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  cases v with
  | mk w x => cases h; rfl

private theorem cursorOffset (s : RamState) (i k : Nat) (hk : k ≤ 32) :
    cursor s i - BitVec.ofNat 64 k = s.regValue .rsi + BitVec.ofNat 64 (32*i + (32-k)) := by
  have he : 32 * (i+1) = 32*i + (32-k) + k := by omega
  simp only [cursor, he, BitVec.ofNat_add]
  bv_omega

private theorem remainingNext {random : ByteArray} {i : Nat} (h : i < random.size / 32) :
    remaining random i - 32 = remaining random (i+1) := by
  have he : random.size - 32*i = (random.size - 32*(i+1)) + 32 := by omega
  simp only [remaining, he, BitVec.ofNat_add]
  bv_omega

set_option maxHeartbeats 650000 in
theorem prepareDecode {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (entry : Entry s fr a) {i : Nat}
    {b : Registers} {mem : Ram} (bound : i < random.size / 32) (current : AtBlock s random fr i b mem) :
    ∃ c m, program.runBlock (dialect Extracted.programImage) ⟨.l106020, b, mem⟩ =
      .call ⟨.l109e60, c, m⟩ (callFrame .l10605d 0x10605d) ∧
      Atom.All Extracted.programImage c m (Fn109e60.frameAt .l109e60 (decodeActivation fr s random i c m)) ∧
      RamWriteFrame mem m (prepareRegions fr) ∧
      ∀ j < 4, Common.scalarWord m (fr.rsp - 288) j = word s i j := by
  let sp := stackPtr s
  let src := s.regValue .rsi
  have room : 10584 ≤ sp.toNat := call.stackAvailable.2.2.1
  have align : sp.toNat % 16 = 8 := call.stackAvailable.2.2.2
  have regsp : s.regValue .rsp = sp := rfl
  obtain ⟨hsp, hdf, hdesc, hmx, hftw, hfcw, _⟩ := current.atoms
  change b[4] = ⟨64, fr.rsp - 392⟩ at hsp
  change b[14] = ⟨64, fr.rsi⟩ at hdesc
  have physical (off : Nat) (h : off ≤ 10584) :
      (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := stackOffset call h
  have stack := stackFrame call entry current.writes
  have input : ValidInput s (registerRegion s .rsi random.size) random := call.inputsInMemory.1
  have low : src.toNat + random.size < 2^32 := input.2.1
  have fits : 32*i + 32 ≤ random.size := by omega
  have base : (cursor s i - 32).toNat = src.toNat + 32*i := by
    change (cursor s i - BitVec.ofNat 64 32).toNat = _
    rw [cursorOffset s i 32 (by decide)]
    simp only [Nat.sub_self, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 32*i) (by omega), Nat.mod_eq_of_lt (by change src.toNat + 32*i < _; omega)]
  have allRead := Readable.of_hasBytes input.2.2 input.2.1
  change Readable s.external (BitVec.ofNat 64 src.toNat) random.size at allRead
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at allRead
  have hr : Readable mem (cursor s i - 32) 32 :=
    (allRead.of_frame stack).sub (by rw [base]; omega) (by rw [base]; omega)
  have win : Writable Extracted.programImage mem (sp - 688) 144 :=
    stackWritableAt (off := 688) call entry current.writes (by decide) (by decide) (by decide)
  have hdr : Writable Extracted.programImage mem (sp - 208) 16 :=
    stackWritableAt (off := 208) call entry current.writes (by decide) (by decide) (by decide)
  let sr := Stack.region s signingKeyGenerateFromRng.minStackBytes
  have sep : MemorySeparation [outputRegion signingKeyGenerateFromRng s, sr]
      [registerRegion s .rsi random.size] := call.separation
  have disjoint := apart_of_disjoint ((sep.2 sr (by simp)).2 _ (.head _))
    (by change 0 < sp.toNat + 8 - (sp.toNat - 10584); omega)
    (by change 0 < random.size; omega)
  change sp.toNat - 10584 + (sp.toNat + 8 - (sp.toNat - 10584)) ≤ src.toNat ∨
    src.toNat + random.size ≤ sp.toNat - 10584 at disjoint
  have p4 : b[4].get 64 = sp - 680 := by
    simp only [hsp, Value.get_mk, entry.rsp, regsp, reduceSubOffset]
  have p14 : b[14].get 64 = sp - 208 := by
    simp only [hdesc, Value.get_mk, entry.descriptor, regsp]
  have p5 : b[5].get 64 = cursor s i := by rw [current.cursorReg, Value.get_mk]
  have p13 : b[13].get 64 = remaining random i := by rw [current.remainingReg, Value.get_mk]
  have norm : sp - 680 - 8 = sp - 688 := by bv_omega
  have ph688 := physical 688 (by decide)
  have ph208 := physical 208 (by decide)
  change (sp - 688).toNat = _ at ph688
  change (sp - 208).toNat = _ at ph208
  have inc := fun x hx => Common.fnCode_subset_programImage x (code_l106020 x hx)
  have run := prepareBlock inc p4 p14 p5 p13 hr (norm ▸ win) hdr
    (by rw [norm, ph688, base]; omega) (by rw [ph208, base]; omega)
  dsimp only at run
  rw [run]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp only [Fn109e60.frameAt, Fn109e60.frameAtG0, decodeActivation, Atom.All, Atom.gpr,
      Atom.Holds, Fin.getElem_fin, Vector.getElem_set, reduceIte, Nat.reduceEqDiff,
      current.scratch, current.decoded, Value.get_mk, remainingNext bound,
      entry.rsp, entry.descriptor, regsp, reduceSubOffset]
    have hx := physical 753 (by decide)
    change (sp - 753).toNat = _ at hx
    have ww : Writable Extracted.programImage mem (sp - 753) 65 :=
      stackWritableAt (off := 753) call entry current.writes (by decide) (by decide) (by decide)
    refine ⟨rfl, hdf, rfl, valueAtWidth _ current.rdxWidth, rfl, current.cursorReg, rfl, rfl,
      valueAtWidth _ current.r8Width, valueAtWidth _ current.r9Width, ?_, current.remainingReg,
      ?_, ?_, hmx, hftw, hfcw, ?_, ?_, by decide, ?_, by omega, by omega, trivial⟩
    · change b[12] = _
      simpa only [entry.rsp, regsp, reduceSubOffset] using current.scratch
    · change b[14] = _
      simpa only [entry.descriptor, regsp] using hdesc
    · change b[15] = _
      simpa only [entry.rsp, regsp, reduceSubOffset] using current.decoded
    all_goals simp only [copyMemory, reduceAddOffset, reduceSubOffset]
    · slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · slot_state region
  · have top := hdr.readable.low
    change (sp - 208).toNat + 16 ≤ 2^32 at top
    simpa only [prepareRegions, entry.rsp, regsp, entry.descriptor, reduceSubOffset] using
      copyFrame mem sp (cursor s i) (remaining random i) (by omega) (by omega)
  · intro j hj
    have scratch : fr.rsp - 288 = sp - 680 + 104 := by rw [entry.rsp, regsp]; bv_omega
    rw [scratch, copiedWord _ _ _ _ _ j hj, cursorOffset _ _ _ (by omega)]
    have same := (inputLoad call stack (32*i + (32-8*(j+1))) (by omega)).2
    rw [same]
    have addr : 32 - 8*(j+1) = 8*(3-j) := by omega
    simp only [word, Common.scalarWord, addr, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_assoc]

end K256.Proofs.Generate.Generator.Sample
