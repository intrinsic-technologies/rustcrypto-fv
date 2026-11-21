import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Limbs
import K256.Proofs.Common.Tactic
import K256.Proofs.Sec1.Serialize.Assemble.Memory

namespace K256.Proofs.Generate.Generator.Multiply.Split.Rounding

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private def storeWords (m : Ram) (p : BitVec 64) (v : Vector (BitVec 64) 4) : Ram :=
  memStore (memStore (memStore (memStore m p v[0]) (p + 8) v[1]) (p + 16) v[2]) (p + 24) v[3]

private theorem storeWords_frame {m n : Ram} {p : BitVec 64} {v : Vector (BitVec 64) 4}
    {rs : List MemoryRegion} (h : RamWriteFrame m n rs)
    (inside : ⟨p.toNat,32⟩ ∈ rs) (bound : p.toNat + 32 ≤ 2^64) :
    RamWriteFrame m (storeWords n p v) rs := by
  unfold storeWords
  have fits (off : Nat) (hoff : off ≤ 24) :
      InRegion ⟨p.toNat,32⟩ (p + BitVec.ofNat 64 off) 8 := by
    simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := off) (b := 2^64) (by omega),
      Nat.mod_eq_of_lt (a := p.toNat + off) (b := 2^64) (by omega)]
    omega
  have firstWord : InRegion ⟨p.toNat,32⟩ p 8 := by
    simpa only [show p + BitVec.ofNat 64 0 = p by simp] using fits 0 (by decide)
  exact ((((h.memStore v[0] ⟨_,inside,firstWord⟩).memStore v[1] ⟨_,inside,fits 8 (by decide)⟩).memStore v[2]
    ⟨_,inside,fits 16 (by decide)⟩).memStore v[3] ⟨_,inside,fits 24 (by decide)⟩)

private theorem storeWords_words (m : Ram) (p : BitVec 64) (v : Vector (BitVec 64) 4)
    : WordsAt (storeWords m p v) p 64 v := by
  have apart (i j : Nat) (hi : i ≤ 24) (hj : j + 8 ≤ i) :
      RangeApart (p + BitVec.ofNat 64 i) 8 (p + BitVec.ofNat 64 j) 8 := by
    apply RangeApart.of_offsets rfl rfl
    have hi' : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    have hj' : (BitVec.ofNat 64 j).toNat = j := Nat.mod_eq_of_lt (by omega)
    have hjLe : (BitVec.ofNat 64 j) ≤ BitVec.ofNat 64 i := BitVec.le_def.mpr (by rw [hi', hj']; omega)
    rw [BitVec.toNat_sub_of_le hjLe]
    simp only [BitVec.toNat_sub, hi', hj']
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have apart0 (i : Nat) (hi : 8 ≤ i) (hm : i ≤ 24) :=
    show RangeApart (p + BitVec.ofNat 64 i) 8 p 8 from
      by simpa only [show p + BitVec.ofNat 64 0 = p by simp] using apart i 0 hm (by omega)
  apply Sec1.Serialize.Assemble.fourWordsAt
  all_goals unfold storeWords
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart0 24 (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart0 16 (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart0 8 (by decide) (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 24 8 (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 16 8 (by decide) (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 24 16 (by decide) (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
theorem finish {fr : Activation} {a : Registers} {m : Ram} {w : Vector (BitVec 64) 8}
    (atoms : Atom.All Extracted.programImage a m (Fn11b8f0.frameAt .l11bae7 fr))
    (widths : ParseSignature.ArgumentWidths a) (dest : Writable Extracted.programImage m fr.rdi 32)
    (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) (bit : a[0].get 8 = (w[5] >>> 63).setWidth 8)
    (bx : a[3] = ⟨64,w[6]⟩) (r12 : a[12] = ⟨64,w[7]⟩)
    (incremented : WordsAt m (fr.rsp-80) 64 (scalarWords ((upper w+1)%domain.n))) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11bae7,a,m⟩,[]⟩ out ∧
    out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn11b8f0.doneAt fr) ∧
    ParseSignature.ArgumentWidths out.values ∧ WordsAt out.store fr.rdi 64 (scalarWords (roundedHigh w)) ∧
    RamWriteFrame m out.store [⟨fr.rsp.toNat-224,224⟩,⟨fr.rdi.toNat,32⟩] := by
  simp only [Fn11b8f0.frameAt, Fn11b8f0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, r14, mx, ft, fc, _, s48, s40, s32, s24, s16, s8,
    retRead, ret, retLow, stack, room, _, _⟩ := atoms
  have sp : a[4].get 64 = fr.rsp - 152 := congrArg (Value.get 64) rsp
  have dst : a[14].get 64 = fr.rdi := congrArg (Value.get 64) r14
  have byte : (a[0].get 64).setWidth 8 = (w[5] >>> 63).setWidth 8 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans bit
  let tmp := memStore m (fr.rsp - 145) ((w[5] >>> 63).setWidth 8)
  let v := scalarWords (roundedHigh w)
  let final := storeWords tmp fr.rdi v
  let areas : List MemoryRegion := [⟨fr.rsp.toNat - 224,224⟩,⟨fr.rdi.toNat,32⟩]
  have off (d : BitVec 64) (h : d.toNat ≤ 224) : (fr.rsp - d).toNat = fr.rsp.toNat - d.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have n145 : (fr.rsp - 145).toNat = fr.rsp.toNat - 145 := off 145 (by decide)
  have tmpFrame : RamWriteFrame m tmp [⟨(fr.rsp - 145).toNat, 1⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    have h := retRead.low
    exact ⟨_, List.mem_singleton_self _, by simp only [InRegion, n145]; omega⟩
  have dstBound : fr.rdi.toNat + 32 ≤ 2^64 := by have := dest.readable.low; omega
  let precise : List MemoryRegion := [⟨(fr.rsp - 145).toNat,1⟩,⟨fr.rdi.toNat,32⟩]
  have preciseFrame : RamWriteFrame m final precise := by
    apply storeWords_frame _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) dstBound
    exact (RamWriteFrame.refl _ _).trans tmpFrame (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have frame : RamWriteFrame m final areas := by
    apply (RamWriteFrame.refl _ _).trans preciseFrame
    intro r hr
    simp only [precise, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [n145] <;> omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
  have beforeWords (i : Nat) (hi : i < 4) :
      memLoad tmp (fr.rsp - BitVec.ofNat 64 (80 - 8*i)) 64 =
        (scalarWords ((upper w+1)%domain.n))[i] := by
    have h := incremented i hi
    have addr : wordAddr (fr.rsp - 80) 64 i = fr.rsp - BitVec.ofNat 64 (80 - 8*i) := by
      have k : 8 * i + (80 - 8 * i) = 80 := by omega
      have k' := congrArg (BitVec.ofNat 64) k
      simp only [BitVec.ofNat_add] at k'
      simp only [wordAddr, Nat.reduceDiv]
      bv_omega
    rw [addr] at h
    rw [tmpFrame.memLoad_eq, h]
    have hi' : (BitVec.ofNat 64 (80 - 8*i)).toNat = 80 - 8*i := Nat.mod_eq_of_lt (by omega)
    have hn := retRead.low
    have addrNat := off (BitVec.ofNat 64 (80 - 8*i)) (by rw [hi']; omega)
    rw [hi'] at addrNat
    simp only [Outside, List.mem_singleton, forall_eq, n145, addrNat, Nat.reduceDiv]
    exact ⟨by omega, Or.inr (by omega)⟩
  have q0 := beforeWords 0 (by decide)
  have q1 := beforeWords 1 (by decide)
  have q2 := beforeWords 2 (by decide)
  have q3 := beforeWords 3 (by decide)
  change memLoad tmp (fr.rsp - 80) 64 = _ at q0
  change memLoad tmp (fr.rsp - 72) 64 = _ at q1
  change memLoad tmp (fr.rsp - 64) 64 = _ at q2
  change memLoad tmp (fr.rsp - 56) 64 = _ at q3
  have same (d : BitVec 64) (hd : d.toNat ≤ 48) :
      memLoad final (fr.rsp - d) 64 = memLoad m (fr.rsp - d) 64 := by
    apply preciseFrame.memLoad_eq
    have hi := retRead.low
    simp only [Outside, precise, n145, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Nat.reduceDiv, off d (by omega)]
    exact ⟨by omega, Or.inr (by omega), Or.inl (by omega)⟩
  have f48 := (same 48 (by decide)).trans s48
  have f40 := (same 40 (by decide)).trans s40
  have f32 := (same 32 (by decide)).trans s32
  have f24 := (same 24 (by decide)).trans s24
  have f16 := (same 16 (by decide)).trans s16
  have f8 := (same 8 (by decide)).trans s8
  have fret : memLoad final fr.rsp 64 = fr.ret := by
    have h := same 0 (by decide)
    rwa [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega, ret] at h
  have bitRead : memLoad tmp (fr.rsp - 145) 8 = (w[5] >>> 63).setWidth 8 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have select (i : Nat) (hi : i < 4) :
      v[i] = if w[5] >>> 63 = 0 then (#v[w[6],w[7],0,0] : Vector (BitVec 64) 4)[i]
        else (scalarWords ((upper w+1)%domain.n))[i] := by
    dsimp only [v]
    rw [← rounded_choice, upper_words]
    split <;> rfl
  have cmov (x y : BitVec 64) :
      (if (!(testFlags ((w[5] >>> 63).setWidth 8 &&& (w[5] >>> 63).setWidth 8)).ZF.getD false) =
        true then x else y) = (if w[5] >>> 63 = 0 then y else x) := by
    rcases shift_bit w with h | h <;> simp only [h] <;> rfl
  have g3 : a[3].get 64 = w[6] := congrArg (Value.get 64) bx
  have g12 : a[12].get 64 = w[7] := congrArg (Value.get 64) r12
  have v0 : v[0] = (if w[5] >>> 63 = 0 then w[6] else (scalarWords ((upper w+1)%domain.n))[0]) :=
    select 0 (by decide)
  have v1 : v[1] = (if w[5] >>> 63 = 0 then w[7] else (scalarWords ((upper w+1)%domain.n))[1]) :=
    select 1 (by decide)
  have v2 : v[2] = (if w[5] >>> 63 = 0 then (0 : BitVec 64) else (scalarWords ((upper w+1)%domain.n))[2]) :=
    select 2 (by decide)
  have v3 : v[3] = (if w[5] >>> 63 = 0 then (0 : BitVec 64) else (scalarWords ((upper w+1)%domain.n))[3]) :=
    select 3 (by decide)
  suffices ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l11bae7, a, m⟩ = .returned out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn11b8f0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ out.store = final by
    obtain ⟨out, run, tag, done_, ws, eq⟩ := this
    exact ⟨out, .done (by simp only [Program.step, run, Transfer.next]), tag, done_, ws,
      eq ▸ storeWords_words tmp fr.rdi v, eq ▸ frame⟩
  let out : Output Value Ram Reg.count :=
    ⟨#v[⟨64, ((w[5] >>> 63).setWidth 8).setWidth 64⟩, ⟨64, (scalarWords ((upper w+1)%domain.n))[3]⟩, ⟨64,v[3]⟩,
      ⟨64,fr.rbx⟩, ⟨64,fr.rsp+8⟩, ⟨64,fr.rbp⟩,
      ⟨64,v[2]⟩, a[7], a[8], a[9], a[10], a[11], ⟨64,fr.r12⟩, ⟨64,fr.r13⟩, ⟨64,fr.r14⟩,
      ⟨64,fr.r15⟩, a[16], a[17], a[18], a[19], a[20], a[21], a[22], a[23],
      a[24], a[25], a[26], a[27], a[28], a[29], a[30], a[31], a[32],
      a[33], a[34], a[35], a[36], a[37], a[38], a[39], a[40], a[41],
      a[42], a[43], a[44], a[45], a[46], a[47], a[48], a[49], a[50],
      a[51], a[52]], some ⟨64,fr.ret⟩, final⟩
  refine ⟨out, ?run, rfl, ?done_, ?widths, rfl⟩
  case run =>
    dsimp only [tmp] at bitRead q0 q1 q2 q3
    generate_block [sp, dst, g3, g12, byte, Lift.reduceAddOffset]
    simp only [bitRead, q0, q1, q2, q3, cmov]
    simp only [← v0, ← v1, ← v2, ← v3]
    dsimp only [final, storeWords, tmp] at f48 f40 f32 f24 f16 f8 fret
    simp only [f48, f40, f32, f24, f16, f8, fret, retLow, and_true]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l11bae7 | assumption)
    rfl
  case done_ =>
    simp only [Fn11b8f0.doneAt, Atom.All, Atom.Holds]
    exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ft, fc, trivial⟩
  case widths =>
    intro ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact widths 7 (by decide)
    · rfl
    · rfl
    · rfl
    · exact widths 8 (by decide)
    · exact widths 9 (by decide)

end K256.Proofs.Generate.Generator.Multiply.Split.Rounding
