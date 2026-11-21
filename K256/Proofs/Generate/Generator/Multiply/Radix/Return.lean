import K256.Proofs.Generate.Generator.Multiply.Radix.State

namespace K256.Proofs.Generate.Generator.Multiply.Radix

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

theorem copiedBytes {m n : Ram} {q dest : BitVec 64}
    (word : ∀ o ∈ ([0, 8, 16, 24] : List Nat),
      memLoad n (dest + BitVec.ofNat 64 o) 64 = memLoad m (q + BitVec.ofNat 64 o) 64)
    (top : memLoad n (dest + 32) 8 = memLoad m (q + 32) 8) (i : Nat) (hi : i < 33) :
    memLoad n (wordAddr dest 8 i) 8 = memLoad m (wordAddr q 8 i) 8 := by
  by_cases h : i = 32
  · subst i
    exact top
  let o := 8 * (i / 8)
  let k := HMod.hMod i 8
  have ho : o ∈ ([0, 8, 16, 24] : List Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, o]
    omega
  have index : o + k = i := by dsimp only [o, k]; omega
  have small : 8 * k + 8 ≤ 64 := by dsimp only [k]; omega
  have load (r : Ram) (p : BitVec 64) :
      (memLoad r (p + BitVec.ofNat 64 o) 64).extractLsb' (8*k) 8 = memLoad r (wordAddr p 8 i) 8 := by
    rw [extractLsb'_memLoad _ _ _ _ (by omega) (by decide) small]
    simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 8), BitVec.add_assoc,
      ← BitVec.ofNat_add, index, wordAddr, Nat.reduceDiv, Nat.one_mul]
  rw [← load n dest, word _ ho, load m q]

private def copyStack (m : Ram) (q dest : BitVec 64) : Ram :=
  let w := fun (i : Nat) => memLoad m (q + BitVec.ofNat 64 i) 64
  let t := memLoad m (q + 32) 8
  let m1 := memStore m (dest + 32) t
  let m2 := memStore m1 (dest + 24) (w 24)
  let m3 := memStore m2 (dest + 16) (w 16)
  let m4 := memStore m3 (dest + 8) (w 8)
  memStore m4 dest (memLoad m q 64)

private theorem copyStack_words (m : Ram) (q dest : BitVec 64) (x : Nat) (bound : x < 2^128)
    (stack : WordsAt m q 8 (Vector.ofFn fun i : Fin 33 => stackByte x 32 i.val)) :
    WordsAt (copyStack m q dest) dest 8 (Vector.ofFn fun i : Fin 33 => byte x i.val) := by
  have copied (o : Nat) (ho : o ∈ ([0, 8, 16, 24] : List Nat)) :
      memLoad (copyStack m q dest) (dest + BitVec.ofNat 64 o) 64 =
        memLoad m (q + BitVec.ofNat 64 o) 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> dsimp only [copyStack] <;> segment_words [] <;> rfl
  have top : memLoad (copyStack m q dest) (dest + 32) 8 = memLoad m (q + 32) 8 := by
    dsimp only [copyStack]
    segment_words [] <;> rfl
  intro i hi
  rw [copiedBytes copied top i hi, stack i hi]
  simp only [Vector.getElem_ofFn]
  by_cases h : i < 32
  · exact ite_eq_left h
  · have heq : i = 32 := by omega
    subst i
    have hn : nibble x 32 = 0 := by
      unfold nibble
      rw [Nat.div_eq_of_lt (show x < 16^32 from bound)]
    simp [stackByte, byte, pending, hn]

set_option maxHeartbeats 800000 in
theorem copyDigits {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    {fr : Activation} {mem m : Ram} {args : regs} {x : Nat}
    (bound : x < 2^128) (s : LoopState code fr mem m args x 32)
    (dst : Writable code mem fr.rdi 33) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l11ac3d, args, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn11aa40.doneAt fr) ∧
      out.values[0] = ⟨64, fr.rdi⟩ ∧ ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 8 (Vector.ofFn fun i : Fin 33 => byte x i.val) ∧
      RamWriteFrame mem out.store [⟨(fr.rsp - 33).toNat, 33⟩, ⟨fr.rdi.toNat, 33⟩] := by
  have atoms := s.atoms
  simp only [Fn11aa40.frameAt, Fn11aa40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, ax, bx, bp, r9, r12, r13, r14, r15, mx, ftw, fcw, rd, ret, retLow, win, room, _⟩ := atoms
  let q := fr.rsp - 33
  have spBits : args[4].get 64 = q := congrArg (Value.get 64) sp
  have axBits : args[0].get 64 = fr.rdi := congrArg (Value.get 64) ax
  have dest := dst.of_frame s.frame
  have stack : Readable m q 33 := win.readable
  have destLow := dst.readable.low
  have spLow := rd.low
  have base : q.toNat = fr.rsp.toNat - 33 := by
    change (fr.rsp - 33).toNat = _
    apply BitVec.toNat_sub_of_le
    change 33 ≤ fr.rsp.toNat
    omega
  have stackBelow : q.toNat + 33 ≤ fr.rdi.toNat := by omega
  have inc := fun v hv => included v (code_l11ac3d v hv)
  have endSp : q + 33 = fr.rsp := by dsimp only [q]; bv_omega
  have retRead : Readable m (q + 33) 8 := endSp ▸ rd
  have ret' : memLoad m (q + 33) 64 = fr.ret := endSp ▸ ret
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?rax, ?widths, ?words, ?frame⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [spBits, axBits]
    segment_words []
    simp only [ret', retLow, and_true]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using inc)
    rfl
  case tag => rfl
  case done_ =>
    refine ⟨?_, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, trivial⟩
    change Value.mk 64 (q + 41) = _
    exact congrArg (Value.mk 64) (by dsimp only [q]; bv_omega)
  case rax => exact ax
  case widths =>
    intro ⟨i, hi⟩ hm
    have hw := s.widths ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact hw
  case words =>
    exact copyStack_words m q fr.rdi x bound s.stack
  case frame =>
    change RamWriteFrame mem (copyStack m q fr.rdi) _
    have prev := s.frame
    have written : RamWriteFrame m (copyStack m q fr.rdi) [⟨fr.rdi.toNat, 33⟩] := by
      dsimp only [copyStack]
      slot_state region
    refine ((RamWriteFrame.refl mem _).trans prev ?_).trans written ?_
    · intro r hr
      rcases List.mem_singleton.mp hr with rfl
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ hr, Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply.Radix
