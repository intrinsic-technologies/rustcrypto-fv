import AesGcm.Proofs.AES16.Encrypt.Calls
import AesGcm.Proofs.AES16.Encrypt.Initial
import AesGcm.Proofs.AES16.Input
import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option hygiene false in
local macro "prefix_proof" u:term "," entry:term "," keyentry:term "," loophead:term ","
    win:num "," depth:num "," cp:num "," buf:num "," off:num "," kbytes:num ","
    klen:num "," slot:num "," keydepth:num "," ro:num "," pc:num "," len:num ","
    ret:num "," codeLemma:ident : tactic =>
  `(tactic| (
    revert hframe htyped
    refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
      a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
    clear args
    intro htyped hframe
    change a4 = ⟨64, fr.rsp⟩ ∧ a22 = ⟨1, 0⟩ ∧ a1 = ⟨64, fr.rcx⟩ ∧
      a2 = ⟨64, fr.rdx⟩ ∧ a3 = ⟨64, fr.rbx⟩ ∧ a5 = ⟨64, fr.rbp⟩ ∧
      a6 = ⟨64, fr.rsi⟩ ∧ a7 = ⟨64, fr.rdi⟩ ∧ a8 = ⟨64, fr.r8⟩ ∧ a9 = ⟨64, fr.r9⟩ ∧
      a12 = ⟨64, fr.r12⟩ ∧ a13 = ⟨64, fr.r13⟩ ∧ a14 = ⟨64, fr.r14⟩ ∧ a15 = ⟨64, fr.r15⟩ ∧
      a39 = ⟨32, fr.mxcsr⟩ ∧ a50 = ⟨16, fr.ftw⟩ ∧ a51 = ⟨16, fr.fcw⟩ ∧
      Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
      fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - $win) $win ∧
      fr.low.toNat + $win ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable fr.original 0x201210 8 ∧ memLoad fr.original 0x201210 64 = 0x103880 ∧
      Readable fr.original 0x201230 8 ∧ memLoad fr.original 0x201230 64 = 0x101230 ∧
      ($ro ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) ∧ True at hframe
    rcases hframe with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, hRetRead, hRet, hRetLow, hStack, hRoom, hAlign,
      hRoRead0, hRo0, hRoRead1, hRo1, hRoApart, -⟩
    have hTypes := htyped
    have hStackRead := hStack.readable
    have hStackLow := hStackRead.low
    have hRetReadLow := hRetRead.low
    have hInputReadLow := hReadInput.low
    have hKeyReadLow := hReadKey.low
    have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n $pc $len := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x ($codeLemma:ident x hx))
      change StoreOk code m a n $pc $len at hx
      exact hx.apart
    let cont : LIR.lifted.StackFrame :=
      {target := $keyentry, kept := #v[], arity := rfl, guard := some ⟨64, $ret⟩}
    obtain ⟨ca, hCall, hCaLabel, hCa4, hCa2, hCa3, hCa6, hCa7, hCa22,
      hCa39, hCa50, hCa51, hCaTyped, hCaFrame, hCaRet,
      hSavedOut, hSaved3, hSaved12, hSaved13, hSaved14, hSaved15, hSaved5⟩ :
        ∃ ca : LIR.lifted.Location,
          LIR.program.runBlock (dialect code)
            ⟨$entry, #v[a0, ⟨64, fr.rcx⟩, ⟨64, fr.rdx⟩, ⟨64, fr.rbx⟩, ⟨64, fr.rsp⟩,
              ⟨64, fr.rbp⟩, ⟨64, fr.rsi⟩, ⟨64, fr.rdi⟩, ⟨64, fr.r8⟩, ⟨64, fr.r9⟩,
              a10, a11, ⟨64, fr.r12⟩, ⟨64, fr.r13⟩, ⟨64, fr.r14⟩, ⟨64, fr.r15⟩,
              a16, a17, a18, a19, a20, a21, ⟨1, 0⟩, a23, a24, a25, a26, a27, a28,
              a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, ⟨32, fr.mxcsr⟩,
              a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, ⟨16, fr.ftw⟩,
              ⟨16, fr.fcw⟩, a52], fr.original⟩ = .call ca cont ∧
          ca.label = .l109ff0 ∧
          ca.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - $cp⟩ ∧
          ca.arguments[2]'(by change 2 < 53; decide) = ⟨64, fr.rdx⟩ ∧
          ca.arguments[3]'(by change 3 < 53; decide) = ⟨64, fr.rsi⟩ ∧
          ca.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
          ca.arguments[7]'(by change 7 < 53; decide) = ⟨64, fr.rsp - $buf⟩ ∧
          ca.arguments[22]'(by change 22 < 53; decide) = ⟨1, 0⟩ ∧
          ca.arguments[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ ∧
          ca.arguments[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ ∧
          ca.arguments[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ ∧
          GPRsTyped ca.arguments ∧
          RamWriteFrame fr.original ca.store [span (fr.rsp - $win) $win] ∧
          memLoad ca.store (fr.rsp - $cp) 64 = $ret ∧
          memLoad ca.store (fr.rsp - 56) 64 = fr.rdi ∧
          memLoad ca.store (fr.rsp - 48) 64 = fr.rbx ∧
          memLoad ca.store (fr.rsp - 40) 64 = fr.r12 ∧
          memLoad ca.store (fr.rsp - 32) 64 = fr.r13 ∧
          memLoad ca.store (fr.rsp - 24) 64 = fr.r14 ∧
          memLoad ca.store (fr.rsp - 16) 64 = fr.r15 ∧
          memLoad ca.store (fr.rsp - 8) 64 = fr.rbp := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left
      · cfg_eval
        runtime_guards transfer
        rfl
      all_goals first | rfl | runtime_typed | runtime_finish [span]
    rcases ca with ⟨caLabel, caArgs, caMem⟩
    dsimp only at hCaLabel hCall hCa4 hCa2 hCa3 hCa6 hCa7 hCa22
    dsimp only at hCa39 hCa50 hCa51 hCaTyped hCaFrame hCaRet
    dsimp only at hSavedOut hSaved3 hSaved12 hSaved13 hSaved14 hSaved15 hSaved5
    subst caLabel
    change Values Value Reg.count at caArgs
    have hBottom : (fr.rsp - $win).toNat = fr.rsp.toNat - $win := by bv_omega
    have hPreciseRoom := precise_room $u fr hRoom
    have hChildRoomPre : (preciseActivation $u fr).low.toNat + (frameInfo $u).window ≤
        (preciseActivation $u fr).rsp.toNat := Nat.le_of_eq hPreciseRoom
    obtain ⟨hSpBound, hCallSp, hBuf, hReadCall, hWriteCall, hChildRoom,
      hChildAlign, hChildApart, hChildWithin, hSavedOutside⟩ :=
      call_geometry $u code caMem (preciseActivation $u fr) 208 (by decide)
        (hStack.of_frame hCaFrame) hChildRoomPre hAlign
    change (fr.rsp - $cp).toNat = fr.rsp.toNat - $cp at hCallSp
    change (fr.rsp - $buf).toNat = fr.rsp.toNat - $buf at hBuf
    change Readable caMem (fr.rsp - $cp) 8 at hReadCall
    change Writable code caMem (fr.rsp - $cp - 208) 208 at hWriteCall
    change (fr.rsp - $win).toNat + 208 ≤ (fr.rsp - $cp).toNat at hChildRoom
    change (fr.rsp - $cp).toNat % 16 = 8 at hChildAlign
    change (⟨(fr.rsp - $win).toNat,
      (fr.rsp - $cp).toNat + 8 - (fr.rsp - $win).toNat⟩ : MemoryRegion).Disjoint
        (span (fr.rsp - $buf) 16) at hChildApart
    have hPreciseRegion : (preciseActivation $u fr).region =
        span (fr.rsp - $win) $win := by
      change (⟨(fr.rsp - $win).toNat,
        fr.rsp.toNat - (fr.rsp - $win).toNat⟩ : MemoryRegion) = _
      congr 1
      omega
    rw [hPreciseRegion] at hChildWithin
    change RegionsWithin
      [⟨(fr.rsp - $win).toNat, (fr.rsp - $cp).toNat - (fr.rsp - $win).toNat⟩,
        span (fr.rsp - $buf) 16, span (fr.rsp - $cp) 8]
      [span (fr.rsp - $win) $win] at hChildWithin
    change ∀ k : Nat, k ≤ 72 → Outside
      [⟨(fr.rsp - $win).toNat, (fr.rsp - $cp).toNat - (fr.rsp - $win).toNat⟩,
        span (fr.rsp - $buf) 16, span (fr.rsp - $cp) 8]
      (fr.rsp - BitVec.ofNat 64 k) 8 at hSavedOutside
    have hDepth : (fr.rsp - $depth).toNat = fr.rsp.toNat - $depth := by
      exact BitVec.toNat_sub_of_le (by change $depth ≤ fr.rsp.toNat; omega)
    have hRootLow : fr.low.toNat ≤ (fr.rsp - $win).toNat := by rw [hBottom]; omega
    have hInputApartNum : fr.rsp.toNat + 8 ≤ fr.rdx.toNat ∨
        fr.rdx.toNat + 16 ≤ fr.low.toNat := by
      have h := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        fr.rdx.toNat 16 (by omega) (by decide) hInputApart
      omega
    have hKeyApartNum : fr.rsp.toNat + 8 ≤ fr.rsi.toNat ∨
        fr.rsi.toNat + $kbytes ≤ fr.low.toNat := by
      have h := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        fr.rsi.toNat $kbytes (by omega) (by decide) hKeyApart
      omega
    have hRoOutside (a : BitVec 64) (hlo : 0x201210 ≤ a.toNat)
        (hhi : a.toNat + 8 ≤ 0x201238) : Outside [span (fr.rsp - $win) $win] a 8 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      have he := List.mem_singleton.mp hr
      subst r
      simp (config := { bitVecOfNat := false }) only [span]
      omega
    obtain ⟨out, hInputExec, hInputTag, hInputDone, hInputTyped, hInputFrame,
      hInputPost⟩ := callContract_exec_values LIR.lifted code .l109ff0
      LIR.Fn109ff0.frameInfo _ _ _ (input_call code hcode) caMem caArgs
      $ret (fr.rsp - $win) hCaTyped
      (by rw [hCa39]; rfl) (by rw [hCa50]; rfl) (by rw [hCa51]; rfl) hCa22
      (by rw [hCa4]; exact hReadCall)
      (by rw [hCa4]; exact hCaRet) (by decide)
      (by intro _; rw [hCa4]; exact hWriteCall)
      (by rw [hCa4]; exact hChildRoom)
      (by rw [hCa4]; exact hChildAlign)
      (by
        change Readable caMem 0x201210 8 ∧ memLoad caMem 0x201210 64 = 0x103880 ∧
          Readable caMem 0x201230 8 ∧ memLoad caMem 0x201230 64 = 0x101230 ∧
          (0x201238 + 208 ≤ ((caArgs[4]).get 64).toNat ∨
            ((caArgs[4]).get 64).toNat ≤ 0x201210) ∧ True
        refine ⟨hRoRead0.of_frame hCaFrame,
          (hCaFrame.memLoad_eq (hRoOutside _ (by decide) (by decide))).trans hRo0,
          hRoRead1.of_frame hCaFrame,
          (hCaFrame.memLoad_eq (hRoOutside _ (by decide) (by decide))).trans hRo1, ?_, trivial⟩
        rw [hCa4]
        change 0x201238 + 208 ≤ (fr.rsp - $cp).toNat ∨ (fr.rsp - $cp).toNat ≤ 0x201210
        omega)
      (by
        dsimp only [activationOfValues]
        rw [hCa2, hCa4, hCa6, hCa7]
        simp (config := { bitVecOfNat := false }) only [Value.get, BitVec.setWidth_eq]
        refine ⟨trivial, hReadInput.of_frame hCaFrame, ?_, ?_, ?_, ?_⟩
        · exact (hStack.of_frame hCaFrame).of_offsets
            (addr_sub _ _) (addr_sub _ _) (by decide)
        · exact hChildApart
        · intro x hx hy
          change (fr.rsp - $win).toNat ≤ x ∧
            x < (fr.rsp - $win).toNat + ((fr.rsp - $cp).toNat + 8 - (fr.rsp - $win).toNat) at hx
          change fr.rdx.toNat ≤ x ∧ x < fr.rdx.toNat + 16 at hy
          omega
        · intro x hx hy
          change (fr.rsp - $buf).toNat ≤ x ∧ x < (fr.rsp - $buf).toNat + 16 at hx
          change fr.rdx.toNat ≤ x ∧ x < fr.rdx.toNat + 16 at hy
          omega)
    change out.values[4] = ⟨64, (caArgs[4]'(by change 4 < 53; decide)).get 64 + 8⟩ ∧
      out.values[22] = ⟨1, 0⟩ ∧
      out.values[3] = ⟨64, (caArgs[3]'(by change 3 < 53; decide)).get 64⟩ ∧
      out.values[5] = ⟨64, (caArgs[5]'(by change 5 < 53; decide)).get 64⟩ ∧
      out.values[12] = ⟨64, (caArgs[12]'(by change 12 < 53; decide)).get 64⟩ ∧
      out.values[13] = ⟨64, (caArgs[13]'(by change 13 < 53; decide)).get 64⟩ ∧
      out.values[14] = ⟨64, (caArgs[14]'(by change 14 < 53; decide)).get 64⟩ ∧
      out.values[15] = ⟨64, (caArgs[15]'(by change 15 < 53; decide)).get 64⟩ ∧
      out.values[39] = ⟨32, (caArgs[39]'(by change 39 < 53; decide)).get 32⟩ ∧
      out.values[50] = ⟨16, (caArgs[50]'(by change 50 < 53; decide)).get 16⟩ ∧
      out.values[51] = ⟨16, (caArgs[51]'(by change 51 < 53; decide)).get 16⟩ ∧ True at hInputDone
    rcases hInputDone with ⟨hOut4, hOut22, hOut3, hOut5, hOut12, hOut13,
      hOut14, hOut15, hOut39, hOut50, hOut51, -⟩
    rw [hCa4] at hOut4
    rw [hCa3] at hOut3
    rw [hCa39] at hOut39
    rw [hCa50] at hOut50
    rw [hCa51] at hOut51
    change out.values[4] = ⟨64, fr.rsp - $cp + 8⟩ at hOut4
    change out.values[3] = ⟨64, fr.rsi⟩ at hOut3
    change out.values[39] = ⟨32, fr.mxcsr⟩ at hOut39
    change out.values[50] = ⟨16, fr.ftw⟩ at hOut50
    change out.values[51] = ⟨16, fr.fcw⟩ at hOut51
    have hOutSp : out.values[4] = ⟨64, fr.rsp - $depth⟩ := by
      rw [hOut4]
      congr 1
      bv_omega
    change RamWriteFrame caMem out.store
      [(activationOfValues caMem caArgs $ret (fr.rsp - $win)).region,
        span (activationOfValues caMem caArgs $ret (fr.rsp - $win)).rdi 16]
      at hInputFrame
    dsimp only [activationOfValues, Activation.region] at hInputFrame
    rw [hCa4, hCa7] at hInputFrame
    change RamWriteFrame caMem out.store
      [⟨(fr.rsp - $win).toNat, (fr.rsp - $cp).toNat - (fr.rsp - $win).toNat⟩,
        span (fr.rsp - $buf) 16] at hInputFrame
    have hWindowWithin := precise_within $u fr hRoom
    rw [hPreciseRegion] at hWindowWithin
    have hInputWindow : RamWriteFrame caMem out.store [span (fr.rsp - $win) $win] := by
      apply (RamWriteFrame.refl caMem [span (fr.rsp - $win) $win]).trans hInputFrame
      intro r hr
      apply hChildWithin r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    have hBeforeKeyWindow := hCaFrame.trans hInputWindow
      (by intro r hr; exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
    have hBeforeKey : RamWriteFrame fr.original out.store [fr.region] :=
      (RamWriteFrame.refl fr.original [fr.region]).trans hBeforeKeyWindow hWindowWithin
    have hKeyOutside := key_outside (by omega : fr.low.toNat ≤ fr.rsp.toNat)
      hReadKey hKeyApart
    have hScheduleOut := scheduleIn_of_frame hSchedule hBeforeKey hKeyOutside
    have hReadKeyOut := hReadKey.of_frame hBeforeKey
    have hStackOut := hStack.of_frame hBeforeKey
    have hInputCa : Fixslice.memoryBlock caMem fr.rdx = fromStandard input := by
      rw [← hInput]
      funext i
      have hi := i.isLt
      have ha : (fr.rdx + BitVec.ofNat 64 i.val).toNat = fr.rdx.toNat + i.val := by
        bv_omega
      have he : memLoad caMem (fr.rdx + BitVec.ofNat 64 i.val) 8 =
          memLoad fr.original (fr.rdx + BitVec.ofNat 64 i.val) 8 := by
        apply hCaFrame.memLoad_eq
        refine ⟨by rw [ha]; omega, ?_⟩
        intro r hr
        have her := List.mem_singleton.mp hr
        subst r
        simp only [span, ha]
        omega
      simpa only [Fixslice.memoryBlock, memLoad_8] using he
    change WordsAt out.store ((caArgs[7]).get 64) 16
      (Vector.ofFn (encode (Fixslice.memoryBlock caMem ((caArgs[2]).get 64)))) at hInputPost
    rw [hCa7, hCa2] at hInputPost
    change WordsAt out.store (fr.rsp - $buf) 16
      (Vector.ofFn (encode (Fixslice.memoryBlock caMem fr.rdx))) at hInputPost
    rw [hInputCa] at hInputPost
    change WordsAt out.store (fr.rsp - $buf) 16 (Vector.ofFn (encodeStandard input))
      at hInputPost
    have hKeyWords := hScheduleOut.words ⟨0, by decide⟩
    simp (config := { bitVecOfNat := false }) only [Nat.mul_zero, BitVec.reduceOfNat,
      add_zero_lit] at hKeyWords
    obtain ⟨next, hKeyRun, hNextLabel, hNext4, hNext3, hNext12, hNextTail,
      hNext22, hNext39, hNext50, hNext51, hNextTyped, hNextWords,
      hKeySlot, hKeyFrame⟩ := key0_runBlock $u code hcode out.values out.store
      (encodeStandard input) (expectedKey (variant $u) key ⟨0, by decide⟩) hInputTyped
      (by
        rw [hOutSp]
        exact hStackOut.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by
        rw [hOut3]
        exact hReadKeyOut.of_offsets (addr_self _) (addr_self _) (by decide))
      (by
        rw [hOutSp, hOut3]
        change (fr.rsp - $depth).toNat + $klen ≤ fr.rsi.toNat ∨
          fr.rsi.toNat + 16 ≤ (fr.rsp - $depth).toNat
        omega)
      (by
        rw [hOutSp]
        simpa only [Value.get, BitVec.setWidth_eq, Bool.false_eq_true, ↓reduceIte,
          show fr.rsp - $depth + $off = fr.rsp - $buf by bv_omega] using hInputPost)
      (by rw [hOut3]; exact hKeyWords)
    rw [hOutSp] at hNext4 hKeySlot hKeyFrame hNextWords
    rw [hOut3] at hNext3 hKeySlot
    rw [hOut22] at hNext22
    rw [hOut39] at hNext39
    rw [hOut50] at hNext50
    rw [hOut51] at hNext51
    change RamWriteFrame out.store next.store [span (fr.rsp - $depth) $klen] at hKeyFrame
    change memLoad next.store (fr.rsp - $depth + $slot) 64 = fr.rsi at hKeySlot
    change WordsAt next.store (fr.rsp - $depth + $off) 16
      (Vector.ofFn fun p : Fin 8 ↦ if p.val = 7 then encodeStandard input p
        else encodeStandard input p ^^^ expectedKey (variant $u) key ⟨0, by decide⟩ p)
      at hNextWords
    rcases next with ⟨nextLabel, nextArgs, nextMem⟩
    dsimp only at hKeyRun hNextLabel hNext4 hNext3 hNext12 hNextTail
    dsimp only at hNext22 hNext39 hNext50 hNext51 hNextTyped hNextWords
    dsimp only at hKeySlot hKeyFrame
    subst nextLabel
    change Values Value Reg.count at nextArgs
    change LIR.program.runBlock (dialect code) ⟨$keyentry, out.values, out.store⟩ =
      .jump ⟨$loophead, nextArgs, nextMem⟩ at hKeyRun
    have hSavedAfter (k : Nat) (hk : k ≤ 56) :
        memLoad nextMem (fr.rsp - BitVec.ofNat 64 k) 64 =
          memLoad caMem (fr.rsp - BitVec.ofNat 64 k) 64 := by
      have ho := hSavedOutside k (by omega)
      have hkn : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
        have hks : BitVec.ofNat 64 k ≤ fr.rsp := by
          change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        rw [BitVec.toNat_sub_of_le hks, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      calc
        memLoad nextMem (fr.rsp - BitVec.ofNat 64 k) 64 =
            memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 := by
          apply hKeyFrame.memLoad_eq
          refine ⟨ho.1, ?_⟩
          intro r hr
          have he := List.mem_singleton.mp hr
          subst r
          right
          simp only [span, hkn, hDepth]
          omega
        _ = memLoad caMem (fr.rsp - BitVec.ofNat 64 k) 64 := by
          apply hInputFrame.memLoad_eq
          refine ⟨ho.1, ?_⟩
          intro r hr
          apply ho.2 r
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          exact hr.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    have hKeyWindow : RamWriteFrame out.store nextMem [span (fr.rsp - $win) $win] := by
      apply (RamWriteFrame.refl out.store [span (fr.rsp - $win) $win]).trans hKeyFrame
      intro r hr
      have he := List.mem_singleton.mp hr
      subst r
      refine ⟨span (fr.rsp - $win) $win, by simp, ?_, ?_⟩
      all_goals simp only [span]; omega
    have hTotalWindow := hBeforeKeyWindow.trans hKeyWindow
      (by intro r hr; exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
    have hTotal : RamWriteFrame fr.original nextMem [fr.region] :=
      (RamWriteFrame.refl fr.original [fr.region]).trans hTotalWindow hWindowWithin
    have hRetFinal : memLoad nextMem fr.rsp 64 = fr.ret := by
      rw [hTotalWindow.memLoad_eq ⟨by omega, ?_⟩, hRet]
      intro r hr
      have he := List.mem_singleton.mp hr
      subst r
      right
      simp only [span]
      omega
    have hFrameFinal : Atom.All code nextArgs nextMem (frameAt $u $loophead fr) := by
      change nextArgs[4] = ⟨64, fr.rsp - $depth⟩ ∧ nextArgs[22] = ⟨1, 0⟩ ∧
        nextArgs[3] = ⟨64, fr.rsi⟩ ∧ nextArgs[39] = ⟨32, fr.mxcsr⟩ ∧
        nextArgs[50] = ⟨16, fr.ftw⟩ ∧ nextArgs[51] = ⟨16, fr.fcw⟩ ∧
        memLoad nextMem (fr.rsp - $keydepth) 64 = fr.rsi ∧
        memLoad nextMem (fr.rsp - 56) 64 = fr.rdi ∧
        memLoad nextMem (fr.rsp - 48) 64 = fr.rbx ∧
        memLoad nextMem (fr.rsp - 40) 64 = fr.r12 ∧
        memLoad nextMem (fr.rsp - 32) 64 = fr.r13 ∧
        memLoad nextMem (fr.rsp - 24) 64 = fr.r14 ∧
        memLoad nextMem (fr.rsp - 16) 64 = fr.r15 ∧
        memLoad nextMem (fr.rsp - 8) 64 = fr.rbp ∧
        Readable nextMem fr.rsp 8 ∧ memLoad nextMem fr.rsp 64 = fr.ret ∧
        fr.ret.toNat < 2^32 ∧ Writable code nextMem (fr.rsp - $win) $win ∧
        fr.low.toNat + $win ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
        Readable nextMem 0x201210 8 ∧ memLoad nextMem 0x201210 64 = 0x103880 ∧
        Readable nextMem 0x201230 8 ∧ memLoad nextMem 0x201230 64 = 0x101230 ∧
        ($ro ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) ∧ True
      refine ⟨hNext4, hNext22, hNext3, hNext39, hNext50, hNext51, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRetRead.of_frame hTotalWindow, hRetFinal, hRetLow,
        hStack.of_frame hTotalWindow, hRoom, hAlign,
        hRoRead0.of_frame hTotalWindow, ?_, hRoRead1.of_frame hTotalWindow, ?_,
        hRoApart, trivial⟩
      · rw [show fr.rsp - $depth + $slot = fr.rsp - $keydepth by bv_omega] at hKeySlot
        exact hKeySlot
      · exact (hSavedAfter 56 (by decide)).trans hSavedOut
      · exact (hSavedAfter 48 (by decide)).trans hSaved3
      · exact (hSavedAfter 40 (by decide)).trans hSaved12
      · exact (hSavedAfter 32 (by decide)).trans hSaved13
      · exact (hSavedAfter 24 (by decide)).trans hSaved14
      · exact (hSavedAfter 16 (by decide)).trans hSaved15
      · exact (hSavedAfter 8 (by decide)).trans hSaved5
      · exact (hTotalWindow.memLoad_eq (hRoOutside _ (by decide) (by decide))).trans hRo0
      · exact (hTotalWindow.memLoad_eq (hRoOutside _ (by decide) (by decide))).trans hRo1
    have hDelayed : delayedPlanes (roundState (variant $u) key input 0)
        (expectedKey (variant $u) key ⟨0, by decide⟩) =
        (fun p : Fin 8 ↦ if p.val = 7 then encodeStandard input p
          else encodeStandard input p ^^^ expectedKey (variant $u) key ⟨0, by decide⟩ p) := by
      rw [← initial_roundState]
      funext p
      simp only [delayedPlanes, xorPlanes]
      split
      · simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      · rfl
    have hResume := CFGCall.exec_reaches_resume hInputExec cont []
      (by rw [hInputTag]; rfl)
    change (LIR.program.sem (dialect code)).Reaches
      ⟨⟨.l109ff0, caArgs, caMem⟩, [cont]⟩ ⟨⟨$keyentry, out.values, out.store⟩, []⟩ at hResume
    refine ⟨⟨$loophead, nextArgs, nextMem⟩, ?_, ?_, ?_⟩
    · apply Semantics.Reaches.trans (Semantics.Reaches.single ?_) (hResume.trans
        (Semantics.Reaches.single ?_))
      · change LIR.program.step (dialect code) ⟨⟨$entry, _, fr.original⟩, []⟩ =
          .next ⟨⟨.l109ff0, caArgs, caMem⟩, [cont]⟩
        rw [Program.step, hCall]
        rfl
      · change LIR.program.step (dialect code) ⟨⟨$keyentry, out.values, out.store⟩, []⟩ =
          .next ⟨⟨$loophead, nextArgs, nextMem⟩, []⟩
        rw [Program.step, hKeyRun]
        rfl
    · exact ⟨hFrameFinal, hNextTyped, scheduleIn_of_frame hSchedule hTotal hKeyOutside,
        hReadKey.of_frame hTotal, hStack.of_frame hTotal, hTotal⟩
    · refine ⟨rfl, hNext12, ?_, ?_⟩
      · rw [show fr.rsp - $depth + $off = fr.rsp - $buf by bv_omega] at hNextWords
        simpa only [buffer, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, hDelayed,
          add_zero_lit] using hNextWords
      · simpa only [Nat.mul_zero, hDelayed, show (7 : Fin 8).val = 7 from rfl,
          ite_true] using hNextTail
  ))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
private theorem prefix128_exec (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant false).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = entryLabel false) (hstore : loc.store = fr.original)
    (hframe : Atom.All code loc.arguments loc.store ((frameInfo false).entryAtoms fr))
    (htyped : GPRsTyped loc.arguments) (hpre : Pre code false key input fr fr.original) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      WorkingState code false key fr next ∧
      LoopState false key input fr 0 (by omega) next := by
  rcases loc with ⟨lab, args, mem⟩
  dsimp only at hlabel hstore hframe htyped ⊢
  subst lab mem
  rcases hpre with ⟨hSchedule, hReadKey, hReadInput, hInput, hOutWrite,
    hOutApart, hInputApart, hKeyApart⟩
  prefix_proof false, LIR.Label.l105100, LIR.Label.l105134, LIR.Label.l105180,
    352, 104, 112, 104, 0, 176, 48, 40, 64, 0x201398, 0x105100, 52,
    0x105134, LIR.code_l105100

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
private theorem prefix256_exec (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant true).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = entryLabel true) (hstore : loc.store = fr.original)
    (hframe : Atom.All code loc.arguments loc.store ((frameInfo true).entryAtoms fr))
    (htyped : GPRsTyped loc.arguments) (hpre : Pre code true key input fr fr.original) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      WorkingState code true key fr next ∧
      LoopState true key input fr 0 (by omega) next := by
  rcases loc with ⟨lab, args, mem⟩
  dsimp only at hlabel hstore hframe htyped ⊢
  subst lab mem
  rcases hpre with ⟨hSchedule, hReadKey, hReadInput, hInput, hOutWrite,
    hOutApart, hInputApart, hKeyApart⟩
  prefix_proof true, LIR.Label.l106960, LIR.Label.l106997, LIR.Label.l1069f0,
    368, 120, 128, 112, 8, 240, 56, 48, 72, 0x2013a8, 0x106960, 55,
    0x106997, LIR.code_l106960

theorem prefix_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = entryLabel use256) (hstore : loc.store = fr.original)
    (hframe : Atom.All code loc.arguments loc.store ((frameInfo use256).entryAtoms fr))
    (htyped : GPRsTyped loc.arguments) (hpre : Pre code use256 key input fr fr.original) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      WorkingState code use256 key fr next ∧
      LoopState use256 key input fr 0 (by omega) next := by
  cases use256
  · exact prefix128_exec code hcode key input fr loc hlabel hstore hframe htyped hpre
  · exact prefix256_exec code hcode key input fr loc hlabel hstore hframe htyped hpre

end AesGcm.Proofs.Machine.AES16.Encrypt
