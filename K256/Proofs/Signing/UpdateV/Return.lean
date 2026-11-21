import K256.Proofs.Signing.UpdateV.State
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Ecdh.Output.Memory
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Verify.LIR.Fn104970

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

set_option maxHeartbeats 1000000 in
theorem returnPath {fr : Activation} {a : Values Value Reg.count} {m : Ram} {digest : ByteArray}
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32) (dataLow : fr.rdi.toNat + 64 < 2^32)
    (apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (writable : Writable Extracted.programImage fr.original fr.rdi 64)
    (frame : Frame .l104c52 fr a m) (widths : ParseSignature.ArgumentWidths a)
    (bytes : (⟨(fr.rsp - 488 + 72).toNat, 32⟩ : MemoryRegion).HasBytes m digest) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l104c52, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn104970.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat + 32, 32⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧
      (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes out.store
        digest := by
  let sp := fr.rsp - 488
  let dst := fr.rdi + 32
  let output : MemoryRegion := ⟨fr.rdi.toNat + 32, 32⟩
  have sn : sp.toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (show (488 : BitVec 64) ≤ fr.rsp from by
      change 488 ≤ fr.rsp.toNat
      omega)
  have dn : dst.toNat = fr.rdi.toNat + 32 := by
    dsimp only [dst]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rdi.toNat + 32 < 2^64; omega)]
    rfl
  have ln : fr.low.toNat = fr.rsp.toNat - 1200 := by
    rw [low]
    exact BitVec.toNat_sub_of_le (show (1200 : BitVec 64) ≤ fr.rsp from depth)
  have dstWrite : Writable Extracted.programImage m dst 32 :=
    (writable.sub (by rw [dn]; omega) (by rw [dn]; omega)).of_frame frame.writes
  have spAddr (i : Nat) (hi : i ≤ 488) :
      (sp + BitVec.ofNat 64 i).toNat = sp.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have extend {t : Ram} (f : RamWriteFrame m t [output]) (i : Nat)
      (hi : i + 8 ≤ 32) (x : BitVec 64) :
      RamWriteFrame m (memStore t (dst + BitVec.ofNat 64 i) x) [output] := by
    apply f.memStore
    refine ⟨_, List.mem_cons_self, ?_⟩
    unfold InRegion
    rw [Ecdh.Output.outputOffset dstWrite.readable.low (by omega), dn]
    change fr.rdi.toNat + 32 ≤ fr.rdi.toNat + 32 + i ∧
      fr.rdi.toNat + 32 + i + 8 ≤ fr.rdi.toNat + 32 + 32 ∧
      fr.rdi.toNat + 32 + i + 8 ≤ 2^64
    omega
  have keep {t : Ram} (f : RamWriteFrame m t [output]) (i : Nat) (hi : i ≤ 488) :
      memLoad t (sp + BitVec.ofNat 64 i) 64 = memLoad m (sp + BitVec.ofNat 64 i) 64 := by
    apply f.memLoad_eq
    refine ⟨?_, ?_⟩
    · rw [spAddr i hi]
      change sp.toNat + i + 8 ≤ 2^64
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [spAddr i hi]
      change sp.toNat + i + 8 ≤ fr.rdi.toNat + 32 ∨ fr.rdi.toNat + 32 + 32 ≤ sp.toNat + i
      omega
  let m1 := memStore m (dst + 24) (memLoad m (sp + 96) 64)
  let m2 := memStore m1 (dst + 16) (memLoad m (sp + 88) 64)
  let m3 := memStore m2 (dst + 8) (memLoad m (sp + 80) 64)
  let m4 := memStore m3 dst (memLoad m (sp + 72) 64)
  have w0 : RamWriteFrame m m [output] := .refl _ _
  have w1 : RamWriteFrame m m1 [output] := extend w0 24 (by decide) _
  have w2 : RamWriteFrame m m2 [output] := extend w1 16 (by decide) _
  have w3 : RamWriteFrame m m3 [output] := extend w2 8 (by decide) _
  have w4 : RamWriteFrame m m4 [output] := by
    simpa only [BitVec.add_zero] using extend w3 0 (by decide) (memLoad m (sp + 72) 64)
  have allWrites : RamWriteFrame fr.original m4 [fr.region, output] := by
    have base : RamWriteFrame fr.original m [fr.region, output] :=
      (RamWriteFrame.refl _ _).trans frame.writes (fun r hr =>
        ⟨r, List.mem_append_left [output] hr, Nat.le_refl _, Nat.le_refl _⟩)
    exact base.trans w4 (fun r hr => ⟨r, List.mem_cons_of_mem _ hr, Nat.le_refl _, Nat.le_refl _⟩)
  have copied : output.HasBytes m4 digest := by
    have src : (⟨(sp - 272 + 344).toNat, 32⟩ : MemoryRegion).HasBytes m digest := by
      rwa [show sp - 272 + 344 = sp + 72 by bv_omega]
    have result := Ecdh.Output.copyHasBytes src dstWrite.readable
    simp only [Ecdh.Output.copyMemory, BitVec.add_zero,
      show sp - 272 + 368 = sp + 96 by bv_omega, show sp - 272 + 360 = sp + 88 by bv_omega,
      show sp - 272 + 352 = sp + 80 by bv_omega, show sp - 272 + 344 = sp + 72 by bv_omega,
      dn] at result
    exact result
  have atoms := frame.atoms
  simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, mx, ft, fc, bx, r12, r13, r14, r15, bp, retRd, ret, retLow, stack, _⟩ := atoms
  have rspBits : a[4].get 64 = sp := congrArg (Value.get 64) rsp
  have dstBits : a[3].get 64 = dst := congrArg (Value.get 64) frame.target
  have readWord {t : Ram} (f : RamWriteFrame m t [output]) (i : Nat) (hi : i + 8 ≤ 488) :
      LoadOk t (sp + BitVec.ofNat 64 i) 8 := by
    apply LoadOk.of_region (stack.readable.of_frame f)
    · rw [spAddr i (by omega), ← low, ln]
      omega
    · rw [spAddr i (by omega), ← low, ln]
      omega
  have storeWord {t : Ram} (f : RamWriteFrame m t [output]) (i off len : Nat)
      (hi : i + 8 ≤ 32) (hc : off + len ≤ bytes_l104c52.length) :
      StoreOk Extracted.programImage t (dst + BitVec.ofNat 64 i) 8 (0x104c52 + BitVec.ofNat 64 off) len := by
    have addr := Ecdh.Output.outputOffset dstWrite.readable.low (i := i) (by omega)
    apply ParseSignature.storeOk_of_codeRange
    · exact (dstWrite.sub (by rw [addr]; omega) (by rw [addr]; omega)).of_frame f
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l104c52 x hx)
    · exact hc
  have store0 : StoreOk Extracted.programImage m (dst + 24) 8 0x104c57 4 := by
    exact storeWord w0 24 5 4 (by decide) (by decide +kernel)
  have store1 : StoreOk Extracted.programImage m1 (dst + 16) 8 0x104c60 4 := by
    exact storeWord w1 16 14 4 (by decide) (by decide +kernel)
  have store2 : StoreOk Extracted.programImage m2 (dst + 8) 8 0x104c6e 4 := by
    exact storeWord w2 8 28 4 (by decide) (by decide +kernel)
  have store3 : StoreOk Extracted.programImage m3 dst 8 0x104c72 3 := by
    change StoreOk _ _ dst 8 (0x104c52 + BitVec.ofNat 64 32) 3
    simpa only [BitVec.add_zero] using storeWord w3 0 32 3 (by decide) (by decide +kernel)
  have retAddr : sp + 488 = fr.rsp := BitVec.sub_add_cancel ..
  have popAddr : sp + 496 = fr.rsp + 8 := by dsimp only [sp]; bv_omega
  have readyRet : LoadOk m4 (sp + 488) 8 := by
    rw [retAddr]
    exact ⟨retRd.low, (retRd.of_frame w4).present⟩
  have ret' : memLoad m4 (sp + 488) 64 = fr.ret := (keep w4 488 (by decide)).trans (retAddr ▸ ret)
  have pop440 : memLoad m4 (sp + 440) 64 = fr.rbx := by
    refine (keep w4 440 (by decide)).trans ?_
    change memLoad m (sp + 440) 64 = _
    rw [show sp + 440 = fr.rsp - 48 by dsimp only [sp]; bv_omega]
    exact bx
  have pop448 : memLoad m4 (sp + 448) 64 = fr.r12 := by
    refine (keep w4 448 (by decide)).trans ?_
    change memLoad m (sp + 448) 64 = _
    rw [show sp + 448 = fr.rsp - 40 by dsimp only [sp]; bv_omega]
    exact r12
  have pop456 : memLoad m4 (sp + 456) 64 = fr.r13 := by
    refine (keep w4 456 (by decide)).trans ?_
    change memLoad m (sp + 456) 64 = _
    rw [show sp + 456 = fr.rsp - 32 by dsimp only [sp]; bv_omega]
    exact r13
  have pop464 : memLoad m4 (sp + 464) 64 = fr.r14 := by
    refine (keep w4 464 (by decide)).trans ?_
    change memLoad m (sp + 464) 64 = _
    rw [show sp + 464 = fr.rsp - 24 by dsimp only [sp]; bv_omega]
    exact r14
  have pop472 : memLoad m4 (sp + 472) 64 = fr.r15 := by
    refine (keep w4 472 (by decide)).trans ?_
    change memLoad m (sp + 472) 64 = _
    rw [show sp + 472 = fr.rsp - 16 by dsimp only [sp]; bv_omega]
    exact r15
  have pop480 : memLoad m4 (sp + 480) 64 = fr.rbp := by
    refine (keep w4 480 (by decide)).trans ?_
    change memLoad m (sp + 480) 64 = _
    rw [show sp + 480 = fr.rsp - 8 by dsimp only [sp]; bv_omega]
    exact bp
  have load96 : LoadOk m (sp + 96) 8 := readWord w0 96 (by decide)
  have load88 : LoadOk m1 (sp + 88) 8 := readWord w1 88 (by decide)
  have keep88 : memLoad m1 (sp + 88) 64 = memLoad m (sp + 88) 64 := keep w1 88 (by decide)
  have load72 : LoadOk m2 (sp + 72) 8 := readWord w2 72 (by decide)
  have keep72 : memLoad m2 (sp + 72) 64 = memLoad m (sp + 72) 64 := keep w2 72 (by decide)
  have load80 : LoadOk m2 (sp + 80) 8 := readWord w2 80 (by decide)
  have keep80 : memLoad m2 (sp + 80) 64 = memLoad m (sp + 80) 64 := keep w2 80 (by decide)
  have load440 : LoadOk m4 (sp + 440) 8 := readWord w4 440 (by decide)
  have load448 : LoadOk m4 (sp + 448) 8 := readWord w4 448 (by decide)
  have load456 : LoadOk m4 (sp + 456) 8 := readWord w4 456 (by decide)
  have load464 : LoadOk m4 (sp + 464) 8 := readWord w4 464 (by decide)
  have load472 : LoadOk m4 (sp + 472) 8 := readWord w4 472 (by decide)
  have load480 : LoadOk m4 (sp + 480) 8 := readWord w4 480 (by decide)
  refine ⟨?_, .done ?run, ?tag, ?done_, ?writes, ?widths, ?digest⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rspBits, dstBits, load96, store0,
      show memStore m (dst + 24) (memLoad m (sp + 96) 64) = m1 from rfl,
      load88, keep88, store1,
      show memStore m1 (dst + 16) (memLoad m (sp + 88) 64) = m2 from rfl,
      load72, load80, keep72,
      keep80, store2,
      show memStore m2 (dst + 8) (memLoad m (sp + 80) 64) = m3 from rfl, store3,
      show memStore m3 dst (memLoad m (sp + 72) 64) = m4 from rfl,
      load440, load448, load456,
      load464, load472, load480,
      readyRet, ret', retLow, and_self, pop440, pop448, pop456, pop464, pop472, pop480,
      popAddr, ↓reduceIte]
    rfl
  case tag => rfl
  case done_ => exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ft, fc, trivial⟩
  case writes => exact allWrites
  case widths =>
    rintro ⟨i, hi⟩ h
    have incoming := widths ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact incoming
  case digest => exact copied

end K256.Proofs.Signing.UpdateV
