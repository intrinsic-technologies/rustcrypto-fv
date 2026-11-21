import K256.Proofs.Ecdh.Wrapper.Tables.Resume
import K256.Proofs.Ecdh.Wrapper.Tables.Copies
import K256.Proofs.Ecdh.Wrapper.Child
import K256.Proofs.Ecdh.Wrapper.AffineMemory
import K256.Proofs.Ecdh.CallSite

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Tables
open Generate.Generator.Multiply.Caller (memcpyPreserved)

set_option maxRecDepth 4096 in
theorem initializeTables {s : RamState} {secret key : ByteArray} {d : Nat} {peer : Generate.Generator.Multiply.Projective}
    {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (copy : a[13] = ⟨64, 0x12a820⟩) (pair : a[14] = ⟨64, localSp s + 0xc0⟩)
    (scalar : ScalarAt s m 0x138 d) (source : peer.Stored m (localSp s + 0xc0)) :
    ∃ b n, Reaches .l1018b0 a m .l101a65 b n ∧ Caller s b n ∧
      b[14] = ⟨64, localSp s + 0xc0⟩ ∧ b[15] = ⟨64, localSp s + 0x1058⟩ ∧
      ScalarAt s n 0x138 d ∧ peer.Stored n (localSp s + 0xc0) := by
  let sp := localSp s
  let init := Tables.identityCopies m sp 16
  let left := callMemory init sp 0x101a3c 344 2264 960
  let right := callMemory left sp 0x101a4f 1304 3224 960
  obtain ⟨depth, high, top⟩ := Scalar.stack_geometry call
  have low : sp.toNat + 6104 < 2^64 := by dsimp only [sp]; omega
  have room : 8 ≤ sp.toNat := by dsimp only [sp]; omega
  have fi : RamWriteFrame m init (writes sp) := identityFrame low 16 (by decide)
  have fl : RamWriteFrame m left (writes sp) := callMemoryFrame low room fi _ (by decide) (by decide)
  have fr : RamWriteFrame m right (writes sp) := callMemoryFrame low room fl _ (by decide) (by decide)
  have win : Writable Extracted.programImage m (sp - 8) 6112 :=
    (state.toMemory.window call).of_offsets (addr_sub sp 8) (addr_sub sp 3936) (by decide)
  have push {n : Ram} (f : RamWriteFrame m n (writes sp)) (base : BitVec 64) (bytes : List UInt8)
      (off : Nat) (code : ∀ x ∈ codeRange base bytes, x ∈ fnCode)
      (fits : off + 3 ≤ bytes.length) (ret : BitVec 64) :
      StoreOk Extracted.programImage n (sp - 8) 8 (base + BitVec.ofNat 64 off) 3 := by
    rw [show sp - 8 = s.regValue .rsp - 6160 from localSp_sub_eight s]
    exact (callSite call (tableMemory call state.toMemory f) 6160 (by decide) (by decide)
      base bytes off 3 (fun x hx => Common.fnCode_subset_programImage x (code x hx)) fits ret).1
  obtain ⟨b, block₁, bs, bd, br, bn, b12, b15, kept₁⟩ := identityCopyCall
    (win.sub (Nat.le_refl _) (by omega)) (loaded_of_stackFrame call state.frame)
    (congrArg (Value.get 64) state.rsp) (congrArg (Value.get 64) copy) (congrArg (Value.get 1) state.df)
    (push fi _ _ 393 code_l1018b0 (by decide +kernel) 0x101a3c)
  have bdf := (kept₁ 22 (by decide) (by decide) (by decide)).trans state.df
  have b9 := congrArg Value.width (kept₁ 9 (by decide) (by decide) (by decide))
  obtain ⟨c, path₁, cs, _, back₁⟩ := resume (dst := 344) (src := 2264) (len := 960)
    (win.of_frame fi) (by decide) (by decide) (by decide) (by decide) block₁ bs bd br bn
    (congrArg (Value.get 1) bdf) (b9.trans (state.widths 9 (by decide)))
  have c12 := (back₁ 12 (by decide)).trans b12
  have c15 := (back₁ 15 (by decide)).trans b15
  have keepC (i : Fin Reg.count) (h : i.val ∈ memcpyPreserved) (h₁ : i.val ≠ 12) (h₂ : i.val ≠ 15) :
      c[i] = a[i] := (back₁ i h).trans (kept₁ i h h₁ h₂)
  have c13 := (keepC 13 (by decide) (by decide) (by decide)).trans copy
  obtain ⟨e, block₂, es, ed, er, en, kept₂⟩ := copyRightCall (congrArg (Value.get 64) cs)
    (congrArg (Value.get 64) c13) (congrArg (Value.get 64) c15)
    (push fl _ _ 16 code_l101a3c (by decide +kernel) 0x101a4f)
  have keepE (i : Fin Reg.count) (h : i.val ∈ memcpyPreserved) (h₁ : i.val ≠ 12) (h₂ : i.val ≠ 15) :
      e[i] = a[i] := (kept₂ i h).trans (keepC i h h₁ h₂)
  have edf := (keepE 22 (by decide) (by decide) (by decide)).trans state.df
  have e9 := congrArg Value.width (keepE 9 (by decide) (by decide) (by decide))
  obtain ⟨f, path₂, fs, _, back₂⟩ := resume (dst := 1304) (src := 3224) (len := 960)
    (win.of_frame fl) (by decide) (by decide) (by decide) (by decide) block₂ es ed er en
    (congrArg (Value.get 1) edf) (e9.trans (state.widths 9 (by decide)))
  have keepF (i : Fin Reg.count) (h : i.val ∈ memcpyPreserved) : f[i] = c[i] := (back₂ i h).trans (kept₂ i h)
  have f13 := (keepF 13 (by decide)).trans c13
  have f12 := (keepF 12 (by decide)).trans c12
  obtain ⟨g, block₃, gs, gd, gr, gn, g15, kept₃⟩ := copyTableCall (congrArg (Value.get 64) fs)
    (congrArg (Value.get 64) f13) (congrArg (Value.get 64) f12)
    (push fr _ _ 19 code_l101a4f (by decide +kernel) 0x101a65)
  have keepG (i : Fin Reg.count) (h : i.val ∈ memcpyPreserved) (h₁ : i.val ≠ 12) (h₂ : i.val ≠ 15) :
      g[i] = a[i] := (kept₃ i h h₂).trans ((keepF i h).trans (keepC i h h₁ h₂))
  have gdf := (keepG 22 (by decide) (by decide) (by decide)).trans state.df
  have g9 := congrArg Value.width (keepG 9 (by decide) (by decide) (by decide))
  obtain ⟨z, path₃, zs, zw, back₃⟩ := resume (dst := 4184) (src := 344) (len := 1920)
    (win.of_frame fr) (by decide) (by decide) (by decide) (by decide) block₃ gs gd gr gn
    (congrArg (Value.get 1) gdf) (g9.trans (state.widths 9 (by decide)))
  have keep (i : Fin Reg.count) (h : i.val ∈ memcpyPreserved) (h₁ : i.val ≠ 12) (h₂ : i.val ≠ 15) :
      z[i] = a[i] := (back₃ i h).trans (keepG i h h₁ h₂)
  have z12 := (back₃ 12 (by decide)).trans ((kept₃ 12 (by decide) (by decide)).trans f12)
  have z15 := (back₃ 15 (by decide)).trans g15
  have final := callMemoryFrame (src := 344) (dst := 4184) (len := 1920) low room fr 0x101a65 (by decide) (by decide)
  refine ⟨z, _, (path₁.trans path₂).trans path₃, ?_, (keep 14 (by decide) (by decide) (by decide)).trans pair,
    z15, WordsAt.of_frame scalar final (by decide) (outside call (by decide)), source.of_frame final (outside call (by decide))⟩
  refine ⟨tableMemory call state.toMemory final, zs, (keep 3 (by decide) (by decide) (by decide)).trans state.output,
    (back₃ 22 (by decide)).trans gdf, ?_, (congrArg Value.width (keep 39 (by decide) (by decide) (by decide))).trans state.mxcsr,
    (congrArg Value.width (keep 50 (by decide) (by decide) (by decide))).trans state.ftw,
    (congrArg Value.width (keep 51 (by decide) (by decide) (by decide))).trans state.fcw⟩
  rintro ⟨i, hi⟩ h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact zw 1 (by decide)
  · exact zw 2 (by decide)
  · exact (congrArg Value.width (keep 3 (by decide) (by decide) (by decide))).trans (state.widths 3 (by decide))
  · exact (congrArg Value.width (keep 5 (by decide) (by decide) (by decide))).trans (state.widths 5 (by decide))
  · exact zw 8 (by decide)
  · exact zw 9 (by decide)
  · exact congrArg Value.width z12
  · exact (congrArg Value.width (keep 13 (by decide) (by decide) (by decide))).trans (state.widths 13 (by decide))
  · exact (congrArg Value.width (keep 14 (by decide) (by decide) (by decide))).trans (state.widths 14 (by decide))
  · exact congrArg Value.width z15

end K256.Proofs.Ecdh.Wrapper
