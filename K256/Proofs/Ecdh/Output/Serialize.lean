import K256.Proofs.Ecdh.Affine.State
import K256.Proofs.Ecdh.Wrapper.Frame
import K256.Proofs.Ecdh.LIR.EcdhDiffieHellman
import K256.Proofs.Ecdh.Output.Serialize.PackReturn
import K256.Proofs.Ecdh.Output.Serialize.Normalize
import K256.Proofs.Ecdh.Scalar.Frame
import K256.Proofs.Sec1.Serialize.Normalize.Correct

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Ecdh.Wrapper Standards.SECG.ECC

def xBytes (p : Curve.Point) : ByteArray :=
  Encoding.natToOctets 32 (match p with | .infinity => 0 | .affine x _ => x)

theorem serialize {s : RamState} {secret peer : ByteArray} {p : Curve.Point}
    {m : Ram} {a : Vector Value Reg.count}
    (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (stack : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (saved : Saved s m) (rsp : a[4] = ⟨64, localSp s - 8⟩)
    (rsi : a[6] = ⟨64, localSp s + 4184⟩) (rdi : a[7] = ⟨64, localSp s + 344⟩)
    (rbx : a[3] = ⟨64, s.regValue .rdi⟩) (df : a[22] = ⟨1, 0⟩)
    (slot : memLoad m (localSp s - 8) 64 = 0x101b1d)
    (x : Affine.XAt m (localSp s + 4184) p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l120350, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, 0x101b1d⟩ ∧ out.values[4] = ⟨64, localSp s⟩ ∧
      out.values[3] = ⟨64, s.regValue .rdi⟩ ∧ out.values[22] = ⟨1, 0⟩ ∧
      RamWriteFrame s.external out.store [Stack.region s ecdhDiffieHellman.minStackBytes] ∧
      Saved s out.store ∧ (⟨(localSp s + 344).toNat, 32⟩ : MemoryRegion).HasBytes out.store (xBytes p) := by
  let base := stackPtr s - 6264
  let dst := localSp s + 344
  let src := localSp s + 4184
  obtain ⟨room, low, _⟩ := Scalar.stack_geometry call
  have align : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have natOff (off : Nat) (h : off ≤ 10088) :=
    Common.stackOffset (off := off) call.stackAvailable h
  have baseN : base.toNat = (stackPtr s).toNat - 6264 := natOff 6264 (by decide)
  have offsets (off : Nat) (h : off ≤ 6264) :
      (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have n88 : (base + 88).toNat = base.toNat + 88 := offsets 88 (by decide)
  have n104 : (base + 104).toNat = base.toNat + 104 := offsets 104 (by decide)
  have n48 : (base + 48).toNat = base.toNat + 48 := offsets 48 (by decide)
  have n8 : (base - 8).toNat = (stackPtr s).toNat - 6272 := by
    rw [show base - 8 = stackPtr s - 6272 by dsimp [base]; bv_omega]
    exact natOff 6272 (by decide)
  have start : base - 121 = stackPtr s - 6385 := by dsimp [base]; bv_omega
  have n121 : (base - 121).toNat = (stackPtr s).toNat - 6385 := by rw [start]; exact natOff 6385 (by decide)
  have sp : base + 104 = localSp s - 8 := by change stackPtr s - 6264 + 104 = stackPtr s - 6152 - 8; bv_omega
  have srcOff : src = stackPtr s - 1968 := by change stackPtr s - 6152 + 4184 = stackPtr s - 1968; bv_omega
  have dstOff : dst = stackPtr s - 5808 := by change stackPtr s - 6152 + 344 = stackPtr s - 5808; bv_omega
  have srcN : src.toNat = (stackPtr s).toNat - 1968 := by rw [srcOff]; exact natOff 1968 (by decide)
  have dstN : dst.toNat = (stackPtr s).toNat - 5808 := by rw [dstOff]; exact natOff 5808 (by decide)
  have win : Writable Extracted.programImage m (base - 121) 433 := by
    rw [start]
    exact (Common.stackWritable (off := 6385) call (by decide) (by decide) (by decide)).of_frame stack
  have source : Readable m src 40 := by
    rw [srcOff]
    exact ((Common.stackWritable (off := 1968) call (by decide) (by decide) (by decide)).of_frame stack).readable
  have dest : Writable Extracted.programImage m dst 32 := by
    rw [dstOff]
    exact (Common.stackWritable (off := 5808) call (by decide) (by decide) (by decide)).of_frame stack
  obtain ⟨v, w, words, repr, val⟩ := x
  obtain ⟨b, n, setup, r4, r6, r7, r3, r14, r22, f1, bx, slot1, input⟩ := normalizeSetup
    (a := a) (m := m) (base := base) (src := src) (dst := dst)
    (by rw [rsp, sp]; rfl) (by rw [rsi]; rfl) (by rw [rdi]; rfl)
    win source (by omega) words
  obtain ⟨c, cr, ct, c4, c3, c14, c22, f2, normalized⟩ := normalize r4 r6 r7 r3 r14 (r22.trans df)
    (win.of_frame f1) (by omega) slot1 input
  have outerSlot : memLoad n (base + 104) 64 = 0x101b1d := by
    rw [f1.memLoad_eq, sp, slot]
    exact ⟨by change _ + 8 ≤ 2^64; omega, fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      right; change (base - 8).toNat + 112 ≤ _; omega⟩
  have restore (i : Nat) (hi : 88 ≤ i) (hj : i ≤ 104) :
      memLoad c.store (base + BitVec.ofNat 64 i) 64 = memLoad n (base + BitVec.ofNat 64 i) 64 := by
    apply f2.memLoad_eq
    have atI := offsets i (by omega)
    refine ⟨by change _ + 8 ≤ 2^64; omega, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | ht
    · right; change (base - 121).toNat + 113 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp ht
      right; change (base + 48).toNat + 40 ≤ _; omega
  have bx' : memLoad c.store (base + 88) 64 = s.regValue .rdi :=
    (restore 88 (by decide) (by decide)).trans (bx.trans (by rw [rbx]; rfl))
  obtain ⟨o, pr, tag, o4, o3, o22, f3, packed⟩ := packReturn c4 c3 c14 c22
    ((win.of_frame f1).of_frame f2) ((dest.of_frame f1).of_frame f2) (by omega)
    bx' ((restore 104 (by decide) (by decide)).trans outerSlot) normalized
  have m1 := (show Scalar.Memory s m from ⟨stack, saved⟩).advance call f1 (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (base - 8).toNat ∧ (base - 8).toNat + 112 ≤ _; omega)
  have m2 := m1.advance call f2 (by
    intro r hr; rcases List.mem_cons.mp hr with rfl | ht
    · change _ ≤ (base - 121).toNat ∧ (base - 121).toNat + 113 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp ht
      change _ ≤ (base + 48).toNat ∧ (base + 48).toNat + 40 ≤ _; omega)
  have m3 := m2.advance call f3 (by
    intro r hr; rcases List.mem_cons.mp hr with rfl | ht
    · change _ ≤ (base - 8).toNat ∧ (base - 8).toNat + 8 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp ht
      change _ ≤ dst.toNat ∧ dst.toNat + 32 ≤ _; omega)
  have after : base + 112 = localSp s := by change stackPtr s - 6264 + 112 = stackPtr s - 6152; bv_omega
  obtain ⟨width, value⟩ := Sec1.Serialize.Normalize.normalize_correct w v 8 repr (by decide)
  have bytes := Sec1.Serialize.packWords_hasBytes width packed
    ((((dest.of_frame f1).of_frame f2).of_frame f3).readable)
  rw [value, val] at bytes
  exact ⟨o, ParseSignature.exec_call setup cr (by rw [ct]; rfl) pr, tag,
    by simpa only [after] using o4, o3, o22, m3.frame, m3.saved, bytes⟩

end K256.Proofs.Ecdh.Output
