import K256.Proofs.Signing.Nonce.Initialize.Update.State
import K256.Proofs.Signing.UpdateV.Finalize.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem outsideWritable {m : Ram} {p : BitVec 64} {n : Nat}
    (w : Writable Extracted.programImage m p n) (b) (hb : b ∈ Extracted.programImage) :
    b.1.toNat + 1 ≤ p.toNat ∨ p.toNat + n ≤ b.1.toNat := by
  by_cases lo : b.1.toNat < p.toNat
  · exact Or.inl (by omega)
  · right
    apply Classical.byContradiction
    intro h
    apply w.notCode b hb (b.1.toNat - p.toNat) (by omega)
    apply BitVec.eq_of_toNat_eq
    have bound := b.1.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ - _) (by omega),
      Nat.add_sub_cancel' (by omega), Nat.mod_eq_of_lt bound]

theorem Environment.imageAt {fr : Activation} {m : Ram} {input : Input} (env : Environment fr input)
    (writes : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,64⟩]) :
    ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2 := by
  intro b hb
  apply (writes.outside _ ?_).trans (env.image b hb)
  have depth := env.depth
  have bottom : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)
  refine ⟨by have := b.1.isLt; omega, fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | h
  · have sep := outsideWritable env.stack b hb
    simp only [Activation.region, env.low, bottom] at sep ⊢
    omega
  · obtain rfl := List.mem_singleton.mp h
    exact outsideWritable env.writable b hb

theorem Live.image {l : Label} {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    {input : Input} {state : State} (live : Live l fr a m state) (env : Environment fr input) :
    ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2 :=
  env.imageAt live.writes

theorem Environment.stateAfter {input : Input} {fr : Activation} {m n : Ram} {state : State}
    (env : Environment fr input) (bytes : StateAt m fr.rdi state)
    (writes : RamWriteFrame m n [fr.region]) : StateAt n fr.rdi state := by
  have dep := env.depth
  have base : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have limit := env.dataLow
  have above : (fr.rdi + 32).toNat = fr.rdi.toNat + 32 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rdi.toNat + 32 < 2^64; omega)]
    rfl
  have out : Outside [fr.region] fr.rdi 64 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    rcases env.apart with h | h
    · exact Or.inl h
    · right
      change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rdi.toNat
      omega
  refine ⟨UpdateV.Finalize.bytesAfter writes ?_ bytes.key, ?_⟩
  · refine ⟨by omega, fun r hr => ?_⟩
    rcases out.2 r hr with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  · change (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes n state.value
    rw [← above]
    exact UpdateV.Finalize.bytesAfter writes (UpdateV.Finalize.outsideOffset out 32 32 (by decide) (by decide)) (by simpa only [above] using bytes.value)

theorem Environment.slicesAt {input : Input} {fr : Activation} {m : Ram}
    (env : Environment fr input)
    (writes : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,64⟩]) :
    input.At {fr with original := m} := by
  cases input with
  | empty => exact env.slices
  | seeded secret reduced =>
    obtain ⟨di, si, dx, limit, read, a, b, c, d, e, f, sec, red⟩ := env.slices
    have depth := env.depth
    have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
      rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
      rfl
    have addr (off : BitVec 64) (fit : off.toNat ≤ 352) :
        (fr.rsp + off).toNat = fr.rsp.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have outside (off : BitVec 64) (n : Nat) (lo : 80 ≤ off.toNat)
        (hi : off.toNat + n ≤ 352) : Outside [fr.region, ⟨fr.rdi.toNat,64⟩] (fr.rsp+off) n := by
      have q := addr off (by omega)
      refine ⟨by omega, fun r hr => Or.inr ?_⟩
      rcases List.mem_cons.mp hr with rfl | h
      · change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
        omega
      · obtain rfl := List.mem_singleton.mp h
        change fr.rdi.toNat + 64 ≤ _
        rw [di, addr _ (by decide)]
        change fr.rsp.toNat + 16 + 64 ≤ _
        omega
    have load (off : BitVec 64) (h : off.toNat ≤ 40) :
        memLoad m (fr.rsi + off) 64 = memLoad fr.original (fr.rsi + off) 64 := by
      apply writes.memLoad_eq
      rw [si, BitVec.add_assoc]
      apply outside
      all_goals
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change 112 + off.toNat < 2^64; omega)]
        simp only [BitVec.reduceToNat]
        omega
    refine ⟨di, si, dx, limit, read.of_frame writes, ?_, (load 8 (by decide)).trans b,
      (load 16 (by decide)).trans c, (load 24 (by decide)).trans d,
      (load 32 (by decide)).trans e, (load 40 (by decide)).trans f,
      UpdateV.Finalize.bytesAfter writes (outside 320 32 (by decide) (by decide)) sec,
      UpdateV.Finalize.bytesAfter writes (outside 208 32 (by decide) (by decide)) red⟩
    have ptr := load 0 (by decide)
    rw [show fr.rsi + (0 : BitVec 64) = fr.rsi by bv_omega] at ptr
    exact ptr.trans a

end K256.Proofs.Signing.Nonce.Initialize.Update
