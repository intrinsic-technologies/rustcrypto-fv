import ChaCha20Poly1305.Proofs.Decrypt.StreamScope
import ChaCha20Poly1305.Proofs.Decrypt.TailXorRun

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

theorem Scope.tailGeo {x fr m} (s : Scope x fr m) : TailGeo fr.rdi (tailPtr x) (Tail.rem64 x.n).toNat m := by
  have bufLow := s.buf.readable.low
  have ctxLow := s.ctx.readable.low
  have cs := s.ctxBuf
  have co := s.bufCode
  have r := remNat x
  have base := baseNat x
  have p : (tailPtr x).toNat = x.buf.toNat+(Tail.base64 x.n).toNat := by
    unfold tailPtr; bv_omega
  have k : (fr.rdi+64).toNat = fr.rdi.toNat+64 := by bv_omega
  exact ⟨s.ctx.readable.sub (by omega) (by omega),s.buf.sub (by omega) (by omega),by omega,by omega,by omega⟩

theorem Scope.residualGeo {x fr m} (s : Scope x fr m) :
    TailGeo (fr.rdi+groups x) (tailPtr x+groups x) (rem4 x).toNat m := by
  have t := s.tailGeo
  have rk := t.keys.low
  have rb := t.buffer.readable.low
  have cs := t.apart
  have co := t.code
  have r := remNat x
  have g := groupsNat x
  have q := remFourNat x
  have ctxLow := s.ctx.readable.low
  have bufLow := s.buf.readable.low
  have keyEq : (fr.rdi+groups x+64).toNat = (fr.rdi+64).toNat+(groups x).toNat := by bv_omega
  have bufEq : (tailPtr x+groups x).toNat = (tailPtr x).toNat+(groups x).toNat := by bv_omega
  exact ⟨t.keys.sub (by omega) (by omega),t.buffer.sub (by omega) (by omega),by omega,by omega,by omega⟩

theorem TailGeo.shape {k b n m} (t : TailGeo k b n m) : Xor.Shape b (k+64) b n :=
  ⟨t.buffer.readable.low,t.keys.low,t.buffer.readable.low,t.apart,.inl rfl⟩

theorem noWrite {r : List MemoryRegion} {a b : Ram} (e : RamWriteFrame a b []) : RamWriteFrame a b r :=
  (RamWriteFrame.refl a r).trans e (by intro _ h; simp at h)

theorem noChange {a b : Ram} (e : RamWriteFrame a b []) (addr : BitVec 64) (i : Nat) :
    Xor.readAt b addr i = Xor.readAt a addr i := by
  apply e.memLoad_eq
  simp [Outside]
  have := (addr+BitVec.ofNat 64 i).isLt
  omega

theorem afterEmpty {s k d n m m₁ m₂ m₃} (before : RamWriteFrame m m₁ [])
    (eff : Xor.Effect s k d n m₁ m₂) (after : RamWriteFrame m₂ m₃ []) :
    Xor.Effect s k d n m m₃ := by
  refine ⟨((noWrite before).trans eff.frame (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)).trans
    after (by intro _ h; simp at h),?_⟩
  intro i hi
  rw [noChange after,eff.value _ hi,noChange before,noChange before]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
