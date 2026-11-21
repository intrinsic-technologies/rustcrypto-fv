import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def cleared (fr : Activation) (second : Bool) (m : Ram) :=
  memStore m (context fr second + 127) (0 : BitVec 8)

def marked (fr : Activation) (second : Bool) (m : Ram) :=
  memStore (cleared fr second m) (context fr second + 127) (1 : BitVec 8)

def tailMemory (fr : Activation) (second : Bool) (m : Ram) (ret : BitVec 64) :=
  memCopy (memStore (marked fr second m) (sp fr - 8) ret)
    (context fr second + 64) (fr.rsp + 351) 1

def tailRegions (fr : Activation) (second : Bool) : List MemoryRegion :=
  [⟨(sp fr - 8).toNat,8⟩,⟨(context fr second + 64).toNat,64⟩]

theorem tailMemory_post {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr (.seeded secret reduced))
    (live : Live (tailAt second) fr a m state) (slots : Slots fr m)
    (ctx : Compressed second fr m state secret) (ret : BitVec 64) :
    let n := tailMemory fr second m ret
    let rs := tailRegions fr second
    RamWriteFrame m n rs ∧ LocalWrites fr rs ∧ Slots fr n ∧
      UpdateV.HmacStateAt n (context fr second) state.key (taggedValue second state ++ secret) := by
  dsimp only
  let p := context fr second
  let k : Nat := if second then 328 else 160
  let slot := sp fr - 8
  let src := fr.rsp + 351
  let rs := tailRegions fr second
  let u := memStore (marked fr second m) slot ret
  let n := tailMemory fr second m ret
  have dep := env.depth
  have limit := env.limit
  have base := spNat env
  have hk : k = 160 ∨ k = 328 := by cases second <;> decide
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low,BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have pn : p.toNat = (sp fr).toNat + k := by
    cases second <;> exact spAddNat env _ (by decide)
  have addr (off : BitVec 64) (h : off.toNat ≤ 168) :
      (p + off).toNat = (sp fr).toNat + k + off.toNat := by
    rw [BitVec.toNat_add,pn,Nat.mod_eq_of_lt (by omega)]
  have slotN : slot.toNat = (sp fr).toNat - 8 := BitVec.toNat_sub_of_le
    (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have srcN : src.toNat = fr.rsp.toNat + 351 := by
    rw [show src = fr.rsp + 351 from rfl,BitVec.toNat_add,Nat.mod_eq_of_lt (by change fr.rsp.toNat + 351 < 2^64; omega)]
    rfl
  have bufN : (p+64).toNat = (sp fr).toNat + k + 64 := addr 64 (by decide)
  have usedN : (p+127).toNat = (sp fr).toNat + k + 127 := addr 127 (by decide)
  have localWrites : LocalWrites fr rs := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · change fr.low.toNat ≤ slot.toNat ∧ slot.toNat + 8 ≤ fr.rsp.toNat - 48
      omega
    · obtain rfl := List.mem_singleton.mp h
      change fr.low.toNat ≤ (p+64).toNat ∧ (p+64).toNat + 64 ≤ fr.rsp.toNat - 48
      omega
  have inBuf {q : BitVec 64} (len : Nat) (lo : (p+64).toNat ≤ q.toNat)
      (hi : q.toNat + len ≤ (p+64).toNat + 64) : InRegions rs q len :=
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),lo,hi,by omega⟩
  have wr₀ := RamWriteFrame.refl m rs
  have t : RamWriteFrame m (cleared fr second m) rs :=
    wr₀.memStore _ (inBuf (q := p+127) 1 (by omega) (by omega))
  have w : RamWriteFrame m (marked fr second m) rs :=
    t.memStore _ (inBuf (q := p+127) 1 (by omega) (by omega))
  have push : RamWriteFrame m u rs := w.memStore _
    ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _,by change slot.toNat + 8 ≤ 2^64; omega⟩
  have frame : RamWriteFrame m n rs := Sec1.Wrapper.Copy.memCopy_frame push
    (inBuf (q := p+64) 1 (Nat.le_refl _) (by omega))
  have outside {q : BitVec 64} {len : Nat} (lim : q.toNat+len ≤ 2^64)
      (above : slot.toNat + 8 ≤ q.toNat)
      (away : q.toNat + len ≤ (p+64).toNat ∨ (p+64).toNat+64 ≤ q.toNat) :
      Outside rs q len := by
    refine ⟨lim,fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · exact Or.inr above
    · obtain rfl := List.mem_singleton.mp h
      exact away
  have before (off : BitVec 64) (bound : off.toNat ≤ 120) : Outside rs (sp fr + off) 8 := by
    have adr : (sp fr + off).toNat = (sp fr).toNat + off.toNat := by
      rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    exact outside (by omega) (by omega) (.inl (by omega))
  have slots' := slotsAfter slots frame (before 8 (by decide)) (before 112 (by decide)) (before 120 (by decide))
  have slice := env.slicesAt live.writes
  obtain ⟨_, _, _, inputLimit, _, _, _, _, _, _, _, sec, _⟩ := slice
  have secLen : secret.size = 32 := sec.1
  have vLen : state.value.size = 32 := live.bytes.value.1
  have tagged : (taggedValue second state).size = 33 := by
    rw [taggedValue,ByteArray.size_append,vLen]; rfl
  have paddedLen : (padded second state).size = 97 := by
    rw [padded,ByteArray.size_append,UpdateV.keyPad_size,tagged]
  have allLen : (taggedValue second state ++ secret).size = 65 := by
    rw [ByteArray.size_append,tagged,secLen]
  have s := append_crossing initialHash (padded second state) secret 31
    (by rw [paddedLen]) (by omega) (by omega)
  have raw : (⟨src.toNat,1⟩ : MemoryRegion).HasBytes m (secret.extract 31 secret.size) := by
    constructor
    · change (secret.extract 31 secret.size).size = 1
      simp [ByteArray.size_extract,secLen]
    · intro i
      have hi : i.val < 1 := by simpa only [ByteArray.size_extract,Nat.min_self,secLen] using i.isLt
      have h := sec.2 ⟨31+i.val,by omega⟩
      change m[BitVec.ofNat 64 ((fr.rsp+320).toNat+(31+i.val))]? = _ at h
      change m[BitVec.ofNat 64 (src.toNat+i.val)]? = _
      rw [ByteArray.getElem_extract]
      have eq : (fr.rsp+320).toNat + (31+i.val) = src.toNat+i.val := by
        rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by change fr.rsp.toNat + 320 < 2^64; omega),srcN]
        change fr.rsp.toNat+320+(31+i.val) = fr.rsp.toNat+351+i.val
        omega
      rwa [eq] at h
  have copied := Sec1.Wrapper.Copy.memCopy_hasBytes (dst := p+64) (by decide : 1 ≤ 2^64)
    (UpdateV.Finalize.bytesAfter push (outside (by omega) (by omega) (.inr (by omega))) raw)
  have small := RamWriteFrame.refl (marked fr second m) (copyRegions (sp fr) (p+64) 1)
  have pushed : RamWriteFrame (marked fr second m) u (copyRegions (sp fr) (p+64) 1) := small.memStore ret
    ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _,by change slot.toNat + 8 ≤ 2^64; omega⟩
  have copiedFrame : RamWriteFrame (marked fr second m) n (copyRegions (sp fr) (p+64) 1) :=
    Sec1.Wrapper.Copy.memCopy_frame pushed ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Nat.le_refl _,Nat.le_refl _,by omega⟩
  have used : memLoad n (p+127) 8 = 1 := by
    rw [copiedFrame.memLoad_eq]
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · refine ⟨by change (p+127).toNat + 1 ≤ 2^64; omega, fun r hr => Or.inr ?_⟩
      rcases List.mem_cons.mp hr with rfl | h
      · change slot.toNat + 8 ≤ (p+127).toNat; omega
      · obtain rfl := List.mem_singleton.mp h
        change (p+64).toNat + 1 ≤ (p+127).toNat; omega
  have hashN := addr 128 (by decide)
  have countN := addr 160 (by decide)
  simp only [BitVec.reduceToNat] at hashN countN
  unfold padded at s
  refine ⟨frame,localWrites,slots',UpdateV.Finalize.bytesAfter frame
    (outside (q := p) (by omega) (by omega) (.inl (by omega))) ctx.outer,?_,?_,?_,?_⟩
  · rw [← ByteArray.append_assoc,s.2,allLen]
    exact copied
  · rw [allLen]; exact used
  · rw [← ByteArray.append_assoc,s.1]
    exact UpdateV.Finalize.stateAfter frame (outside (q := p+128) (by omega) (by omega) (.inr (by omega))) ctx.hash
  · rw [allLen]
    exact (frame.memLoad_eq (outside (q := p+160) (by change (p+160).toNat+8 ≤ 2^64; omega) (by omega)
      (.inr (by omega)))).trans ctx.count

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
