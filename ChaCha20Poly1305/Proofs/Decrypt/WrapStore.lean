import ChaCha20Poly1305.Proofs.Decrypt.DetachBase

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open Hash
def stores (m : Ram) (sp a b t : BitVec 64) := memStore (memStore (memStore (memStore (memStore
  m (sp+32) a) (sp+40) a) (sp+48) b) sp t) (sp-8) (0x1015d4 : BitVec 64)
def preAreas (sp : BitVec 64) : List MemoryRegion := [⟨sp.toNat-8,8⟩,⟨sp.toNat,8⟩,⟨sp.toNat+32,24⟩]
theorem storesFrame {m sp a b t} (floor : 8≤sp.toNat) (low : sp.toNat+88≤2^32) :
    RamWriteFrame m (stores m sp a b t) (preAreas sp) := by
  unfold stores
  repeat' apply RamWriteFrame.memStore
  all_goals first | exact RamWriteFrame.refl _ _ | (simp [InRegions,InRegion,preAreas]; bv_omega)

theorem storesRead {m sp a b t p n} (fl : 872≤sp.toNat) (low : sp.toNat+88≤2^32)
    (pl : p.toNat+n≤2^32) (sep : p.toNat+n≤sp.toNat-872 ∨ sp.toNat+88≤p.toNat) :
    memLoad (stores m sp a b t) p (8*n)=memLoad m p (8*n) := by
  apply (storesFrame (by omega) low).memLoad_eq
  simp [Outside,preAreas]; omega

theorem finishFrame {orig m m' sp a b t low} {add : List MemoryRegion} (floor : low+872≤sp.toNat) (limit : sp.toNat+88≤2^32)
    (init : RamWriteFrame orig m (⟨low,sp.toNat-low⟩ :: (add ++ [⟨sp.toNat,8⟩,⟨(sp+32).toNat,24⟩])))
    (later : RamWriteFrame (stores m sp a b t) m' (⟨low,(sp-8).toNat-low⟩ :: (add ++ [⟨sp.toNat,8⟩,⟨(sp+32).toNat,24⟩]))) :
    RamWriteFrame orig m' (⟨low,sp.toNat-low⟩ :: (add ++ [⟨sp.toNat,8⟩,⟨(sp+32).toNat,24⟩])) := by
  apply (init.trans (storesFrame (by omega) limit) _).trans later
  · intro r hr
    rcases List.mem_cons.mp hr with e|h
    · subst r; exact ⟨_,.head _,Nat.le_refl _,by bv_omega⟩
    · exact ⟨r,.tail _ h,Nat.le_refl _,Nat.le_refl _⟩
  · intro r hr
    simp only [preAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,.head _,by dsimp; omega,by dsimp; omega⟩
    · exact ⟨_,.tail _ (List.mem_append_right _ (.head _)),Nat.le_refl _,Nat.le_refl _⟩
    · exact ⟨_,.tail _ (List.mem_append_right _ (.tail _ (.head _))),by dsimp; bv_omega,by dsimp; bv_omega⟩

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
