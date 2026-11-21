import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Loop
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Safety

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def firstSaved (fr : Activation) (m : Ram) :=
  memStore m (sp fr + 112) (fr.rdi + 32)

def firstTagged (fr : Activation) (m : Ram) :=
  taggedMemory (firstSaved fr m) (sp fr + 160) (fr.rdi + 32) 0

def firstResult (seeded : Bool) (fr : Activation) (m : Ram) :=
  let t := firstTagged fr m
  if seeded then memStore (memStore t (sp fr + 120) fr.rdi) (sp fr + 8) (fr.rsi + 48) else t

variable {fr : Activation} {input : Input} {a : Verify.Core.Registers} {m : Ram} {state : State}

theorem firstFrame (env : Environment fr input) (s : Bool) :
    RamWriteFrame m (firstResult s fr m) (area fr 8 288) := by
  have saved := stackStore (i := 112) env (RamWriteFrame.refl m (area fr 8 288))
    (fr.rdi+32) (by decide) (by decide) (by decide)
  have tagged := taggedFrame (off := 160) env saved (fr.rdi+32) 0 (by decide) (by decide) (by decide)
  cases s
  · exact tagged
  · exact stackStore (i := 8) env
      (stackStore (i := 120) env tagged fr.rdi (by decide) (by decide) (by decide))
      (fr.rsi+48) (by decide) (by decide) (by decide)

theorem firstState (env : Environment fr input) (live : Live (appendAt false) fr a m state)
    (ctx : UpdateV.HmacStateAt m (context fr false) state.key ByteArray.empty) (s : Bool) :
    UpdateV.HmacStateAt (firstResult s fr m) (context fr false) state.key (taggedValue false state) := by
  have ws : RamWriteFrame m (firstSaved fr m) (area fr 112 120) :=
    stackStore (i := 112) env (RamWriteFrame.refl m _) (fr.rdi+32) (by decide) (by decide) (by decide)
  have old := UpdateV.Finalize.hmacAfter ws
    (stackOutside (i := 160) env (by decide) (by decide) (by decide)) ctx
  have bytes : (⟨(fr.rdi+32).toNat,32⟩ : MemoryRegion).HasBytes m state.value := by
    rw [valueNat env]
    exact live.bytes.value
  have out := valueOutside (lo := 112) (hi := 120) (i := 0) (n := 32) env
    (by decide) (by decide) (by decide)
  rw [show fr.rdi+32+BitVec.ofNat 64 0 = fr.rdi+32 by bv_omega] at out
  have read := (stackWritable env live ws 224 32 (by decide)).readable
  have tagged : UpdateV.HmacStateAt (firstTagged fr m) (context fr false) state.key
      (taggedValue false state) := taggedState 0 old (UpdateV.Finalize.bytesAfter ws out bytes)
        (by change Readable _ (sp fr+160+64) 32; rwa [show sp fr+160+64=sp fr+224 by bv_omega])
  cases s
  · exact tagged
  · have ws' := stackStore (i := 120) env (RamWriteFrame.refl (firstTagged fr m) (area fr 8 128))
      fr.rdi (by decide) (by decide) (by decide)
    exact UpdateV.Finalize.hmacAfter
      (stackStore (i := 8) env ws' (fr.rsi+48) (by decide) (by decide) (by decide))
      (stackOutside (i := 160) env (by decide) (by decide) (by decide)) tagged

theorem firstSlots (env : Environment fr input) : Slots fr (firstResult true fr m) := by
  have frame : RamWriteFrame (firstSaved fr m) (firstTagged fr m) (area fr 224 288) :=
    taggedFrame (off := 160) env (.refl _ _) _ _ (by decide) (by decide) (by decide)
  have value := frame.memLoad_eq (k := 64)
    (stackOutside (i := 112) env (by decide) (by decide) (by decide))
  have hv : memLoad (firstTagged fr m) (sp fr+112) 64 = fr.rdi+32 :=
    value.trans (memLoad_memStore_same _ _ _ (by decide) (by decide))
  unfold firstResult
  simp only [ite_true]
  refine ⟨memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_⟩
  · iterate 2 rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (by apply RangeApart.of_offsets rfl rfl <;> decide)]
    exact hv
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (by apply RangeApart.of_offsets rfl rfl <;> decide)]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix
