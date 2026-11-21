import K256.Proofs.Signing.UpdateV.Finalize.Rounds
import K256.Proofs.Signing.UpdateV.Finalize.Return
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.RFC Standards.NIST.SHA2

private theorem restoreOffsets : ∀ i : Fin 6,
    (#v[312,352,320,328,336,344] : Vector (BitVec 64) 6)[i] =
      360 - (#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i] := by decide +kernel

theorem execute {a : Registers} {m : Ram} {sp src dst : BitVec 64} {key input : ByteArray}
    (call : Call a m sp src dst) (state : HmacStateAt m src key input)
    (keyShort : key.size ≤ 64) (small : input.size % 64 < 56) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l107a50,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,memLoad m sp 64⟩ ∧ out.values[4] = ⟨64,sp + 8⟩ ∧
      (∀ i : Fin 6, out.values[(#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[i]] =
        ⟨64,a[(#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[i]].get 64⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [scratch sp,⟨dst.toNat,32⟩] ∧
      (⟨dst.toNat,32⟩ : MemoryRegion).HasBytes out.store (HMAC.hmac SHA256.hashBytes 64 key input) ∧
      ParseSignature.ArgumentWidths out.values := by
  let base := sp-360
  have depth := call.depth
  have limit := call.limit
  have baseNat : base.toNat = sp.toNat - 360 :=
    BitVec.toNat_sub_of_le (show (360 : BitVec 64) ≤ sp from by change 360 ≤ sp.toNat; omega)
  have botNat : (sp - 704).toNat = sp.toNat - 704 :=
    BitVec.toNat_sub_of_le (show (704 : BitVec 64) ≤ sp from depth)
  have retAddr : base+360 = sp := by dsimp only [base]; bv_omega
  obtain ⟨b,t,reached,f,hash⟩ := rounds call state small
  have retSame : memLoad t sp 64 = memLoad m sp 64 := by
    apply f.writes.memLoad_eq
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change sp.toNat-704+704 ≤ sp.toNat; omega
  have stackReadable : Readable t base 368 := by
    apply Readable.of_frame (regions := [scratch sp]) _ f.writes
    refine ⟨by omega,fun i hi => ?_⟩
    by_cases h : i < 360
    · have rd : Readable m base 360 := call.stack.readable.sub (by omega) (by omega)
      exact rd.present i h
    · have eq : base + BitVec.ofNat 64 i = sp + BitVec.ofNat 64 (i-360) := by
        calc
          _ = base + BitVec.ofNat 64 (360 + (i-360)) := by rw [show 360 + (i-360) = i by omega]
          _ = _ := by rw [BitVec.ofNat_add,← BitVec.add_assoc]; rw [show base + BitVec.ofNat 64 360 = sp from retAddr]
      rw [eq]
      exact call.ret.present _ (by omega)
  have above := call.dstAbove
  obtain ⟨out,ret,tag,rsp,regs,keep,writes,bytes,widths⟩ := returnBlock (base := base) f.rsp f.output stackReadable
    (call.dstWrite.of_frame f.writes) (by omega) (by rw [retAddr,retSame]; exact call.retLow) hash
  rw [retAddr,retSame] at tag
  have outSp : base+368 = sp+8 := by dsimp only [base]; bv_omega
  change out.values[4] = ⟨64,base+368⟩ at rsp
  rw [outSp] at rsp
  refine ⟨out,Program.Exec.of_sem (reached.exec ret.sem),tag,rsp,?_,
    fun i hi => (keep i hi).trans (f.kept i hi),?_,?_,?_⟩
  · intro i
    rw [regs]
    have eq : base + (#v[312,352,320,328,336,344] : Vector (BitVec 64) 6)[i] =
        sp - (#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i] := by
      rw [restoreOffsets]; dsimp only [base]; bv_omega
    rw [eq,f.slots]
  · refine ((RamWriteFrame.refl m [scratch sp,⟨dst.toNat,32⟩]).trans f.writes ?_).trans writes ?_
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
  · let msg := keyPad key 0x5c ++ SHA256.hashBytes (keyPad key 0x36 ++ input)
    have size : (SHA256.hashBytes (keyPad key 0x36 ++ input)).size = 32 := Vector.size_toArray _
    have short : msg.size % 64 < 56 := by
      dsimp only [msg]; rw [ByteArray.size_append,keyPad_size,size]; decide
    have equation : serializeHash (digestState msg) = SHA256.hashBytes msg := by
      simpa only [short,ite_true,digestState] using serializeHash_finalize msg
    change (⟨dst.toNat,32⟩ : MemoryRegion).HasBytes out.store (serializeHash (digestState msg)) at bytes
    rw [equation,hash_keyPads keyShort] at bytes
    exact bytes
  · intro i hi
    apply widths
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with h|h|h|h|h|h <;> simp [h]

end K256.Proofs.Signing.UpdateV.Finalize
