import K256.Proofs.Signing.Nonce.Fill.State
import K256.Proofs.Signing.UpdateV.Finalize.Memory

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers)

theorem Environment.subNat {fr : Activation} (env : Environment fr)
    (k : BitVec 64) (h : k.toNat ≤ 2160) : (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans h env.depth))

theorem Environment.addNat {fr : Activation} (env : Environment fr)
    (k : BitVec 64) (h : k.toNat ≤ 768) : (fr.rsp + k).toNat = fr.rsp.toNat + k.toNat := by
  have := env.limit
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem Frame.stack {fr : Activation} {a : Registers} {m : Ram} (frame : Frame fr a m) :
    Writable Extracted.programImage m (fr.rsp - 2160) 2160 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,win,_⟩ := frame.atoms
  exact win

theorem Environment.slotNat {fr : Activation} (env : Environment fr) (i : BitVec 64) (h : i.toNat ≤ 232) :
    (sp fr + i).toNat = fr.rsp.toNat - 232 + i.toNat := by
  have := env.depth
  have := env.limit
  rw [BitVec.toNat_add, show (sp fr).toNat = fr.rsp.toNat - 232 from env.subNat 232 (by decide),
    Nat.mod_eq_of_lt (by omega)]

theorem Environment.pushNat {fr : Activation} (env : Environment fr) :
    (sp fr - 8).toNat = fr.rsp.toNat - 240 := by
  rw [show sp fr - 8 = fr.rsp - 240 by unfold sp; bv_omega]
  exact env.subNat 240 (by decide)

theorem Frame.slot {fr : Activation} {a : Registers} {m : Ram} (f : Frame fr a m)
    (env : Environment fr) (i : BitVec 64) (n : Nat) (h : i.toNat + n ≤ 232) :
    Writable Extracted.programImage m (sp fr + i) n := by
  have := env.depth
  apply f.stack.sub <;> rw [Environment.slotNat env i (by omega), env.subNat 2160 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega

theorem Frame.pushSlot {fr : Activation} {a : Registers} {m : Ram} (f : Frame fr a m)
    (env : Environment fr) : Writable Extracted.programImage m (sp fr - 8) 8 := by
  have := env.depth
  apply f.stack.sub <;> rw [Environment.pushNat env, env.subNat 2160 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega

private theorem orderOutside {fr : Activation} (env : Environment fr) {i : BitVec 64} {n : Nat}
    (lo : 424 ≤ i.toNat) (hi : i.toNat + n ≤ 704) : Outside (regions fr) (fr.rsp+i) n := by
  have addr := env.addNat i (by omega)
  have dst := env.addNat 392 (by decide)
  have gen : fr.rdi + 8 = fr.rsp + 704 := by rw [env.gen]; bv_omega
  have st := env.addNat 704 (by decide)
  have bottom := env.subNat 2160 (by decide)
  have lim := env.limit
  have dep := env.depth
  refine ⟨by omega,fun r hr => ?_⟩
  simp only [regions,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [Activation.region,env.low,env.dst,bottom,gen,addr,dst,st,BitVec.reduceToNat] <;> omega

theorem Frame.orderPtr {fr : Activation} {a : Registers} {m : Ram} (f : Frame fr a m)
    (env : Environment fr) : memLoad m fr.rdi 64 = fr.rsp + 600 := by
  apply Eq.trans (f.writes.memLoad_eq ?_) env.orderPtr
  rw [env.gen]
  exact orderOutside env (by decide) (by decide)

theorem Frame.orderWords {fr : Activation} {a : Registers} {m : Ram} (f : Frame fr a m)
    (env : Environment fr) : WordsAt m (fr.rsp + 600) 64
      (Generate.Generator.Multiply.scalarWords Standards.SECG.DomainParameters.Secp256k1.domain.n) :=
  env.orderWords.of_frame f.writes (by decide) (orderOutside env (by decide) (by decide))

theorem Frame.imageAfter {fr : Activation} {a : Registers} {m n : Ram} (f : Frame fr a m)
    (env : Environment fr) (writes : RamWriteFrame fr.original n (regions fr)) :
    ∀ b ∈ Extracted.programImage, n[b.1]? = some b.2 := by
  intro b hb
  have apart {p : BitVec 64} {n : Nat} {t : Ram} (w : Writable Extracted.programImage t p n) :
      b.1.toNat + 1 ≤ p.toNat ∨ p.toNat + n ≤ b.1.toNat := by
    apply Classical.byContradiction
    intro outside
    have lo : p.toNat ≤ b.1.toNat := by omega
    have hi : b.1.toNat < p.toNat + n := by omega
    apply w.notCode b hb (b.1.toNat - p.toNat) (by omega)
    rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have stack := apart f.stack
  have upper := apart env.window
  have bottom := env.subNat 2160 (by decide)
  have dst := env.addNat 392 (by decide)
  have gen : fr.rdi + 8 = fr.rsp + 704 := by rw [env.gen]; bv_omega
  have state := env.addNat 704 (by decide)
  have depth := env.depth
  apply (writes.outside _ ?_).trans (env.image b hb)
  refine ⟨Nat.succ_le_of_lt b.1.isLt, fun r hr => ?_⟩
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [Activation.region, env.low, bottom, env.dst, dst, gen, state, BitVec.reduceToNat] at * <;> omega

theorem Frame.afterCall {fr : Activation} {a b : Registers} {m n : Ram} {rs : List MemoryRegion}
    (f : Frame fr a m) (env : Environment fr) (writes : RamWriteFrame m n rs)
    (within : RegionsWithin rs (regions fr))
    (keep : ∀ (k : BitVec 64) (w : Nat), (w = 64 ∧ k.toNat ∈ [0,8,16,24,32,40,48,88,96,168,184,192] ∨ w = 32 ∧ k = 176) →
      memLoad n (fr.rsp - k) w = memLoad m (fr.rsp - k) w)
    (sp' : b[4] = ⟨64,sp fr⟩)
    (regs : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i])
    (widths : ∀ i : Fin Reg.count, i.val ∈ Activation.entryNumbers → b[i].width = 64) :
    Frame fr b n := by
  have total := f.writes.trans writes within
  have tables := Fn100a40.callSlots_loaded (sections := Extracted.programSections)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (f.imageAfter env total)
  have ⟨r0,v0⟩ := tables (0x203dd0,0x12a820) (by decide)
  have ⟨r1,v1⟩ := tables (0x203de0,0x129770) (by decide)
  have ⟨r2,v2⟩ := tables (0x203e10,0x12a700) (by decide)
  have ⟨r3,v3⟩ := tables (0x203e20,0x100a20) (by decide)
  have atoms := f.atoms
  simp only [Fn100a40.frameAt,Fn100a40.frameAtG1,Atom.All,Atom.Holds] at atoms
  obtain ⟨_,df,mx,ft,fc,ds,sz,gen,bx,r12,r13,r14,r15,bp,rd,rt,rtLow,win,space,align,
    _,_,_,_,_,_,_,_,apart,_⟩ := atoms
  refine ⟨?_, widths, ?_, ?_, ?_, total⟩
  · simp only [Fn100a40.frameAt,Fn100a40.frameAtG1,Atom.All,Atom.Holds]
    exact ⟨sp',(regs 22 (by decide)).trans df,(regs 39 (by decide)).trans mx,
      (regs 50 (by decide)).trans ft,(regs 51 (by decide)).trans fc,
      (keep 192 64 (by decide)).trans ds,
      (keep 184 64 (by decide)).trans sz,
      (keep 88 64 (by decide)).trans gen,
      (keep 48 64 (by decide)).trans bx,
      (keep 40 64 (by decide)).trans r12,
      (keep 32 64 (by decide)).trans r13,
      (keep 24 64 (by decide)).trans r14,
      (keep 16 64 (by decide)).trans r15,
      (keep 8 64 (by decide)).trans bp,
      rd.of_frame writes,(show memLoad n fr.rsp 64 = memLoad m fr.rsp 64 by
        rw [← (show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega)]
        exact keep 0 64 (by decide)).trans rt,
      rtLow,win.of_frame writes,space,align,r0,v0,r1,v1,r2,v2,r3,v3,apart,trivial⟩
  all_goals first
    | exact (show memLoad n (sp fr + 56) 32 = _ by simpa only [sp,reduceAddOffset] using keep 176 32 (by decide)).trans f.bits
    | exact (show memLoad n (sp fr + 64) 64 = _ by simpa only [sp,reduceAddOffset] using keep 168 64 (by decide)).trans f.statePtr
    | exact (show memLoad n (sp fr + 136) 64 = _ by simpa only [sp,reduceAddOffset] using keep 96 64 (by decide)).trans f.valuePtr

theorem stateAfter {fr : Activation} {m n : Ram}
    {rs : List MemoryRegion} {s : Initialize.State} (writes : RamWriteFrame m n rs)
    (out : Outside rs (fr.rdi + 8) 64) (bytes : Initialize.StateAt m (fr.rdi + 8) s) :
    Initialize.StateAt n (fr.rdi + 8) s := by
  have h := out.1
  have addr : ((fr.rdi + 8) + 32).toNat = (fr.rdi + 8).toNat + 32 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change (fr.rdi + 8).toNat + 32 < 2^64; omega)]
    rfl
  refine ⟨UpdateV.Finalize.bytesAfter writes ?_ bytes.key, ?_⟩
  · exact ⟨by omega,fun r hr => by rcases out.2 r hr with _ | _ <;> omega⟩
  · have after := UpdateV.Finalize.bytesAfter writes
      (UpdateV.Finalize.outsideOffset out 32 32 (by decide) (by decide)) (by simpa only [addr] using bytes.value)
    simpa only [addr] using after

end K256.Proofs.Signing.Nonce.Fill
