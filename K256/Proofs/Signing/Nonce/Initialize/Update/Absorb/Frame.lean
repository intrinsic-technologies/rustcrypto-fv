import K256.Proofs.Signing.Nonce.Initialize.Update.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev FrameTail (fr : Activation) (a : Verify.Core.Registers) (m : Ram) :=
  Atom.All Extracted.programImage a m ((Fn103f30.frameAt .l1048ba fr).drop 5)

def LocalWrites (fr : Activation) (rs : List MemoryRegion) : Prop :=
  ∀ r ∈ rs, fr.low.toNat ≤ r.start ∧ r.start + r.size ≤ fr.rsp.toNat - 48

theorem frameTailAfter {fr : Activation} {input : Input} {m n : Ram} {rs : List MemoryRegion}
    {a b : Verify.Core.Registers} (env : Environment fr input) (old : FrameTail fr a m)
    (writes : RamWriteFrame m n rs) (locality : LocalWrites fr rs) : FrameTail fr b n := by
  obtain ⟨bx, r12, r13, r14, r15, bp, rd, ret, small, win, room, align,
    rd₁, copy, rd₂, fill, gap, _⟩ := old
  change 0x204598 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at gap
  have depth := env.depth
  have limit := env.limit
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have keep (off : BitVec 64) (h : off.toNat ≤ 48) :
      memLoad n (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    have addr := BitVec.toNat_sub_of_le (show off ≤ fr.rsp from (by change off.toNat ≤ _; omega))
    apply writes.memLoad_eq
    refine ⟨by rw [addr]; change _ + 8 ≤ 2^64; omega, fun r hr => Or.inr ?_⟩
    have bound := (locality r hr).2
    rw [addr]
    omega
  have last := keep 0 (by decide)
  rw [show fr.rsp - 0 = fr.rsp by bv_omega] at last
  have got (p : BitVec 64) (lo : 0x203dd0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x203e18) :
      memLoad n p 64 = memLoad m p 64 := by
    apply writes.memLoad_eq
    refine ⟨by change _ + 8 ≤ 2^64; omega, fun r hr => ?_⟩
    obtain ⟨lower, upper⟩ := locality r hr
    change p.toNat + 8 ≤ _ ∨ _ ≤ p.toNat
    omega
  exact ⟨(keep 48 (by decide)).trans bx, (keep 40 (by decide)).trans r12,
    (keep 32 (by decide)).trans r13, (keep 24 (by decide)).trans r14,
    (keep 16 (by decide)).trans r15, (keep 8 (by decide)).trans bp,
    Readable.of_frame rd writes, last.trans ret, small, Writable.of_frame win writes, room, align,
    Readable.of_frame rd₁ writes, (got _ (by decide) (by decide)).trans copy,
    Readable.of_frame rd₂ writes, (got _ (by decide) (by decide)).trans fill, gap, trivial⟩

theorem liveAfter {fr : Activation} {input : Input} {state : State} {l k : Label}
    {m n : Ram} {a b : Verify.Core.Registers} {rs : List MemoryRegion}
    (env : Environment fr input) (old : Live l fr a m state) (writes : RamWriteFrame m n rs)
    (locality : LocalWrites fr rs) (atoms : Atom.All Extracted.programImage b n (Fn103f30.frameAt k fr))
    (widths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64)
    (label : k ≠ .l104951) : Live k fr b n state := by
  have stack : RamWriteFrame m n [fr.region] := by
    apply (RamWriteFrame.refl m _).trans writes
    intro r hr
    obtain ⟨lower, upper⟩ := locality r hr
    refine ⟨fr.region,List.mem_singleton_self _,lower,?_⟩
    change _ ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    omega
  exact ⟨atoms, old.writes.trans stack (fun r hr => ⟨r,by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩),
    env.stateAfter old.bytes stack, fun h => (label h).elim, widths⟩

theorem slotsAfter {fr : Activation} {m n : Ram} {rs : List MemoryRegion}
    (slots : Slots fr m) (writes : RamWriteFrame m n rs)
    (stop : Outside rs (sp fr + 8) 8) (value : Outside rs (sp fr + 112) 8)
    (state : Outside rs (sp fr + 120) 8) : Slots fr n :=
  ⟨(writes.memLoad_eq stop).trans slots.stop, (writes.memLoad_eq value).trans slots.value,
    (writes.memLoad_eq state).trans slots.state⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb
