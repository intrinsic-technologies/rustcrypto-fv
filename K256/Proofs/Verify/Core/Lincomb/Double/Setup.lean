import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine K256.Proofs.Verify.LIR
  Common.Tactic Generate.Generator.Multiply.Prepare

abbrev localStack (sp : BitVec 64) : BitVec 64 := sp - 0x228

def savedStack (a : Registers) (m : Ram) (sp : BitVec 64) : Ram :=
  memStore
    (memStore
      (memStore
        (memStore
          (memStore
            (memStore m (sp - 8) (a[5].get 64))
            (sp - 16) (a[15].get 64))
          (sp - 24) (a[14].get 64))
        (sp - 32) (a[13].get 64))
      (sp - 40) (a[12].get 64))
    (sp - 48) (a[3].get 64)

abbrev copyPoint (m : Ram) (q src : BitVec 64) := memCopy m (q + 0x128) src 120

theorem stackOffset {sp q : BitVec 64} {k : Nat} (hq : q = localStack sp)
    (room : 0x298 ≤ sp.toNat) (high : sp.toNat ≤ 2^32) (hk : k ≤ 0x228) :
    (q + BitVec.ofNat 64 k).toNat = sp.toNat - 0x228 + k := by
  rw [hq, BitVec.toNat_add, BitVec.toNat_sub_of_le (by exact show 0x228 ≤ sp.toNat by omega)]
  simp only [BitVec.reduceToNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem savedFrame {a : Registers} {m : Ram} {sp : BitVec 64}
    (room : 0x298 ≤ sp.toNat) (high : sp.toNat ≤ 2^32) :
    RamWriteFrame m (savedStack a m sp) [scratch sp 0x298] := by
  have inside (k : Nat) (hk : 8 ≤ k) (hk' : k ≤ 0x298) :
      InRegions [scratch sp 0x298] (sp - BitVec.ofNat 64 k) 8 := by
    have kn : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    have nat : (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
      rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 k).toNat ≤ sp.toNat; rw [kn]; omega), kn]
    refine ⟨_, .head _, ?_⟩
    change sp.toNat - 0x298 ≤ (sp - BitVec.ofNat 64 k).toNat ∧
      (sp - BitVec.ofNat 64 k).toNat + 8 ≤ sp.toNat - 0x298 + 0x298 ∧
      (sp - BitVec.ofNat 64 k).toNat + 8 ≤ 2^64
    rw [nat]
    omega
  have f := (RamWriteFrame.refl m _).memStore (a[5].get 64) (inside 8 (by decide) (by decide))
  have f := f.memStore (a[15].get 64) (inside 16 (by decide) (by decide))
  have f := f.memStore (a[14].get 64) (inside 24 (by decide) (by decide))
  have f := f.memStore (a[13].get 64) (inside 32 (by decide) (by decide))
  have f := f.memStore (a[12].get 64) (inside 40 (by decide) (by decide))
  exact f.memStore (a[3].get 64) (inside 48 (by decide) (by decide))

private theorem blockCode : ∀ x ∈ codeRange 0x110cd0 bytes_l110cd0,
    x ∈ Extracted.programImage :=
  fun x hx => Common.fnCode_subset_programImage x (code_l110cd0 x hx)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem firstSquareSetup {a : Registers} {m : Ram} {sp src dst : BitVec 64}
    (e : RoutineEntry a m sp 0x298) (si : a[6].get 64 = src) (di : a[7].get 64 = dst)
    (read : Readable m src 120) (separate : Outside [scratch sp 0x298] src 120) :
    let q := localStack sp
    let beforeCopy := memStore (savedStack a m sp) (q + 0x1a0) dst
    let afterCopy := copyPoint beforeCopy q src
    let n := memStore afterCopy (q - 8) (0x110d0e : BitVec 64)
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l110cd0,a,m⟩ =
      .call ⟨.l1145f0,b,n⟩ ⟨.l110d0e,#v[],rfl,some ⟨64,0x110d0e⟩⟩ ∧
      b[4] = ⟨64,q-8⟩ ∧ b[6] = ⟨64,q+0x150⟩ ∧ b[7] = ⟨64,q+0x1a8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n [scratch sp 0x298] := by
  intro q beforeCopy afterCopy n
  have room : 0x298 ≤ sp.toNat := e.room
  have lowNat : (sp - 0x298).toNat = sp.toNat - 0x298 :=
    BitVec.toNat_sub_of_le (by exact e.room)
  have top := e.stack.readable.low
  change (sp - 0x298).toNat + 0x298 ≤ 2^32 at top
  rw [lowNat] at top
  have high : sp.toNat ≤ 2^32 := by omega
  have ptr (k : Nat) (hk : k ≤ 0x228) :
      (q + BitVec.ofNat 64 k).toNat = sp.toNat - 0x228 + k :=
    stackOffset rfl e.room high hk
  have inStack (k len : Nat) (hk : k + len ≤ 0x228) :
      InRegions [scratch sp 0x298] (q + BitVec.ofNat 64 k) len := by
    refine ⟨_, .head _, ?_⟩
    change sp.toNat - 0x298 ≤ (q + BitVec.ofNat 64 k).toNat ∧
      (q + BitVec.ofNat 64 k).toNat + len ≤ sp.toNat - 0x298 + 0x298 ∧
      (q + BitVec.ofNat 64 k).toNat + len ≤ 2^64
    rw [ptr k (by omega)]
    omega
  have calleeStack : (q - 8).toNat = sp.toNat - 0x230 := by
    change (sp - 0x228 - 8).toNat = _
    rw [show sp - 0x228 - 8 = sp - 0x230 by bv_omega]
    exact BitVec.toNat_sub_of_le (by exact show 0x230 ≤ sp.toNat by omega)
  have f0 := savedFrame (a := a) (m := m) e.room high
  have f1 : RamWriteFrame m beforeCopy [scratch sp 0x298] := f0.memStore dst (inStack 0x1a0 8 (by decide))
  have f2 : RamWriteFrame m afterCopy [scratch sp 0x298] :=
    Sec1.Wrapper.Copy.memCopy_frame f1 (inStack 0x128 120 (by decide))
  have f3 : RamWriteFrame m n [scratch sp 0x298] := by
    apply f2.memStore
    refine ⟨_, .head _, ?_⟩
    change sp.toNat - 0x298 ≤ (q - 8).toNat ∧
      (q - 8).toNat + 8 ≤ sp.toNat - 0x298 + 0x298 ∧ (q - 8).toNat + 8 ≤ 2^64
    rw [calleeStack]
    omega
  have copyRead : Readable beforeCopy src 120 := read.of_frame f1
  have copyApart : src.toNat + 8 * (15 : BitVec 64).toNat ≤ (q + 0x128).toNat ∨
      (q + 0x128).toNat + 8 * (15 : BitVec 64).toNat ≤ src.toNat := by
    have hs := separate.2 _ (List.mem_cons_self)
    change src.toNat + 120 ≤ sp.toNat - 0x298 ∨ sp.toNat - 0x298 + 0x298 ≤ src.toNat at hs
    change src.toNat + 120 ≤ (q + BitVec.ofNat 64 0x128).toNat ∨
      (q + BitVec.ofNat 64 0x128).toNat + 120 ≤ src.toNat
    rw [ptr 0x128 (by decide)]
    omega
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) e.rsp
  have df : a[22].get 1 = 0 := congrArg (Value.get 1) e.df
  have win : Writable Extracted.programImage m (sp - 0x298) 0x298 := e.stack
  have destCopy : Writable Extracted.programImage beforeCopy (q + 0x128) 120 :=
    (win.of_frame f1).of_offsets (x := sp) (c := 0 - 0x100) (d := 0 - 0x298)
      (by dsimp only [q,localStack]; bv_omega) (addr_sub _ _) (by decide)
  have rep : RepMovsOk Extracted.programImage beforeCopy 0 src (q + 0x128) 15 8 0x110cf6 3 :=
    copyGuard copyRead (ParseSignature.storeOk_of_codeRange (off := 0x26) destCopy blockCode (by decide))
      copyApart
  have localDst : q + 0x1a0 = sp - 136 := by dsimp only [q,localStack]; bv_omega
  have localCopy : q + 0x128 = sp - 256 := by dsimp only [q,localStack]; bv_omega
  have localLink : q - 8 = sp - 560 := by dsimp only [q,localStack]; bv_omega
  have localY : q + 0x150 = sp - 216 := by dsimp only [q,localStack]; bv_omega
  have localYY : q + 0x1a8 = sp - 128 := by dsimp only [q,localStack]; bv_omega
  have linkWrite : Writable Extracted.programImage afterCopy (q - 8) 8 :=
    (win.of_frame f2).of_offsets (x := sp) (c := 0 - 0x230) (d := 0 - 0x298)
      (by rw [localLink]; exact addr_sub _ _) (addr_sub _ _) (by decide)
  have linkGuard : StoreOk Extracted.programImage afterCopy (q - 8) 8 0x110d09 5 :=
    ParseSignature.storeOk_of_codeRange (off := 0x39) linkWrite blockCode (by decide)
  refine ⟨?_, ?run, ?_, ?_, ?_, ?keep, f3⟩
  case run =>
    cfg_eval [rsp,si,di,df,BitVec.sub_sub,BitVec.reduceAdd]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using blockCode)
    rw [← localDst, ← localCopy, ← localLink, ← localY, ← localYY]
    change (if False ∨ RepMovsOk Extracted.programImage beforeCopy 0 src (q+0x128) 15 8 0x110cf6 3
      then if StoreOk Extracted.programImage afterCopy (q-8) 8 0x110d09 5 then _ else _
      else _) = _
    rw [ite_eq_left (Or.inr rep), ite_eq_left linkGuard]
    rfl
  case keep =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  all_goals rfl

end K256.Proofs.Verify.Core.Lincomb.Double
