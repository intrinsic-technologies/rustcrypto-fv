import K256.Proofs.Verify.Core.Lincomb.Geometry
import K256.Proofs.Verify.Core.Lincomb.Copy
import K256.Proofs.Verify.Hash.Update.Copy

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)



abbrev callResume (l : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨l, #v[], rfl, some ⟨64, ret⟩⟩

theorem reachesCall {site child after : Label} {a b : Registers} {m n : Ram}
    {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (call : program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩ =
      .call ⟨child,b,n⟩ (callResume after ret))
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨child,b,n⟩,[]⟩ out)
    (tag : out.tag = some ⟨64,ret⟩) :
    Reaches site a m after out.values out.store := by
  refine .step (b := ⟨⟨child,b,n⟩,[callResume after ret]⟩) ?_ ?_
  · simp only [Program.sem, Program.step, call, Transfer.next]
  · exact ParseSignature.exec_reaches_resume run _ [] (by rw [tag]; exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))

theorem copyCall {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m : Ram} {site after : Label} {ret : BitVec 64} {src dst len : Nat}
    (e : Entry fr a p digest r s) (whole : RamWriteFrame fr.original m [fr.region])
    (srcRoom : src + len ≤ 10952) (dstRoom : dst + len ≤ 10952)
    (disjoint : dst + len ≤ src ∨ src + len ≤ dst) (small : ret.toNat < 2^32)
    (call : program.runBlock (dialect Extracted.programImage) ⟨site,b,m⟩ =
      .call ⟨.l12a820,c,memStore m (workSp fr - 8) ret⟩ (callResume after ret))
    (rsp : c[4].get 64 = workSp fr - 8) (di : c[7].get 64 = slot fr dst)
    (si : c[6].get 64 = slot fr src) (dx : c[2].get 64 = BitVec.ofNat 64 len)
    (df : c[22].get 1 = 0) :
    ∃ d n, Reaches site b m after d n ∧ d[4] = ⟨64, workSp fr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → d[i] = c[i]) ∧
      Copied m (slot fr src) n (slot fr dst) len ∧ RamWriteFrame m n (workWrites fr 8 dst len) := by
  let pushed := memStore m (workSp fr - 8) ret
  have base := workNat e
  have room := e.stackRoom
  have high := e.low
  have push := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at push
  have source := slotNat e (k := src) (by omega)
  have destination := slotNat e (k := dst) (by omega)
  have bound : (BitVec.ofNat 64 len).toNat = len := Nat.mod_eq_of_lt (by omega)
  have slotW : Writable _ m (workSp fr - 8) 8 := belowWrite e whole (by decide)
  have pushedFrame : RamWriteFrame m pushed [scratch (workSp fr) 8] :=
    (RamWriteFrame.refl _ _).memStore ret ⟨_, List.mem_singleton_self _, by dsimp [InRegion,scratch]; omega⟩
  have tag : memLoad pushed (workSp fr - 8) 64 = ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have distinct : RangeApart (slot fr dst) len (workSp fr - 8) 8 := by
    intro i hi j hj eq
    have eq' := congrArg BitVec.toNat eq
    rw [toNat_add_ofNat (slot fr dst) i (by omega), toNat_add_ofNat (workSp fr - 8) j (by omega)] at eq'
    omega
  obtain ⟨out, run, store, returned, _, sp, keep⟩ :=
    Hash.Update.memcpy di si dx rsp df
      (by rw [bound]; exact (workWrite e whole srcRoom).readable.of_frame pushedFrame)
      (by rw [bound]; exact (workWrite e whole dstRoom).of_frame pushedFrame)
      (by rw [bound]; omega) (by rw [bound]; exact distinct) (slotW.readable.of_frame pushedFrame)
      (by rw [tag]; exact small)
  refine ⟨_, _, reachesCall call run (returned.trans (congrArg (fun x => some (Value.mk 64 x)) tag)),
    sp.trans (by rw [BitVec.sub_add_cancel]), keep, ?_, ?_⟩
  · intro k width hp hk
    rw [store, bound, Sec1.Parser.Result.memLoad_memCopy _ _ _ (by omega) hk]
    apply pushedFrame.memLoad_eq
    have eq := toNat_add_ofNat (slot fr src) k (by omega)
    refine ⟨by omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [scratch]
    omega
  · rw [store, bound]
    have f : RamWriteFrame m pushed (workWrites fr 8 dst len) :=
      (RamWriteFrame.refl _ _).memStore ret ⟨_, List.mem_cons_self .., by dsimp [InRegion,scratch]; omega⟩
    exact f.memStore _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by change (slot fr dst).toNat ≤ (slot fr dst).toNat ∧ (slot fr dst).toNat + 8*len/8 ≤ (slot fr dst).toNat + len ∧ (slot fr dst).toNat + 8*len/8 ≤ 2^64; omega⟩

end K256.Proofs.Verify.Core.Lincomb
