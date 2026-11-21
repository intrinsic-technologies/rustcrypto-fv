import K256.Proofs.Ecdh.Wrapper.Frame
import K256.Proofs.Generate.Generator.Affine.Memory

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.Generator.Affine

abbrev returnSlot (s : RamState) := s.regValue .rsp - 6160

theorem localSp_sub_eight (s : RamState) : localSp s - 8 = returnSlot s := by
  unfold localSp returnSlot
  bv_omega

theorem localOffset (s : RamState) (off : Nat) (h : off ≤ 6152) :
    localSp s + BitVec.ofNat 64 off = s.regValue .rsp - BitVec.ofNat 64 (6152 - off) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 6152 off (by omega) h]
  unfold localSp
  bv_omega

theorem callPushFrame {s : RamState} {secret peer : ByteArray} {mem : Ram} (ret : BitVec 64)
    (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (frame : RamWriteFrame s.external mem [Stack.region s ecdhDiffieHellman.minStackBytes]) :
    RamWriteFrame s.external (memStore mem (returnSlot s) ret)
      [Stack.region s ecdhDiffieHellman.minStackBytes] :=
  frame.memStore _ ⟨_, List.mem_cons_self, Common.stackRange (off := 6160) call.stackAvailable
    (by decide) (by decide)⟩

theorem affineSourceAt {s : RamState} {mem : Ram} {point : Standards.SECG.ECC.Curve.Point}
    (source : ProjectiveAt mem (localSp s + 344) point) (ret : BitVec 64) :
    ProjectiveAt (memStore mem (returnSlot s) ret) (localSp s + 344) point := by
  obtain ⟨x, y, z, xl, yl, zl, wx, wy, wz, rx, ry, rz, h⟩ := source
  refine ⟨x, y, z, xl, yl, zl, wx.write_apart _ _ ?_, wy.write_apart _ _ ?_,
    wz.write_apart _ _ ?_, rx, ry, rz, h⟩
  all_goals
    apply RangeApart.of_diff
    simp only [localSp, returnSlot]
    constructor <;> bv_omega

end K256.Proofs.Ecdh.Wrapper
