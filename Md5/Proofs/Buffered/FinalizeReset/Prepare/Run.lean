import Md5.Proofs.Buffered.FinalizeReset.Prepare.Execution
import Md5.Proofs.Buffered.FinalizeReset.Prepare.Setup
import Md5.Proofs.Buffered.FinalizeReset.Prepare.Memset

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run_to_memset {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre boundary message s variant) :
    ∃ u v t, (copyEffect s variant).Holds s u ∧ (setupEffect u variant).Holds u v ∧
      (∃ fuel, Advances boundary fuel s v) ∧ MemsetSiteResult boundary (variant.address 0x1007e6) v t := by
  have hsize := variant.stackBytes_bounds
  obtain ⟨n, u, ha, hu, hcu, hcopy⟩ :=
    copy_run hp.ready hp.code hp.toStorage hp.boundaryOutside hp.rip
  have hsu := copy_storage hp.toStorage hcopy
  have hpos : (.reg 15 : Operand 64).read u = BitVec.ofNat 64 (message.size % 64) :=
    hcopy.writes.1.trans (position_eq hp)
  have hbound : ((.reg 15 : Operand 64).read u).toNat < 64 := by
    rw [hpos, BitVec.toNat_ofNat]
    omega
  obtain ⟨m, v, hb, hv, hcv, hsetup⟩ :=
    setup_run hu hcu hsu hp.boundaryOutside hcopy.rip hbound
  have hdf : DirectionFlagClear u.RFLAGS :=
    (hcopy.agrees.directionFlagClear (by simp [copyEffect, Effect.components]) hp.df).df
  obtain ⟨t, ht⟩ := memset_run hp.stride hsu hpos (by omega) hdf hsetup hv hcv hp.boundaryOutside
  exact ⟨u, v, t, hcopy, hsetup, ⟨n + m, ha.trans hb⟩, ht⟩

end Md5.Proofs.Buffered.FinalizeReset.Prepare
