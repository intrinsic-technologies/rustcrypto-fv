import Base16ct.Proofs.Copied.Md5.Spec.Program
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse

namespace Base16ct.Proofs.Copied.Md5.Proofs

open Base16ct.Proofs.Copied.Md5.Spec.Program Prelude X86 X86Proofs

theorem supportedIntegerMachineState_of_ready [bindings : Machine.Bindings]
    {s t : Machine.RamState} {cs : List Component}
    (h : ReadyToStep t) (he : AgreesExcept cs s t)
    (hs : Prelude.SupportedSSE bindings.processor s) :
    SupportedIntegerMachineState bindings.processor t :=
  ⟨h.cpu, X86Proofs.SupportedSSE.of_agreesExcept he hs, h.memory, h.ready⟩

theorem machineRamUnitStrideDecodable_of_ready [bindings : Machine.Bindings]
    {s : Machine.RamState} (h : ReadyToStep s) (hstride : UnitStringStride bindings) :
    MachineRamUnitStrideDecodable bindings s :=
  ⟨h.smrr, h.memoryType, hstride, h.features.lzcnt⟩

theorem memReadable_of_allocated {s : Machine.RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (h : region.Allocated s.external)
    (hlow : addr.toNat + len ≤ userAddressLimit)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  refine ⟨hlow, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply h
  have hi64 : i < 2^64 := by unfold userAddressLimit at hlow; omega
  have hsum : addr.toNat + i < 2^64 := by unfold userAddressLimit at hlow; omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem stack_return_readable {s : Machine.RamState} {bytes : Nat}
    (h : Stack.Valid s bytes) : MemReadable s (stackPtr s) 8 := by
  rcases h with ⟨hb, ha, hn, _⟩
  have hstart : (Stack.region s bytes).start ≤ (stackPtr s).toNat := by
    change (s.regValue .rsp).toNat - bytes ≤ (s.regValue .rsp).toNat
    omega
  have hend : (Stack.region s bytes).start + (Stack.region s bytes).size =
      (stackPtr s).toNat + 8 := by
    change ((s.regValue .rsp).toNat - bytes) +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - bytes)) =
      (s.regValue .rsp).toNat + 8
    omega
  apply memReadable_of_allocated ha
  · change (Stack.region s bytes).start + (Stack.region s bytes).size < userAddressLimit at hb
    omega
  · exact hstart
  · omega

theorem hasBytes_of_memoryWriteFrame {s t : Machine.RamState}
    {regions : Vector MemoryRegion n} {region : MemoryRegion} {bytes : ByteArray}
    (h : MemoryWriteFrame s t regions) (hb : region.HasBytes s.external bytes)
    (hbound : region.Bounded) (hsep : ∀ r ∈ regions, region.Disjoint r) :
    region.HasBytes t.external bytes := by
  refine ⟨hb.1, ?_⟩
  intro i
  rw [h _ (by
    intro r hr
    apply hsep r hr
    have hsize : bytes.size = region.size := hb.1
    have hlt : region.start + i.val < 2^64 := by
      unfold MemoryRegion.Bounded userAddressLimit at hbound
      omega
    simp only [MemoryRegion.Contains, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega)]
  exact hb.2 i

end Base16ct.Proofs.Copied.Md5.Proofs
