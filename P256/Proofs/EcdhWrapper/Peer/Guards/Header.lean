import P256.Proofs.EcdhWrapper.Peer.Guards.Tag
import P256.Proofs.EcdhWrapper.Peer.Guards.Length
import P256.Proofs.Sec1.Decode.Header.Model
import P256.Proofs.Program.Input
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem header [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1069db)
    (count : s.regValue .rbp = BitVec.ofNat 64 bytes.size)
    (bounded : (registerRegion s .r12 bytes.size).Bounded)
    (memory : (registerRegion s .r12 bytes.size).HasBytes s.external bytes)
    (shape : Sec1.EncodingShape bytes) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ t.RIP = 0x106a04 ∧
      AgreesExcept [.reg 0,.reg 1,.flags,.rip] s t := by
  have sizes := shape.size
  have positive : 0 < bytes.size := by omega
  have bound : bytes.size < 2^64 := by omega
  have accepted := (Sec1.Decode.Header.accepts_shape positive bound).mpr shape
  have pair : Sec1.Decode.Header.validTag (bytes.data[0]?.getD 0).toBitVec = true ∧
      BitVec.ofNat 64 bytes.size =
        Sec1.Decode.Header.expectedLength (bytes.data[0]?.getD 0).toBitVec := by
    simpa only [Sec1.Decode.Header.accepts,Bool.and_eq_true,beq_iff_eq] using accepted
  have first : s.external[s.regValue .r12]? = some (bytes.data[0]?.getD 0) := by
    have h := memory.2 ⟨0,positive⟩
    simpa only [registerRegion,MemoryRegion.start,Nat.add_zero,BitVec.ofNat_toNat,
      BitVec.setWidth_eq,Array.getElem?_eq_getElem positive,Option.getD_some,
      ByteArray.getElem_eq_getElem_data] using h
  have load : memLoad s.external (s.regValue .r12) 8 = (bytes.data[0]?.getD 0).toBitVec :=
    P256.Proofs.Common.Memory.memLoad8_of_byte first
  have readable : MemReadable s (s.regValue .r12) 1 := by
    exact memoryRegion_memReadable bounded (hasBytes_allocated memory)
      (Nat.le_refl _) (by change (s.regValue .r12).toNat+1 ≤ (s.regValue .r12).toNat+bytes.size; omega)
  obtain ⟨a,ra,readyA,ripA,cxA,ga⟩ := tag_branch ready loaded outside rip readable
    (by rw [load]; exact pair.1)
  have memA := ga.external (by simp [Component.Covers])
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded,memA] using loaded
  have countA : a.regValue .rbp = Sec1.Decode.Header.expectedLength (bytes.data[0]?.getD 0).toBitVec :=
    ((ga.read (n := 64) (r := 5) (by simp)).trans count).trans pair.2
  obtain ⟨t,rt,readyT,ripT,gt⟩ := length_branch readyA loadedA outside ripA
    (bytes.data[0]?.getD 0).toBitVec pair.1 (by simpa only [load] using cxA)
  refine ⟨t,ra.trans rt,readyT,?_,(ga.trans gt).mono (by simp)⟩
  simpa only [countA,ite_true] using ripT

end P256.Proofs.EcdhWrapper.Peer.Guards
