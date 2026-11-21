import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.Memory
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.State
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.HighLimb
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.HighScan
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.MiddleScan
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.LowScan
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.Length
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.Count
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.Setup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

theorem prefix_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (registers : EntryRegisters initial s) (rip : s.RIP = 0x106f4e) :
    ∃ t, Stage initial t boundary ∧ LoopRegisters initial t 0 ∧ t.RIP = 0x107050 := by
  obtain ⟨a, high⟩ := Prefix.high_limb_correct pre stage registers rip
  obtain ⟨b, highScan⟩ := Prefix.high_scan_correct pre high
  obtain ⟨c, middleScan⟩ := Prefix.middle_scan_correct pre highScan
  obtain ⟨d, lowScan⟩ := Prefix.low_scan_correct pre middleScan
  obtain ⟨e, length⟩ := Prefix.length_correct pre lowScan
  obtain ⟨f, count⟩ := Prefix.count_correct pre length
  exact Prefix.setup_correct pre count

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
