import AesGcm.Proofs.AES16.Encrypt.Prefix
import AesGcm.Proofs.AES16.Encrypt.Rounds
import AesGcm.Proofs.AES16.Encrypt.Final
import AesGcm.Proofs.AES16.Encrypt.Algebra
import AesGcm.Proofs.AES16.Encrypt.Initial
import Standards.NIST.AES.Cipher
import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.AES16.Sbox
import AesGcm.Proofs.AES16.Output
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn105100.Frame
import AesGcm.Proofs.Machine.LIR.Fn106960.Frame

namespace AesGcm.Proofs.Machine.AES16

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem encrypt_callContract (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (key : Vector UInt8 (variant use256).keyBytes)
    (input : Standards.NIST.AES.Block) :
    CallContract LIR.lifted code (if use256 then .l106960 else .l105100)
      (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo)
      (fun fr ↦ [span fr.rdi 16])
      (fun fr mem ↦ ScheduleIn (variant use256) key fr.rsi mem ∧
        Readable mem fr.rsi (16 * ((variant use256).Nr + 1)) ∧
        Readable mem fr.rdx 16 ∧ Fixslice.memoryBlock mem fr.rdx = Fixslice16.fromStandard input ∧
        Writable code mem fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16) ∧
        (callStack fr).Disjoint (span fr.rdx 16) ∧
        (callStack fr).Disjoint (span fr.rsi (16 * ((variant use256).Nr + 1))))
      (fun fr mem ↦ Fixslice.memoryBlock mem fr.rdi =
        Fixslice16.fromStandard (Standards.NIST.AES.cipher (variant use256) key input)) := by
  intro fr loc hlabel hstore hframe htyped hpre
  change Encrypt.Pre code use256 key input fr loc.store at hpre
  rw [hstore] at hpre
  obtain ⟨first, hprefix, hfirstWork, hfirstLoop⟩ :=
    Encrypt.prefix_exec use256 code hcode key input fr loc hlabel hstore hframe htyped hpre
  obtain ⟨last, hrounds, hlastWork, hlast⟩ :=
    Encrypt.rounds use256 code hcode key input fr first hpre.2.2.2.2.2.2.2 hfirstWork hfirstLoop
  obtain ⟨output, hfinish, hresult⟩ := Encrypt.finish use256 code hcode key input fr last
    hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2 hlastWork hlast
  refine ⟨output, X86Proofs.CFG.Program.Exec.of_sem
    ((hprefix.trans hrounds).exec hfinish.sem), ?_⟩
  exact hresult

end AesGcm.Proofs.Machine.AES16
