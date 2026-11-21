import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Small
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Large

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem correct [Bindings] (l : Layout) : Contract l := by
  intro initial s n reserve regions data wf flow code blocks stride machine stack avoids
    returnAddress state prepared apart within
  let ctx : Context l initial regions reserve :=
    ⟨wf,flow,code,blocks,stride,machine,stack,avoids,returnAddress,within⟩
  have input := Preserved.initial state prepared.rsp
  obtain ⟨u,inputU,select⟩ := run_stage ctx input .select prepared.rip
  have memory := select.agrees.external
    (by simp [Stage.effect,Effect.components,Component.Covers])
  have hasherU : HasherAt u (l.buffer (l.sp initial)) ByteArray.empty l.initialHash :=
    prepared.hasher.of_bytes (fun _ _ => by rw [memory])
  have sourceU : u.regValue .rsi=data.address :=
    (select.agrees.read (n := 64) (r := 6)
      (by simp [Stage.effect,Effect.components])).trans prepared.source
  have lengthU : u.regValue .r14=BitVec.ofNat 64 data.bytes.size :=
    (select.agrees.read (n := 64) (r := 14)
      (by simp [Stage.effect,Effect.components])).trans prepared.length
  have bytesU : data.region.HasBytes u.external data.bytes := by rw [memory]; exact prepared.bytes
  have low : data.address.toNat+data.bytes.size<2^32 := prepared.bounded
  have lengthNat : (s.regValue .r14).toNat=data.bytes.size := by
    rw [prepared.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ripU := select.rip
  change u.RIP=(if (s.regValue .r14).toNat≤63 then l.pc .smallSetup else l.pc .bulkSetup) at ripU
  rw [lengthNat] at ripU
  by_cases short : data.bytes.size≤63
  · rw [ite_eq_left short] at ripU
    exact small ctx inputU ripU hasherU sourceU lengthU bytesU prepared.bounded apart short
  · rw [ite_eq_right short] at ripU
    exact large ctx inputU ripU hasherU sourceU lengthU bytesU prepared.bounded apart

end Sha2.Proofs.Common.SHA256.Absorb.Direct
