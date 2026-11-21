import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success.Run
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success.Tail
import P256.Proofs.SignatureWrapper.Epilogue.Success.Output
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Restore
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
open P256.Proofs.SignatureWrapper.Epilogue.Success (bytes_encodeFixed)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

set_option maxHeartbeats 800000 in
theorem accept [bindings : Bindings] {initial t : RamState} {value : Nat × Nat}
    (pre : Pre initial) (state : State initial t)
    (low : (returnBoundary initial).rip.toNat < 2^32) (rip : t.RIP = 0x1022b1)
    (first : Nat256At t (stackPtr initial - 80) value.1)
    (second : Nat256At t (stackPtr initial - 48) value.2) :
    ∃ fuel u, Returns (returnBoundary initial) fuel t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧ SuccessfulStatus u ∧
      MemoryWriteFrame t u #v[registerRegion initial .rcx 72] ∧
      readOutput signatureFromSlice initial u = .ok (Ecdsa.encodeFixed value) := by
  obtain ⟨b,hb,sb,ipb,fb⟩ := capacity_payload pre state rip
  have mb := fb.external (by simp [Component.Covers])
  obtain ⟨nc,c,hc,sc,ipc,frameC,wordsC⟩ := serialize_run pre sb ipb
  have payloadC (part : Bool) (j : Nat) (hj : j < 4) :
      memLoad c.external (initial.regValue .rcx + (if part then 40 else 8) + BitVec.ofNat 64 (8*j)) 64 =
        bswap64 (BitVec.ofNat 64 ((if part then value.2 else value.1) / 2^(64*(3-j)))) := by
    rw [wordsC part j hj]
    congr 1
    have loc : stackPtr b + (if part then 40 else 8) =
        stackPtr initial - (if part then 48 else 80) := by
      rw [sb.rsp]
      cases part <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
    rw [loc, mb]
    cases part
    · exact first.memLoad_limb (3-j) (by omega)
    · exact second.memLoad_limb (3-j) (by omega)
  obtain ⟨g,hg,sg,ipg,axg,lengthG,fg⟩ := finish_store pre sc ipc
  have payloadG (part : Bool) (j : Nat) (hj : j < 4) :
      memLoad g.external (initial.regValue .rcx + (if part then 40 else 8) + BitVec.ofNat 64 (8*j)) 64 =
        bswap64 (BitVec.ofNat 64 ((if part then value.2 else value.1) / 2^(64*(3-j)))) := by
    have keep : memLoad g.external (initial.regValue .rcx + (if part then 40 else 8) + BitVec.ofNat 64 (8*j)) 64 =
        memLoad c.external (initial.regValue .rcx + (if part then 40 else 8) + BitVec.ofNat 64 (8*j)) 64 := by
      apply memLoad_congr
      intro i hi
      change (g.external[initial.regValue .rcx + (if part then 40 else 8) + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 i]?).getD 0 = _
      rw [fg.byte ?_]
      · rfl
      · intro c hc hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        all_goals try exact hv.elim
        obtain ⟨k,hk,heq⟩ := hv
        have heq' : BitVec.ofNat 64 ((if part then 40 else 8) + 8*j + i) = BitVec.ofNat 64 k := by
          apply (BitVec.add_right_inj (initial.regValue .rcx)).mp
          cases part <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
            BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using heq
        have h := congrArg BitVec.toNat heq'
        simp only [BitVec.toNat_ofNat] at h
        cases part <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;> omega
    rw [keep]
    exact payloadC part j hj
  obtain ⟨u,hu,machine,bindingsSupported,saved,direction,mu,axu⟩ :=
    Return.restore (locals := 72) sg pre.stack (by decide) pre.outside low 0x2320
      ⟨by decide, by decide, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ ipg
  have frame : MemoryWriteFrame t u #v[registerRegion initial .rcx 72] := by
    intro x hx
    have keepG : g.external[x]? = c.external[x]? := fg.byte (by
      intro comp hcomp hcovers
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hcomp
      rcases hcomp with rfl | rfl | rfl | rfl
      all_goals try exact hcovers.elim
      apply hx (registerRegion initial .rcx 72) (by simp)
      exact output_contains pre (off := 0) (len := 8) (by decide)
        (by simpa only [BitVec.add_zero] using hcovers))
    rw [mu, keepG, frameC x hx, mb]
  have output : readOutput signatureFromSlice initial u = .ok (Ecdsa.encodeFixed value) := by
    have size := P256.Proofs.SignatureFromDer.encodeFixed_size value
    apply readOutput_of_bytes (by rw [size]; decide)
    · have allocated := (output_writable pre sg).add 0 (len := 8) (by decide)
      have hb := Bytes.of_memLoad (n := 64) (by
        intro i hi
        simpa only [BitVec.add_zero] using allocated.mem i hi)
      rw [lengthG] at hb
      change Bytes u.external (initial.regValue .rcx) 8
        (storedByte (BitVec.ofNat 64 (Ecdsa.encodeFixed value).size))
      rw [mu,size]
      exact hb
    · change ∀ i < (Ecdsa.encodeFixed value).size,
        u.external[initial.regValue .rcx + 8 + BitVec.ofNat 64 i]? = some (Ecdsa.encodeFixed value).data[i]!
      rw [mu]
      apply bytes_encodeFixed
      · exact ((output_writable pre sg).add 8 (len := 64) (by decide)).mem
      · exact payloadG false
      · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Bool.true_eq, ite_true] using payloadG true
  refine ⟨_,u,(((hb.trans hc).trans hg).returns hu),
    machine,bindingsSupported,saved,direction,?_,frame,output⟩
  change (u.regValue .rax).setWidth 32 = 0
  rw [axu,axg]
  rfl

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success
