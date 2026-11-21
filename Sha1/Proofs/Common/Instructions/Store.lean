import Sha1.Proofs.Common.Instructions.StorePre
import Sha1.Proofs.Common.Instructions.MemoryWriteFrame

namespace Sha1.Proofs.Common.Instructions.Store

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem storeEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) {n : Nat} (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    {s : RamState} (h : Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8) s) :
    (storeEffect p len addr v s).Avoids (codeRange p bytes) := by
  subst hlen
  exact Effect.avoids_of_components_mem_rip (storeEffect_components p _ addr v s) h.code


theorem storeEffect_step_pre [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect P (codeRange p bytes) (storeEffect p len addr v) := by
  intro s h hcode hs
  have hp := hpre s hs
  exact ⟨_, hstep s h hcode hs,
    Sha1.Proofs.Common.Instructions.MemoryWriteFrame.readyToStep_afterStep_store h _ _ _ _ hp.write.low hp.write.tables,
    ⟨afterStep_store_rip h _ _ _ _, Operand.read_afterStep_store s _ hn h64 _ _ _, trivial,
      AgreesExcept.afterStep_store s _ _ _ _⟩⟩


theorem storeEffect_step [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8)) (codeRange p bytes) (storeEffect p len addr v) :=
  storeEffect_step_pre hn h64 addr v (fun _ h => h) hstep


theorem storeEffect_triple_pre [Bindings] {P : RamState → Prop} {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} (hlen : bytes.length = len) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    Triple P (codeRange p bytes) (Effect.post (storeEffect p len addr v)) :=
  Triple.of_effect (fun s hs => storeEffect_avoids hlen addr v (hpre s hs))
    (storeEffect_step_pre hn h64 addr v hpre hstep)


theorem storeEffect_triple [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p len addr (n / 8)) (codeRange p bytes)
      (Effect.post (storeEffect p len addr v)) :=
  storeEffect_triple_pre hlen hn h64 addr v (fun _ h => h) hstep


end Sha1.Proofs.Common.Instructions.Store
