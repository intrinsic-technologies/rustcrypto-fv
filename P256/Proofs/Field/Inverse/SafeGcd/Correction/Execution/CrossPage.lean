import P256.Proofs.Common.Refine.Lemma.Store
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPageEffect
import P256.Proofs.Common.Lift.Footprint
import P256.Proofs.Common.Lift.Eval

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Lift P256.Proofs.CFG

theorem StorePre.of_stateOf {p : BitVec 64} {codeLen : Nat} {addr : RamState → BitVec 64}
    {len : Nat} {L : List Reg}
    (haddr : ∀ s, addr (stateOf p (entriesOf L s) s.external) = addr s) :
    ∀ s : RamState, s.RIP = p → StorePre p codeLen addr len
      (stateOf p (entriesOf L s) s.external) → StorePre p codeLen addr len s := by
  intro s hrip h
  obtain ⟨-, hr, ht, hc⟩ := h
  rw [haddr] at hr ht hc
  exact ⟨hrip, hr.of_external_eq (stateOf_external _ _ _).symm, ht, hc⟩

theorem StorePre.of_addr {p q : BitVec 64} {codeLen : Nat} {am : AddrMode} {len : Nat}
    {L : List Reg} (h : addrRegsIn am L = true) :
    ∀ s : RamState, s.RIP = p → StorePre p codeLen (fun s ↦ am.addr s q) len
      (stateOf p (entriesOf L s) s.external) →
        StorePre p codeLen (fun s ↦ am.addr s q) len s :=
  StorePre.of_stateOf fun s ↦ addr_stateOf am s (fun _ ↦ mem_of_addrRegsIn h) q

structure StoreOk (code : CodeMap) (mem : Ram) (a : BitVec 64) (len : Nat) (p : BitVec 64)
    (codeLen : Nat) : Prop where
  low : a.toNat + len ≤ 2^32
  present : ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome
  tables : PageTableEntriesApart a.toNat len
  apart : RangeApart a len p codeLen
  notCode : ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i

theorem guard_store_iff {t : RamState} {p : BitVec 64} {code : CodeMap} {mem : Ram}
    {e : RamState → Effect} {codeLen len : Nat} {addr : RamState → BitVec 64}
    (hrip : t.RIP = p) (hext : t.external = mem)
    (hmem : (e t).components.filter Component.isMem = [.mem (addr t) len]) :
    Guard code (StorePre p codeLen addr len) e t mem ↔ StoreOk code mem (addr t) len p codeLen := by
  subst mem
  constructor
  · rintro ⟨⟨-, hr, ht, hc⟩, ha, -⟩
    exact ⟨hr.low, hr.mem, ht, hc, (avoids_iff_of_mem hmem).mp ha⟩
  · intro h
    exact ⟨⟨hrip, ⟨h.low, h.present⟩, h.tables, h.apart⟩,
      (avoids_iff_of_mem hmem).mpr h.notCode, (writesPresent_iff_of_mem hmem).mpr h.present⟩

open Classical in
theorem eval_exec_store {code : CodeMap} {mem : Ram} {p : BitVec 64}
    {e : RamState → Effect} {R : List Reg} {args : Values Value R.length}
    {codeLen len : Nat} {addr : RamState → BitVec 64}
    (hmem : ∀ t, (e t).components.filter Component.isMem = [.mem (addr t) len]) :
    Op.eval code (.exec p (StorePre p codeLen addr len) e R) args mem =
      if StoreOk code mem (addr (Op.state p R args mem)) len p codeLen then
        some (⟨1, 0⟩, (applyWrites (Op.state p R args mem) (e (Op.state p R args mem)).writes).external)
      else none := by
  rw [Op.eval_exec, propext (guard_store_iff (Op.state_RIP R args) (Op.state_external R args)
    (hmem _))]

open Classical in
theorem eval_exec_storeEffect {code : CodeMap} {mem : Ram} {p : BitVec 64}
    {R : List Reg} {args : Values Value R.length} {codeLen n : Nat}
    {addr : RamState → BitVec 64} {v : RamState → BitVec n} :
    Op.eval code (.exec p (StorePre p codeLen addr (n / 8)) (storeEffect p codeLen addr v) R)
      args mem =
      if StoreOk code mem (addr (Op.state p R args mem)) (n / 8) p codeLen then
        some (⟨1, 0⟩, memStore mem (addr (Op.state p R args mem)) (v (Op.state p R args mem)))
      else none := by
  rw [eval_exec_store (fun _ ↦ rfl)]
  simp only [storeEffect, applyWrites_mem_external, Op.state_external]

open Classical in
@[cfg_eval ↓] theorem movM64R64Effect_exec {code : CodeMap} {mem : Ram} {p : BitVec 64}
    {R : List Reg} {args : Values Value R.length} (src : BitVec 5) (am : AddrMode)
    (len : Nat) (hlen : 3 + am.tail.length = len) :
    Op.eval code (.exec p (StorePre p len
      (fun s ↦ am.addr s (p + BitVec.ofNat 64 len)) 8)
      (movM64R64Effect p src am) R) args mem =
      if StoreOk code mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 len))
          8 p len then
        some (⟨1, 0⟩, memStore mem
          (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 len))
          ((Operand.reg src : Operand 64).read (Op.state p R args mem)))
      else none := by
  subst len
  exact eval_exec_storeEffect (n := 64)

theorem StoreOk.of_region {code : CodeMap} {mem : Ram} {a b p : BitVec 64}
    {len n codeLen : Nat} (h : P256.Proofs.Refine.Writable code mem b len)
    (hstart : b.toNat ≤ a.toNat) (hend : a.toNat + n ≤ b.toNat + len)
    (hap : RangeApart a n p codeLen) : StoreOk code mem a n p codeLen :=
  let h' := h.sub hstart hend
  ⟨h'.readable.low, h'.readable.present, h'.tables, hap, h'.notCode⟩

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
