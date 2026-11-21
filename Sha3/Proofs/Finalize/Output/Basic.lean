import Sha3.Proofs.Stores.WordMov
import Sha3.Proofs.Permutation.Compose
import Sha3.Proofs.Permutation.InstructionEffects

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_8B_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0x8b) (hm : bytes[j + 1]? = some modrm)
    (hj : j + 1 < 15) (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.MOV_GPRv_MEMv_1 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2)))
        ctx (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x8b modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode ↦ decodeLegacy0_run_of_opcode8B a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe ↦ decodeLegacy0Opcode8B_run_of_memory a u _ ctx _ hmod hmode hfe hf)

theorem mov_scan_r_m_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x8b :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t ↦
      writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem addr : Operand n).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x8b :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x8b :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_8B_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x8b reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [mov_r_m_form _ t _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip _ (SegAccess.flat _ _)
    (memAlu_dataReady h _) hmode
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8b _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_r32_m32_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x8b :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hw : MemReadable s (am.addrAt s (2 + am.tail.length)) 4) :
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") (.reg (gprNumber 0 0 reg) : Operand 32)
        (movSpec ((Operand.mem (am.addrAt s (2 + am.tail.length)) : Operand 32).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  exact mov_scan_r_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    rfl rfl rfl rfl reg am hv (AddrContext.legacy _ am hx hb) hcode hlow hw

def movR32M32LegacyEffect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 (2 + am.tail.length)
  writes := [⟨(Operand.reg dst : Operand 64),
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) :
      Operand 32).read s).setWidth 64⟩]

theorem mov_r32_m32_legacy_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s ↦ am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x8b :: am.modrm reg :: am.tail))
      (movR32M32LegacyEffect p (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have := am.tail_length_le
  refine ⟨_, mov_r32_m32_legacy_step s h reg am hv hx hb hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

end X86Proofs


namespace Sha3.Proofs.Finalize.Output

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure OutputPre (p ptr out : BitVec 64) (count : Nat) (source : Operand 64)
    (code : CodeMap) (s : RamState) : Prop where
  rip : s.RIP = p
  state : (Operand.reg 3 : Operand 64).read s = ptr
  pointer : source.read s = out
  stateRead : ∀ offset n, offset + n ≤ 200 → MemReadable s (ptr + BitVec.ofNat 64 offset) n
  outputRead : ∀ offset n, offset + n ≤ count → MemReadable s (out + BitVec.ofNat 64 offset) n
  tables : ∀ i < count, ¬ InPageTables (out + BitVec.ofNat 64 i)
  codeApart : ∀ i < count, ∀ x ∈ code, out + BitVec.ofNat 64 i ≠ x.1
  stateApart : RangeApart out count ptr 200

theorem OutputPre.load_store {p ptr out : BitVec 64} {count : Nat} {source : Operand 64}
    {code : CodeMap} {s : RamState} (hp : OutputPre p ptr out count source code s)
    (memory : Ram) (offset sourceOffset : BitVec 64) {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : offset.toNat + n / 8 ≤ count) (hsource : sourceOffset.toNat + width / 8 ≤ 200) :
    memLoad (memStore memory (out + offset) value)
      (ptr + sourceOffset) width =
      memLoad memory (ptr + sourceOffset) width := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi he
  apply hp.stateApart (offset.toNat + i) (by omega) (sourceOffset.toNat + j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.add_assoc] using he

theorem OutputPre.load_store_base {p ptr out : BitVec 64} {count : Nat}
    {source : Operand 64} {code : CodeMap} {s : RamState}
    (hp : OutputPre p ptr out count source code s) (memory : Ram)
    (offset : BitVec 64) {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : offset.toNat + n / 8 ≤ count) (hsource : width / 8 ≤ 200) :
    memLoad (memStore memory (out + offset) value) ptr width =
      memLoad memory ptr width := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    hp.load_store memory offset 0 value width houtput (by simpa using hsource)

theorem OutputPre.load_store_zero {p ptr out : BitVec 64} {count : Nat}
    {source : Operand 64} {code : CodeMap} {s : RamState}
    (hp : OutputPre p ptr out count source code s) (memory : Ram)
    (sourceOffset : BitVec 64) {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : n / 8 ≤ count) (hsource : sourceOffset.toNat + width / 8 ≤ 200) :
    memLoad (memStore memory out value) (ptr + sourceOffset) width =
      memLoad memory (ptr + sourceOffset) width := by
  simpa using hp.load_store memory 0 sourceOffset value width (by simpa using houtput) hsource

theorem OutputPre.store_tables {p ptr out : BitVec 64} {count : Nat} {source : Operand 64}
    {code : CodeMap} {s : RamState} (hp : OutputPre p ptr out count source code s)
    (offset n : Nat) (h : offset + n ≤ count) :
    ∀ i < n, ¬ InPageTables (out + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hp.tables (offset + i) (by omega)

theorem OutputPre.store_avoids {p ptr out : BitVec 64} {count : Nat} {source : Operand 64}
    {code : CodeMap} {s : RamState} (hp : OutputPre p ptr out count source code s)
    (offset : Nat) {n : Nat} (value : BitVec n) (next : BitVec 64)
    (h : offset + n / 8 ≤ count) :
    (Effect.mk next [⟨(Operand.mem (out + BitVec.ofNat 64 offset) : Operand n), value⟩] none).Avoids
      code := by
  intro x hx c hc
  simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rintro ⟨i, hi, he⟩
    apply hp.codeApart (offset + i) (by omega) x hx
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he.symm
  · exact id

end Sha3.Proofs.Finalize.Output

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem StorePreReadable.of_holds {e : Effect} {s s' : RamState} {p next : BitVec 64}
    {am : AddrMode} {len : Nat} (h : e.Holds s s') (ho : Obs (e.after s true) s')
    (hrip : e.rip = p) (hr : MemReadable s (am.addr (e.after s true) next) len)
    (htables : ∀ i < len, ¬ Sha3.Spec.Program.InPageTables
      (am.addr (e.after s true) next + BitVec.ofNat 64 i)) :
    StorePreReadable p (fun t ↦ am.addr t next) len s' := by
  refine ⟨LoadPre.of_holds h ho hrip (fun _ _ obs => AddrMode.addr_obs obs am next) hr, ?_⟩
  dsimp only
  rw [← AddrMode.addr_obs ho]
  exact htables

end X86Proofs

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem Operand.write_reg_external {n : Nat} (s : RamState) (reg : BitVec 5)
    (value : BitVec n) : ((Operand.reg reg : Operand n).write s value).external = s.external := rfl

theorem Operand.write_mem_external {n : Nat} (s : RamState) (address : BitVec 64)
    (value : BitVec n) : ((Operand.mem address : Operand n).write s value).external =
      memStore s.external address value := rfl

end X86Proofs

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem movR32M32LegacyEffect_local {p : BitVec 64} {dst : BitVec 5}
    {am : AddrMode} : Effect.Local (movR32M32LegacyEffect p dst am) := by
  effect_local [movR32M32LegacyEffect]

end X86Proofs
