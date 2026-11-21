import Sha3.Proofs.Memcpy.Contract
import Sha3.Proofs.Memcpy.Prefix
import Sha3.Proofs.Memcpy.ScalarBlocks

namespace Sha3.Proofs.Memcpy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem return_steps [Bindings] {len : Nat} {aligned : Bool}
    (boundary : ReturnBoundary) (s f : RamState)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s len aligned)
    (hf : ReadyToStep f) (hcf : CodeIn Extracted.programImage f)
    (fip : f.RIP = 0x106a9e) (fsp : stackPtr f = stackPtr s)
    (frax : (Operand.reg 0 : Operand 64).read f = (Operand.reg 7 : Operand 64).read s)
    (sfFrame : AgreesExcept (clobbers ((Operand.reg 7 : Operand 64).read s) len) s f)
    (fcopy : ∀ i < len, f.external[(Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 i]? =
      s.external[(Operand.reg 6 : Operand 64).read s + BitVec.ofNat 64 i]?) :
    ∃ t, Advances boundary 1 f t ∧ Done s t len := by
  have ftop : stackTop f = stackTop s := clobbers_stackTop sfFrame fsp h.disjoint
  have fr : RetPre 0x106a9e f := ⟨⟨fip, by
    rw [fsp]
    exact MemReadable.of_agreesExcept sfFrame h.stack⟩, by rw [ftop]; exact h.returnLow⟩
  obtain ⟨t, hft, ht, het⟩ := ret_effect_step 0x106a9e f hf
    (instruction_codeIn hcf (by decide +kernel)) fr
  have tsp : stackPtr t = stackPtr s + 8 :=
    het.writes.trans (congrArg (· + 8) fsp)
  have tip : t.RIP = stackTop s := het.rip.trans ftop
  have hat : Advances boundary 1 f t := Advances.of_step hft (by
    rcases h.afterReturn with hrip | hrsp
    · exact .inl (tip ▸ hrip)
    · right
      change stackPtr t ≠ boundary.rsp
      rw [tsp]
      exact hrsp)
  have tf : AgreesExcept (clobbers ((Operand.reg 7 : Operand 64).read s) len) f t := het.agrees.mono (by
    intro q hq
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [clobbers])
  have tframe := agrees_clobbers_trans sfFrame tf
  refine ⟨t, hat, ht, clobbers_code tframe h.destination.low h.program hcode,
    tip, tsp, ?_, ?_, tframe⟩
  · exact (het.agrees.read (n := 64) (r := 0)
      (by rw [retEffect_components]; decide)).trans frax
  · have tmem : t.external = f.external := het.agrees.external
      (by simp [retEffect_components, Component.Covers])
    simpa only [tmem] using fcopy

theorem copy_stage [inst : Bindings] (hstride : UnitStringStride inst)
    {byte : Bool} {len off count : Nat} {aligned : Bool}
    (boundary : ReturnBoundary) (s a : RamState) (h : Pre boundary s len aligned)
    (ha : ReadyToStep a) (hca : CodeIn Extracted.programImage a)
    (p : BitVec 64) (rex : UInt8) (hrex : byte = false → RexWPrefix rex.toBitVec)
    (hmem : (p, movsCode byte rex) ∈ instructionBytes) (hip : a.RIP = p)
    (hcount : rcx.read a = BitVec.ofNat 64 count) (hsmall : count < 2^64)
    (hsrc : rsi.read a = rsi.read s + BitVec.ofNat 64 off)
    (hdst : rdi.read a = rdi.read s + BitVec.ofNat 64 off)
    (hsp : stackPtr a = stackPtr s)
    (hbound : off + movsBytes byte * count ≤ len)
    (halign : (rdi.read a).toNat % movsBytes byte = 0)
    (hframe : AgreesExcept (clobbers (rdi.read s) len) s a)
    (hcopy : ∀ i < off, a.external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]?) :
    ∃ b, Advances boundary (max count 1) a b ∧ ReadyToStep b ∧
      CodeIn Extracted.programImage b ∧ b.RIP = p + BitVec.ofNat 64 (movsLength byte) ∧
      rsi.read b = rsi.read s + BitVec.ofNat 64 (off + movsBytes byte * count) ∧
      rdi.read b = rdi.read s + BitVec.ofNat 64 (off + movsBytes byte * count) ∧
      stackPtr b = stackPtr s ∧
      (Operand.reg 0 : Operand 64).read b = (Operand.reg 0 : Operand 64).read a ∧
      (Operand.reg 2 : Operand 64).read b = (Operand.reg 2 : Operand 64).read a ∧
      (Operand.reg 8 : Operand 64).read b = (Operand.reg 8 : Operand 64).read a ∧
      AgreesExcept (clobbers (rdi.read s) len) s b ∧
      (∀ i < off + movsBytes byte * count,
        b.external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]?) := by
  have hn : (rcx.read a).toNat = count := by simp only [hcount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  have hb : off + movsBytes byte * (rcx.read a).toNat ≤ len := by simpa only [hn] using hbound
  have hp := h.movsPre hframe hip hsrc hdst hb halign hmem
  obtain ⟨b, hab, hr, hc, he, hnew, hf⟩ := movs_steps hstride boundary p rex hrex hmem
    a ha hca hp (hsp ▸ h.inside) (by
      rw [hdst]
      exact avoids_subrange h.destination.low hb h.program)
  rw [hn] at hab hnew hf
  have hw := he.writes
  change (rsi.read b = rsi.read a + BitVec.ofNat 64 (movsBytes byte * (rcx.read a).toNat)) ∧
    (rdi.read b = rdi.read a + BitVec.ofNat 64 (movsBytes byte * (rcx.read a).toNat)) ∧ _ at hw
  rw [hn, hsrc, hdst, add_ofNat_add_ofNat, add_ofNat_add_ofNat] at hw
  rw [hsrc, hdst] at hnew
  rw [hdst] at hf
  refine ⟨b, hab, hr, hc, he.rip, hw.1, hw.2.1, ?_, ?_, ?_, ?_,
    agrees_clobbers_trans hframe (clobbers_subrange hf hbound),
    copy_extend h.source.low h.destination.low h.separate hbound hframe hf hcopy hnew⟩
  · exact (he.agrees.read (n := 64) (r := 4) (by rw [repMovsEffect_components]; simp)).trans hsp
  · exact he.agrees.read (n := 64) (r := 0) (by rw [repMovsEffect_components]; simp)
  · exact he.agrees.read (n := 64) (r := 2) (by rw [repMovsEffect_components]; simp)
  · exact he.agrees.read (n := 64) (r := 8) (by rw [repMovsEffect_components]; simp)

theorem memcpy_steps [inst : Bindings] (hstride : UnitStringStride inst)
    {len : Nat} {aligned : Bool} (hlen : 8 ≤ len)
    (boundary : ReturnBoundary) (s : RamState) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s len aligned) :
    let lead := (8 - (rdi.read s).toNat % 8) % 8
    ∃ t, Advances boundary
      (13 + max lead 1 + max ((len - lead) / 8) 1 + max ((len - lead) % 8) 1) s t ∧
      Done s t len := by
  let lead := (8 - (rdi.read s).toNat % 8) % 8
  have hl : lead < 8 := Nat.mod_lt _ (by decide)
  have hlen64 : len < 2^64 := by have := h.source.low; omega
  have hl64 : lead < 2^64 := by omega
  have hn : (BitVec.ofNat 64 len - BitVec.ofNat 64 lead).toNat = len - lead := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hl64]; omega)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hl64]
  obtain ⟨a, hsa, ha, hca, hpa⟩ := prefix_steps_general (lead := BitVec.ofNat 64 lead) s hready hcode h.rip h.length
    (neg_mask_nat _) (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64,
      Nat.mod_eq_of_lt hlen64]; omega) boundary h.inside
  have asp : stackPtr a = stackPtr s := hpa.agrees.read (n := 64) (r := 4) (by decide)
  have asrc : rsi.read a = rsi.read s + BitVec.ofNat 64 0 := by
    simpa only [BitVec.add_zero] using hpa.agrees.read (n := 64) (r := 6) (by decide)
  have adst : rdi.read a = rdi.read s + BitVec.ofNat 64 0 := by
    simpa only [BitVec.add_zero] using hpa.agrees.read (n := 64) (r := 7) (by decide)
  have saframe : AgreesExcept (clobbers (rdi.read s) len) s a := hpa.agrees.mono (by
    intro q hq
    simp only [scalarClobbers, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clobbers])
  obtain ⟨b, hab, hb, hcb, bip, bsrc, bdst, bsp, brax, brdx, br8, sbframe, bcopy⟩ :=
    copy_stage hstride (byte := true) boundary s a h ha hca 0x106a87 0
      (by simp) (by decide +kernel) hpa.rip hpa.rcx hl64 asrc adst asp
      (by change 0 + 1 * lead ≤ len; omega) (by change _ % 1 = 0; exact Nat.mod_one _) saframe (by omega)
  simp only [movsBytes, ite_true, Nat.one_mul, Nat.zero_add] at bsrc bdst bcopy
  obtain ⟨c, hbc, hc, hcc, cip, crc, crdx, hfbc⟩ := prepare_steps_general b hb hcb bip
    (brdx.trans hpa.rdx) (br8.trans hpa.r8) boundary (bsp ▸ h.inside)
  have cc : rcx.read c = BitVec.ofNat 64 ((len - lead) / 8) := by
    rw [crc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, hn, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (len - lead) / 8 < 2^64)]
  have cf : AgreesExcept (clobbers (rdi.read s) len) b c := hfbc.mono (by
    intro q hq
    simp only [loopClobbers, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [clobbers])
  have csp : stackPtr c = stackPtr s := (hfbc.read (n := 64) (r := 4) (by decide)).trans bsp
  have csrc := (hfbc.read (n := 64) (r := 6) (by decide)).trans bsrc
  have cdst := (hfbc.read (n := 64) (r := 7) (by decide)).trans bdst
  have crax := (hfbc.read (n := 64) (r := 0) (by decide)).trans (brax.trans hpa.rax)
  have cmem : c.external = b.external := hfbc.external (by simp [loopClobbers, Component.Covers])
  obtain ⟨d, hcd, hd, hcdcode, dip, dsrc, ddst, dsp, drax, drdx, _, sdframe, dcopy⟩ :=
    copy_stage hstride (byte := false) boundary s c h hc hcc 0x106a93 0x48
      (by intro _; simp [RexWPrefix]) (by decide +kernel) cip cc (by omega)
      csrc cdst csp (by change lead + 8 * ((len - lead) / 8) ≤ len; omega)
      (by rw [cdst]; exact add_lead_aligned _)
      (agrees_clobbers_trans sbframe cf) (by simpa only [cmem] using bcopy)
  obtain ⟨e, hde, he, hce, eip, erc, hfde⟩ := remainder_steps_general d hd hcdcode dip
    (drdx.trans crdx) boundary (dsp ▸ h.inside)
  rw [hn] at erc
  have esp : stackPtr e = stackPtr s := (hfde.read (n := 64) (r := 4) (by decide)).trans dsp
  have esrc := (hfde.read (n := 64) (r := 6) (by decide)).trans dsrc
  have edst := (hfde.read (n := 64) (r := 7) (by decide)).trans ddst
  have erax := (hfde.read (n := 64) (r := 0) (by decide)).trans (drax.trans crax)
  have emem : e.external = d.external := hfde.external (by simp [loopClobbers, Component.Covers])
  have ef : AgreesExcept (clobbers (rdi.read s) len) d e := hfde.mono (by
    intro q hq
    simp only [loopClobbers, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [clobbers])
  obtain ⟨f, hef, hf, hcf, fip, _, _, fsp, frax, _, _, sfframe, fcopy⟩ :=
    copy_stage hstride (byte := true) boundary s e h he hce 0x106a9c 0
      (by simp) (by decide +kernel) eip erc (by omega) esrc edst esp
      (by change lead + 8 * ((len - lead) / 8) + 1 * ((len - lead) % 8) ≤ len; omega)
      (by change _ % 1 = 0; exact Nat.mod_one _) (agrees_clobbers_trans sdframe ef)
      (by simpa only [emem] using dcopy)
  have total : lead + movsBytes false * ((len - lead) / 8) +
      movsBytes true * ((len - lead) % 8) = len := by
    change lead + 8 * ((len - lead) / 8) + 1 * ((len - lead) % 8) = len
    omega
  rw [total] at fcopy
  obtain ⟨t, hft, ht⟩ := return_steps boundary s f hcode h hf hcf fip fsp
    (frax.trans erax) sfframe fcopy
  refine ⟨t, ?_, ht⟩
  have hadv := hsa.trans (hab.trans (hbc.trans (hcd.trans (hde.trans (hef.trans hft)))))
  have heq : 7 + (max lead 1 + (3 + (max ((len - lead) / 8) 1 +
      (2 + (max ((len - lead) % 8) 1 + 1))))) =
      13 + max lead 1 + max ((len - lead) / 8) 1 + max ((len - lead) % 8) 1 := by omega
  rw [heq] at hadv
  exact hadv

theorem memcpy208_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s : RamState) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s) :
    ∃ t, Advances boundary 41 s t ∧ Done s t := by
  have ha : (rdi.read s).toNat % 8 = 0 := h.aligned
  have hm := memcpy_steps hstride (by decide) boundary s hready hcode h
  dsimp only at hm
  rw [ha] at hm
  have heq : 13 + max ((8 - 0) % 8) 1 + max ((208 - (8 - 0) % 8) / 8) 1 +
      max ((208 - (8 - 0) % 8) % 8) 1 = 41 := by decide
  rw [heq] at hm
  exact hm

theorem memcpy200_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s : RamState) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s 200 false) :
    ∃ t, Advances boundary (memcpy200Steps (rdi.read s)) s t ∧ Done s t 200 := by
  rw [memcpy200Steps_eq]
  exact memcpy_steps hstride (by decide) boundary s hready hcode h

end Sha3.Proofs.Memcpy
