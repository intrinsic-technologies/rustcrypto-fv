import Base16ct.Proofs.EncodeStr.Upper.Epilogue.Return
import Base16ct.Proofs.EncodeStr.Upper.Machine
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Effect
namespace Base16ct.Proofs.EncodeStr.Upper.Epilogue
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem success_run [Bindings] {initial s : RamState} (value : BitVec 64)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = 0x10047d) (hsp : stackPtr s = stackPtr initial - 24)
    (hm : MemReadable s (stackPtr initial - 16) 8)
    (hvalue : (Operand.mem (stackPtr initial - 16) : Operand 64).read s = value)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rbx) 8)
    (hcode : ∀ i < 8, ¬ InProgram (s.regValue .rbx + BitVec.ofNat 64 i))
    (hsepB : RangeApart (s.regValue .rbx) 8 (stackPtr initial - 8) 8)
    (hsepR : RangeApart (s.regValue .rbx) 8 (stackPtr initial) 8)
    (hmb : MemReadable s (stackPtr initial - 8) 8)
    (hbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx)
    (hmret : MemReadable s (stackPtr initial) 8)
    (hv : (Operand.mem (stackPtr initial) : Operand 64).read s = (returnBoundary initial).rip)
    (hl : (returnBoundary initial).rip.toNat < 2^32)
    (ho : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, Returns (returnBoundary initial) 6 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 0, .reg 3, .reg 4, .flags, .rip, .mem (s.regValue .rbx) 8] s t ∧
      t.regValue .rax = 0 ∧ t.regValue .rbx = initial.regValue .rbx ∧
      (Operand.mem (s.regValue .rbx) : Operand 64).read t = value := by
  have haddr : stackPtr s + 8 = stackPtr initial - 16 := by
    rw [hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hc1 : CodeIn (codeRange 0x10047d [0x48, 0x8b, 0x44, 0x24, 8]) s := by
    have hbytes : Extracted.textBytes.toListFrom 0x47d 5 = [0x48, 0x8b, 0x44, 0x24, 8] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x47d = 0x10047d by decide +kernel]
      using program_text_slice hc 0x47d 5 (by decide +kernel)
  obtain ⟨u, run1, ready1, e1⟩ :=
    (mov_r64_m64_effect_step 0x10047d 0x48 (by constructor <;> decide +kernel) 0
      (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid]) rfl rfl).advances hr hc1
      ⟨hip, by change MemReadable s (stackPtr s + 8) 8; rw [haddr]; exact hm⟩
      (text_address_ne_return ho 0x482 (by decide +kernel))
  have a1 : AgreesExcept [.reg 0, .rip] s u := e1.agrees
  have mem1 : u.external = s.external := a1.external (by simp [Component.Covers])
  have bx1 : u.regValue .rbx = s.regValue .rbx := a1.read (n := 64) (r := 3) (by simp)
  have val1 : u.regValue .rax = value := by
    have hv1 := e1.writes
    change u.regValue .rax = (Operand.mem (stackPtr s + 8) : Operand 64).read s at hv1
    rw [haddr, hvalue] at hv1
    exact hv1
  have hc2 : CodeIn (codeRange 0x100482 [0x48, 0x89, 0x03]) u := by
    have hbytes : Extracted.textBytes.toListFrom 0x482 3 = [0x48, 0x89, 0x03] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x482 = 0x100482 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem1) 0x482 3 (by decide +kernel)
  have pre2 : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre 0x100482 3 (fun x => x.regValue .rbx) 8 u := by
    refine ⟨e1.rip, ?_, ?_⟩
    · rw [bx1]; exact hw.of_external_eq mem1
    · intro i hi j hj he
      apply hcode i hi
      rw [bx1] at he
      rw [he]
      have hsize : 0x482 + 3 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x482 + j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc,
        show Extracted.textAddress + BitVec.ofNat 64 0x482 = 0x100482 by decide +kernel] using hx
  have addr2 : storeAddrAt 0x100482 (.base 3 .none) 3 u = u.regValue .rbx := by
    change u.regValue .rbx + 0 = u.regValue .rbx
    exact BitVec.add_zero _
  have pre2a : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre 0x100482 3
      (storeAddrAt 0x100482 (.base 3 .none) 3) 8 u := by
    refine ⟨pre2.rip, ?_, ?_⟩
    · rw [addr2]; exact pre2.write
    · rw [addr2]; exact pre2.code
  obtain ⟨v, run2, ready2, e2⟩ :=
    (Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x100482 0x48
      (by constructor <;> decide +kernel) 0 (.base 3 .none)
      (by decide +kernel) rfl rfl).advances ready1 hc2 pre2a
      (text_address_ne_return ho 0x485 (by decide +kernel))
  have a2 : AgreesExcept [.mem (s.regValue .rbx) 8, .rip] u v := by
    have ha : AgreesExcept [.mem (storeAddrAt 0x100482 (.base 3 .none) 3 u) 8, .rip] u v := by
      simpa only [movM64R64Effect_components,
        show 3 + (AddrMode.base 3 .none).tail.length = 3 from rfl] using e2.agrees
    rw [addr2, bx1] at ha
    exact ha
  have hcV : CodeIn Extracted.programImage v := CodeIn.of_agreesExcept a2 (by
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, he⟩ := hcov
      exact hcode i hi (he ▸ ⟨x.2, hx⟩)
    · exact hcov) (hc.of_external_eq mem1)
  have hc3 : CodeIn (codeRange 0x100485 [0x31, 0xc0]) v := by
    have hbytes : Extracted.textBytes.toListFrom 0x485 2 = [0x31, 0xc0] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x485 = 0x100485 by decide +kernel]
      using program_text_slice hcV 0x485 2 (by decide +kernel)
  obtain ⟨w, run3, ready3, e3⟩ :=
    (xor_r32_r32_effect_step 0x100485 0xc0 rfl).advances ready2 hc3 e2.rip
      (text_address_ne_return ho 0x487 (by decide +kernel))
  have a3 : AgreesExcept [.reg 0, .flags, .rip] v w := e3.agrees
  have mem3 : w.external = v.external := a3.external (by simp [Component.Covers])
  have aall := (a1.trans a2).trans a3
  have rsp3 : stackPtr w = stackPtr initial - 24 :=
    (aall.read (n := 64) (r := 4) (by simp)).trans hsp
  have slots (addr : BitVec 64) (ha : RangeApart (s.regValue .rbx) 8 addr 8) :
      (Operand.mem addr : Operand 64).read w = (Operand.mem addr : Operand 64).read s := by
    apply memLoad_congr
    intro i hi
    have he := aall.byte (x := addr + BitVec.ofNat 64 i) (by
      intro c hc hcov
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl | rfl)
      all_goals try exact hcov
      obtain ⟨j, hj, he⟩ := hcov
      exact ha j hj i hi he.symm)
    change (w.external[addr + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[addr + BitVec.ofNat 64 i]?).getD 0
    rw [he]
  have hc4 : CodeIn (codeRange 0x100487 [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3]) w := by
    have hbytes : Extracted.textBytes.toListFrom 0x487 6 = [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x487 = 0x100487 by decide +kernel]
      using program_text_slice (hcV.of_external_eq mem3) 0x487 6 (by decide +kernel)
  obtain ⟨t, run4, ready4, a4, bx4⟩ := restore_return 0x100487 ready3 hc4 e3.rip rsp3
    ⟨hmb.low, fun i hi => aall.grow _ (hmb.mem i hi)⟩
    ((slots _ hsepB).trans hbx)
    ⟨hmret.low, fun i hi => aall.grow _ (hmret.mem i hi)⟩
    ((slots _ hsepR).trans hv) hl
  refine ⟨t, ((run1.trans run2).trans run3).returns run4, ready4,
    (aall.trans a4).mono (by simp), ?_, bx4, ?_⟩
  · have hz : w.regValue .rax = 0 := by
      have he := e3.writes
      change w.regValue .rax =
        ((v.regValue .rax).setWidth 32 ^^^ (v.regValue .rax).setWidth 32).setWidth 64 at he
      rw [BitVec.xor_self] at he
      exact he
    exact (a4.read (n := 64) (r := 0) (by simp)).trans hz
  · have mt := a4.external (by simp [Component.Covers])
    change memLoad t.external _ 64 = _
    rw [mt, mem3]
    have he := e2.writes
    change memLoad v.external (u.regValue .rbx + 0#64) 64 = u.regValue .rax at he
    rw [BitVec.add_zero, bx1, val1] at he
    exact he

end Base16ct.Proofs.EncodeStr.Upper.Epilogue
