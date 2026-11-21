import K256.Proofs.Common.SignatureRun
import K256.Proofs.Generate.Generator.Affine.State
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

def normalizeMemory (fr : Activation) (m : Ram) : Ram :=
  let m := memStore m (fr.rsp - 8) fr.rbp
  let m := memStore m (fr.rsp - 16) fr.r15
  let m := memStore m (fr.rsp - 24) fr.r14
  let m := memStore m (fr.rsp - 32) fr.r13
  let m := memStore m (fr.rsp - 40) fr.r12
  let m := memStore m (fr.rsp - 48) fr.rbx
  memStore m (fr.rsp - 240) (0x10ed05 : Word)

def normalizeReturn : StackFrame Value Label signature Reg.count :=
  ⟨.l10ed05, #v[], rfl, some ⟨64, 0x10ed05⟩⟩

private theorem pushGuard {m : Ram} {addr pc : Word} {len : Nat}
    (w : Writable Extracted.programImage m addr 8)
    (within : (pc - 0x10ece0).toNat + len ≤ bytes_l10ece0.length) :
    StoreOk Extracted.programImage m addr 8 pc len := by
  have h := ParseSignature.storeOk_of_codeRange w
    (fun v hv => Common.fnCode_subset_programImage v (code_l10ece0 v hv)) within
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show 0x10ece0 + (pc - 0x10ece0) = pc by bv_omega] at h

theorem normalizeEntry {a : Registers} {m : Ram} {fr : Activation}
    (s : State .l10fe50 fr a m) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10ece0, a, m⟩ =
      .call ⟨.l114930, b, normalizeMemory fr m⟩ normalizeReturn ∧
      b[4] = ⟨64, fr.rsp - 240⟩ ∧ b[6] = ⟨64, fr.rsi + 80⟩ ∧
      b[7] = ⟨64, fr.rsp - 144⟩ ∧ b[3] = ⟨64, fr.rdi⟩ ∧ b[14] = ⟨64, fr.rsi⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,15,22,39,50,51] → b[i] = a[i]) := by
  obtain ⟨sp, _, _, _, bx, bp, si, di, _, _, r12, r13, r14, r15, _, _, _, _, _, _, win, _⟩ := s.atoms
  change a[4] = ⟨64, fr.rsp⟩ at sp
  change a[3] = ⟨64, fr.rbx⟩ at bx
  change a[5] = ⟨64, fr.rbp⟩ at bp
  change a[6] = ⟨64, fr.rsi⟩ at si
  change a[7] = ⟨64, fr.rdi⟩ at di
  change a[12] = ⟨64, fr.r12⟩ at r12
  change a[13] = ⟨64, fr.r13⟩ at r13
  change a[14] = ⟨64, fr.r14⟩ at r14
  change a[15] = ⟨64, fr.r15⟩ at r15
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  refine ⟨?regs, ?run, ?post⟩
  case run =>
    cfg_eval
    simp only [sp, bx, bp, si, di, r12, r13, r14, r15, Value.get_mk]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_
             apply pushGuard _ (by decide)
             repeat' apply Writable.memStore
             apply win.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
    · rfl
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact bp.symm | exact r12.symm | exact r13.symm | exact r15.symm

end K256.Proofs.Generate.Generator.Affine
