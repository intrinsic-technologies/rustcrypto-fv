import K256.Proofs.Sec1.Affine.Compressed.Contract
import K256.Proofs.Sec1.SqrtChainExecution.Stages
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

def sqrtActivation (fr : Activation) (regs : Values Value Reg.count) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := workSP fr - 8, ret := 0x120d03, low := fr.rsp - 1048,
    rcx := regs[1].get 64, rdx := regs[2].get 64, rbx := regs[3].get 64, rbp := regs[5].get 64,
    rsi := workSP fr + 144, rdi := workSP fr + 304, r8 := regs[8].get 64, r9 := regs[9].get 64,
    r12 := regs[12].get 64, r13 := regs[13].get 64, r14 := regs[14].get 64, r15 := regs[15].get 64}

theorem stackOffset {fr : Activation} (room : 1048 ≤ fr.rsp.toNat) (off : Nat) (bound : off ≤ 1048) :
    (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
  have hn : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le, hn]
  rw [BitVec.le_def, hn]
  omega

theorem sqrtEntry {code : CodeMap} {fr : Activation} {args next : Values Value Reg.count}
    {mem m : Ram} {v : Inputs} {want : BitVec 8} (cover : ∀ e ∈ fnCode, e ∈ code)
    (env : Environment fr)
    (entry : CubeReady code fr args mem v want)
    (cube : CubePost args next mem m (workSP fr) v.masked v.valid) :
    let child := sqrtActivation fr next m
    Atom.All code next m (Fn115950.frameAt .l115950 child) ∧ Readable m child.rsi 40 ∧
      Writable code m child.rdi 41 ∧ SqrtChainExecution.Geometry code child := by
  have a := entry.atoms
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at a
  obtain ⟨_, df, mx, ft, fc, _, _, _, _, _, _, _, _, _, _, stack, room, align, _⟩ := a
  change fr.low.toNat + 1048 ≤ fr.rsp.toNat at room
  have writable := stack.of_frame cube.frame
  have addr (n : Nat) (h : n ≤ 1048) := stackOffset (fr := fr) (by omega) n h
  have spEq : workSP fr - 8 = fr.rsp - 496 := by unfold workSP; bv_omega
  have srcEq : workSP fr + 144 = fr.rsp - 344 := by unfold workSP; bv_omega
  have dstEq : workSP fr + 304 = fr.rsp - 184 := by unfold workSP; bv_omega
  have lower : workSP fr - 8 - 552 = fr.rsp - 1048 := by unfold workSP; bv_omega
  have stackN : (fr.rsp - 1048).toNat = fr.rsp.toNat - 1048 := addr 1048 (by decide)
  have spN : (workSP fr - 8).toNat = fr.rsp.toNat - 496 := by rw [spEq]; exact addr 496 (by decide)
  have srcN : (workSP fr + 144).toNat = fr.rsp.toNat - 344 := by rw [srcEq]; exact addr 344 (by decide)
  have dstN : (workSP fr + 304).toNat = fr.rsp.toNat - 184 := by rw [dstEq]; exact addr 184 (by decide)
  have subset (a : Word) (len : Nat) (lo : (fr.rsp-1048).toNat ≤ a.toNat)
      (hi : a.toNat + len ≤ fr.rsp.toNat) : Writable code m a len :=
    writable.sub lo (by change _ ≤ (fr.rsp - 1048).toNat + 1048; omega)
  have text := env.text
  simp only [sqrtActivation, Fn115950.frameAt, Fn115950.frameAtG0, Atom.All, Atom.Holds]
  refine ⟨⟨cube.rsp, (cube.kept 22 (by decide)).trans df, cube.gprs 1 (by decide),
    cube.gprs 2 (by decide), cube.gprs 3 (by decide), cube.gprs 5 (by decide), cube.rsi, cube.rdi,
    cube.gprs 8 (by decide), cube.gprs 9 (by decide), cube.gprs 12 (by decide),
    cube.gprs 13 (by decide), cube.gprs 14 (by decide), cube.gprs 15 (by decide),
    (cube.kept 39 (by decide)).trans mx, (cube.kept 50 (by decide)).trans ft, (cube.kept 51 (by decide)).trans fc,
    (subset _ 8 (by omega) (by omega)).readable, cube.ret, by decide, ?_, by omega, ?_, trivial⟩,
    ?_⟩
  · rw [lower]
    exact subset _ 552 (by omega) (by omega)
  · change fr.rsp.toNat % 16 = 8 at align
    omega
  · refine ⟨(subset (workSP fr + 144) 40 (by omega) (by omega)).readable,
      subset (workSP fr + 304) 41 (by omega) (by omega),cover,?_,?_,?_,?_,?_⟩
    all_goals dsimp only
    all_goals omega

end K256.Proofs.Sec1.Affine.Compressed
