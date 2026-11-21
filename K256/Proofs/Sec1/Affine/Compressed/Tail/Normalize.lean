import K256.Proofs.Sec1.Affine.Compressed.Tail.Stages
import K256.Proofs.Sec1.Affine.Compressed.SqrtEntry
import K256.Proofs.Sec1.Serialize.Normalize.Execution

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

theorem normalizeRootCall {code : CodeMap} {fr : Activation} {args next : Values Value Reg.count}
    {mem m : Ram} {xs a : Limbs} {xOK ok : Bool} {want : BitVec 8} {ret : Word} {src dst : Nat}
    (env : Environment fr) (body : BodyAt code fr args mem xs xOK want)
    (input : NormalizeAt code args next mem m (workSP fr) ret src dst a ok)
    (offsets : (src = 184 ∧ dst = 224) ∨ (src = 264 ∧ dst = 392)) (low : ret.toNat < 2^32) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l114930,next,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,workSP fr⟩ ∧
      (∀ i : Fin 53, i.val ∈ [22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame mem out.store (selectWrites (workSP fr)) ∧
      WordsAt out.store (workSP fr + BitVec.ofNat 64 dst) 64 (Serialize.Normalize.normalize a) ∧
      memLoad out.store (workSP fr+32) 8 = BitVec.ofNat 8 ok.toNat := by
  let sp := workSP fr
  let c : Serialize.Normalize.Ctx := ⟨sp + BitVec.ofNat 64 src, sp + BitVec.ofNat 64 dst,
    next[39], next[50], next[51]⟩
  let child : Activation := { fr with
    original := m, rsp := sp - 8, low := sp - 121, ret := ret
    rbx := next[3].get 64, rbp := next[5].get 64, r12 := next[12].get 64
    r13 := next[13].get 64, r14 := next[14].get 64, r15 := next[15].get 64
    rsi := c.src, rdi := c.dst }
  let initialDst : Limbs := Vector.ofFn fun i => memLoad m (wordAddr c.dst 64 i.val) 64
  have hdw : WordsAt m c.dst 64 initialDst := by
    intro i hi
    simp only [initialDst, Vector.getElem_ofFn]
  have atoms := body.atoms
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, df, _, _, _, _, _, _, _, _, _, _, read, _, _, stack, room, align, _⟩ := atoms
  have stackLow := read.low
  have offset (k : Nat) (hk : k ≤ 1048) := stackOffset (fr := fr) (by omega) k hk
  have spN : sp.toNat = fr.rsp.toNat - 488 := offset 488 (by decide)
  have slotN : (sp - 8).toNat = fr.rsp.toNat - 496 := by
    rw [show sp - 8 = fr.rsp - 496 by dsimp only [sp, workSP]; bv_omega]
    exact offset 496 (by decide)
  have scratchN : (sp - 121).toNat = fr.rsp.toNat - 609 := by
    rw [show sp - 121 = fr.rsp - 609 by dsimp only [sp, workSP]; bv_omega]
    exact offset 609 (by decide)
  have addN (k : Nat) (hk : k ≤ 488) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have srcN : c.src.toNat = sp.toNat + src := addN src (by omega)
  have dstN : c.dst.toNat = sp.toNat + dst := addN dst (by omega)
  have win := stack.of_frame input.frame
  have startN : (fr.rsp - 1048).toNat = fr.rsp.toNat - 1048 := offset 1048 (by decide)
  have slice (address : Word) (size : Nat) (lo : fr.rsp.toNat - 1048 ≤ address.toNat)
      (hi : address.toNat + size ≤ fr.rsp.toNat) : Writable code m address size :=
    win.sub (by omega) (by omega)
  have window : Writable code m ((sp - 8) - 113) 113 := by
    rw [show sp - 8 - 113 = sp - 121 by bv_omega]
    exact slice _ _ (by omega) (by omega)
  have text := env.text
  have entry : Atom.All code next m (Serialize.Normalize.frameAt .l114930 child ++
      Serialize.Normalize.core.atoms .entry c child ⟨c.dst, a, initialDst⟩) := by
    rw [Serialize.Normalize.frameAt_114930, Atom.all_append]
    constructor
    · exact ⟨input.rsp, (input.kept 22 (by decide)).trans df, input.wide 3 (by decide),
        input.wide 5 (by decide), input.rsi, input.rdi, input.wide 12 (by decide),
        input.wide 13 (by decide), input.wide 14 (by decide), input.wide 15 (by decide),
        (slice (sp - 8) 8 (by omega) (by omega)).readable, input.slot, low, window,
        by change (sp - 121).toNat + 113 ≤ (sp - 8).toNat; omega,
        by change (sp - 8).toNat % 16 = 8; omega, trivial⟩
    · refine ⟨input.rsi, input.rdi, rfl, rfl, rfl, rfl, input.words,
        (slice c.src 40 (by omega) (by omega)).readable, hdw, slice c.dst 40 (by omega) (by omega),
        ?_, Or.inr ?_, Or.inr ?_, Or.inr ?_, ?_, ?_, trivial⟩
      all_goals try dsimp only [Atom.Holds, child]
      all_goals omega
  obtain ⟨out, run, tag, post, writes⟩ := Serialize.Normalize.normalizeExecution c child a
    initialDst next m entry (RamWriteFrame.refl _ _)
  rw [Serialize.Normalize.doneAt_eq] at post
  obtain ⟨rsp, df', _, _, _, _, _, _, mx, ft, fc, _, _, words, _⟩ := post
  have kept (i : Fin 53) (hi : i.val ∈ [22,39,50,51]) : out.values[i] = args[i] := by
    apply Eq.trans _ (input.kept i hi)
    rcases i with ⟨i, bound⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact df'.trans ((input.kept 22 (by decide)).trans df).symm
    · exact mx
    · exact ft
    · exact fc
  change RamWriteFrame m out.store
    [⟨(sp - 121).toNat, (sp - 8).toNat - (sp - 121).toNat⟩, ⟨c.dst.toNat, 40⟩] at writes
  rw [show (sp - 8).toNat - (sp - 121).toNat = 113 by omega] at writes
  have frame := input.frame.trans writes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (by decide : 113 ≤ 121) _⟩
    · have n184 : (sp+184).toNat = sp.toNat + 184 := addN 184 (by decide)
      refine ⟨⟨(sp+184).toNat, 248⟩, by simp [selectWrites, sp], ?_, ?_⟩
      all_goals dsimp only <;> omega)
  have flag : memLoad out.store (sp+32) 8 = memLoad m (sp+32) 8 := by
    apply writes.memLoad_eq
    have n32 : (sp+32).toNat = sp.toNat + 32 := addN 32 (by decide)
    refine ⟨by change _ + 1 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega
  refine ⟨out, run, tag, ?_, kept, frame, words, flag.trans input.flag⟩
  change out.values[4] = ⟨64, (sp - 8) + 8⟩ at rsp
  simpa only [BitVec.sub_add_cancel] using rsp

end K256.Proofs.Sec1.Affine.Compressed
