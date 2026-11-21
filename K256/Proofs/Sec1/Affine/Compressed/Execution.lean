import K256.Proofs.Sec1.Affine.Compressed.Start.Call
import K256.Proofs.Sec1.Affine.Compressed.Cube.Call
import K256.Proofs.Sec1.SqrtChainExecution.Call
import K256.Proofs.Sec1.Affine.Compressed.Result
import K256.Proofs.Sec1.Affine.Compressed.SqrtResume
import K256.Proofs.Sec1.Affine.Compressed.Emit.Call
import K256.Proofs.Sec1.Affine.Compressed.Tail.Call

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

attribute [local irreducible] SqrtChain.result SqrtChainExecution.chainWord

theorem Inputs.resultAt {v : Inputs} {m : Ram} {dst : Word} {tag : UInt8} {want : BitVec 8}
    (parity : want.toNat = tag.toNat % 2)
    (valid : memLoad m (dst + 88) 8 = BitVec.ofNat 8 (v.valid && v.sqrtOK).toNat)
    (point : (v.valid && v.sqrtOK) = true → Parser.AffineAt m dst v.coordinate (chosenY v.root want)) :
    Affine.ResultAt m dst (Sec1.decompress tag v.x) := by
  rw [v.decompress tag want parity]
  cases h : v.valid && v.sqrtOK with
  | false => exact (valid.trans (by rw [h]; rfl))
  | true => exact ⟨valid.trans (by rw [h]; rfl), v.coordinate, chosenY v.root want, rfl, point h⟩

private theorem statusByte (r x : Fin modulus) :
    (if r*r = x then (1 : BitVec 8) else 0) = BitVec.ofNat 8 (decide (SqrtChain.modSq r.val = x.val)).toNat := by
  simp only [Fin.ext_iff, Fin.val_mul, SqrtChain.modSq]
  split <;> simp_all

theorem decoderOfCalls {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    (sqrt : ∀ {fr : Activation} {args : Values Value Reg.count} {a : Limbs} {x : Fin modulus},
      SqrtChainExecution.Geometry code fr → Atom.All code args fr.original (Fn115950.frameAt .l115950 fr) →
      WordsAt fr.original fr.rsi 64 a → Readable fr.original fr.rsi 40 → Writable code fr.original fr.rdi 41 →
      FieldRepr a x 8 →
      ∃ o, program.Exec (dialect code) ⟨⟨.l115950,args,fr.original⟩,[]⟩ o ∧
        FieldRepr (SqrtChainExecution.words a 27) (SqrtChainExecution.candidate x) 8 ∧
        SqrtChainExecution.Return code fr (SqrtChainExecution.words a 27)
          (if SqrtChainExecution.candidate x * SqrtChainExecution.candidate x = x then 1 else 0) o) :
    DecoderCall code := by
  intro fr args mem tag want pre env parity
  let v := inputs mem fr.rsi
  obtain ⟨atCube,started,first,ready,firstWrites⟩ := startCall cover fr args mem want pre
  change CubeReady code fr atCube started v want at ready
  have cubeWin : Writable code started (workSP fr - 8) 192 := by
    have stack := pre.stack.of_frame firstWrites
    apply stack.of_offsets (x := fr.rsp) (c := 0-496) (d := 0-1048)
    · unfold workSP; bv_omega
    · bv_omega
    · decide
  have sp : atCube[4].get 64 = workSP fr := congrArg (Value.get 64) ready.atoms.1
  obtain ⟨regs,m,call,post⟩ := cubeCall cover atCube started _ v.a v.b v.c v.d v.valid sp ready.canonical
    ready.r12 ready.r13 ready.r14 ready.rbx ready.r15 ready.rbp cubeWin
  change CubePost atCube regs started m (workSP fr) v.masked v.valid at post
  let child := sqrtActivation fr regs m
  obtain ⟨frame,rd,wr,geometry⟩ := sqrtEntry cover env ready post
  obtain ⟨us,input,repr⟩ := post.cube
  have run := sqrt (fr := child) (x := v.radicand) geometry frame input rd wr repr
  obtain ⟨o, exec, yr,ret,doneAt,_,ys,flag,writes⟩ := run
  have path := Serialize.Coordinates.reaches_call call exec ret
  obtain ⟨body,typed,midWrites⟩ := sqrtResume ready post o doneAt writes
  have root : SqrtChainExecution.candidate v.radicand = v.root := by
    apply Fin.ext
    exact (SqrtChain.result_sqrt v.radicand).symm
  change memLoad o.store (workSP fr + 304 + 40) 8 = _ at flag
  rw [root] at yr flag
  have status : (if v.root * v.root = v.radicand then (1 : BitVec 8) else 0) =
      BitVec.ofNat 8 v.sqrtOK.toNat := statusByte v.root v.radicand
  have roots : RootAt o.store (workSP fr) v.root v.sqrtOK := by
    refine ⟨?_, fun _ => ⟨_,ys,yr⟩⟩
    rw [show workSP fr + 344 = workSP fr + 304 + 40 by bv_omega]
    exact flag.trans status
  have bit : want = 0 ∨ want = 1 := by
    have hn : want.toNat < 2 := parity ▸ Nat.mod_lt _ (by decide)
    rcases (show want.toNat = 0 ∨ want.toNat = 1 by omega) with z | one
    · exact Or.inl (BitVec.eq_of_toNat_eq z)
    · exact Or.inr (BitVec.eq_of_toNat_eq one)
  obtain ⟨selected,sm,p,body',picked,pickWrites⟩ :=
    selectCall cover fr _ _ _ v.valid v.sqrtOK want v.root env body typed roots bit v.root_pos
  obtain ⟨out,e,target,done',rax,outWrites,valid,point⟩ :=
    emitCall cover fr selected sm v.masked v.valid v.sqrtOK want v.coordinate _ env body' picked v.masked_repr
  refine ⟨out,Program.Exec.of_sem (first.exec (path.exec (p.exec e.sem))),target,done',rax,?_,?_⟩
  · have narrow : RegionsWithin [fr.region] [fr.region] := fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩
    have wide := (firstWrites.trans midWrites narrow).trans pickWrites narrow
    apply ((RamWriteFrame.refl _ _).trans wide ?_).trans outWrites
    · exact fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩
    · intro r h
      obtain rfl := List.mem_singleton.mp h
      exact ⟨fr.region,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  · exact Inputs.resultAt (v := v) (m := out.store) (dst := fr.rdi)
        (tag := tag) (want := want) parity valid point

theorem decoderCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) : DecoderCall code := by
  apply decoderOfCalls cover
  intro fr args a x geometry frame words rd wr repr
  exact SqrtChainExecution.execution geometry frame words rd wr repr

end K256.Proofs.Sec1.Affine.Compressed
