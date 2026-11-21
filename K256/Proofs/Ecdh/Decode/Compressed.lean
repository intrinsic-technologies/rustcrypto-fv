import K256.Proofs.Sec1.Affine.Compressed.Execution
import K256.Proofs.Ecdh.Decode.Compressed.Emit
import K256.Proofs.Ecdh.Decode.Repr

namespace K256.Proofs.Ecdh.Decode

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field K256.Proofs.Sec1.Serialize.Coordinates

open K256.Proofs.Sec1 K256.Proofs.Sec1.Affine K256.Proofs.Sec1.Affine.Compressed

attribute [local irreducible] SqrtChain.result SqrtChainExecution.chainWord

private theorem masked_repr (v : Inputs) (h : v.valid = true) : FieldRepr v.masked v.coordinate 1 := by
  have hx : v.x < modulus := of_decide_eq_true h
  simp only [Inputs.masked, Uncompressed.CoordinateWords.masked,
      (show Uncompressed.CoordinateWords.valid v = true from h), ite_true]
  exact Uncompressed.unpack_repr v.a v.b v.c v.d v.coordinate (Nat.mod_eq_of_lt hx).symm (by decide)

private theorem statusByte (r x : Fin modulus) :
    (if r*r = x then (1 : BitVec 8) else 0) = BitVec.ofNat 8 (decide (SqrtChain.modSq r.val = x.val)).toNat := by
  simp only [Fin.ext_iff, Fin.val_mul, SqrtChain.modSq]
  split <;> simp_all

theorem compressedDecoder {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (tag : UInt8) (want : BitVec 8)
    (pre : EntryPre code fr args mem want) (env : Environment fr) (parity : want.toNat = tag.toNat % 2)
    {point : Standards.SECG.ECC.Curve.Point} (ok : Sec1.decompress tag (inputs mem fr.rsi).x = some point) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l1205b0,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All code out.values out.store (Fn1205b0.doneAt fr) ∧
      out.values[0] = ⟨64,fr.rdi⟩ ∧ RamWriteFrame mem out.store [fr.region, ⟨fr.rdi.toNat,89⟩] ∧
      memLoad out.store (fr.rdi + 88) 8 = 1 ∧ AffinePointAt out.store fr.rdi point := by
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
  have run := SqrtChainExecution.execution (fr := child) (x := v.radicand) geometry frame input rd wr repr
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
    selectNormalized cover fr _ _ _ v.valid v.sqrtOK want v.root env body typed roots bit v.root_pos
  obtain ⟨out,e,target,done',rax,outWrites,valid,pointAt⟩ :=
    emitNormalized cover fr selected sm v.masked v.valid v.sqrtOK want v.coordinate _ env body' picked (masked_repr v)
  refine ⟨out,Program.Exec.of_sem (first.exec (path.exec (p.exec e.sem))),target,done',rax,?_,?_⟩
  · have narrow : RegionsWithin [fr.region] [fr.region] := fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩
    have wide := (firstWrites.trans midWrites narrow).trans pickWrites narrow
    apply ((RamWriteFrame.refl _ _).trans wide ?_).trans outWrites
    · exact fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩
    · intro r h
      obtain rfl := List.mem_singleton.mp h
      exact ⟨fr.region,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  · change Sec1.decompress tag v.x = some point at ok
    rw [v.decompress tag want parity] at ok
    split at ok
    next h =>
      cases Option.some.inj ok
      exact ⟨valid.trans (by rw [h]; rfl), _, _, rfl, rfl, pointAt h⟩
    next => contradiction

end K256.Proofs.Ecdh.Decode
