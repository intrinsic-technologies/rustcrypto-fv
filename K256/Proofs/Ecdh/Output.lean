import K256.Proofs.Ecdh.Output.Serialize
import K256.Proofs.Ecdh.Output.Return
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Ecdh.Wrapper Standards.SECG.ECC

private def serializeArgs (a : Vector Value Reg.count) (sp : BitVec 64) :=
  ((a.set 4 ⟨64, sp - 8⟩).set 6 ⟨64, sp + 4184⟩).set 7 ⟨64, sp + 344⟩

private def continuation : StackFrame Value Label signature Reg.count :=
  ⟨.l101b1d, #v[], rfl, some ⟨64, 0x101b1d⟩⟩

private theorem serializeCall {a : Vector Value Reg.count} {sp : BitVec 64} {m : Ram} {code : CodeMap}
    (rsp : a[4].get 64 = sp) (r14 : a[14].get 64 = sp + 4184)
    (push : StoreOk code m (sp - 8) 8 0x101b18 5) :
    program.runBlock (dialect code) ⟨.l101b0d, a, m⟩ = .call
      ⟨.l120350, serializeArgs a sp, memStore m (sp - 8) (0x101b1d : BitVec 64)⟩ continuation := by
  cfg_eval
  simp only [rsp, r14, push, ↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun he => Vector.ext fun i hi => he ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [serializeArgs, Vector.getElem_set] <;> rfl

theorem execution {s : RamState} {secret peer : ByteArray} {p : Curve.Point}
    {m : Ram} {a : Vector Value Reg.count}
    (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (stack : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (saved : Saved s m) (rsp : a[4].get 64 = localSp s)
    (r14 : a[14].get 64 = localSp s + 4184)
    (rbx : a[3] = ⟨64, s.regValue .rdi⟩) (df : a[22] = ⟨1, 0⟩)
    (x : Affine.XAt m (localSp s + 4184) p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l101b0d, a, m⟩, []⟩ out ∧
      Common.Returned s (regions s) out ∧ (outputRegion ecdhDiffieHellman s).HasBytes out.store (xBytes p) := by
  let sp := localSp s
  let addr := sp - 8
  let m' := memStore m addr (0x101b1d : BitVec 64)
  have offset : addr = s.regValue .rsp - 6160 := by dsimp [addr, sp, localSp]; bv_omega
  have push : StoreOk Extracted.programImage m addr 8 0x101b18 5 := by
    rw [offset]
    exact ParseSignature.storeOk_of_codeRange (off := 11)
      ((Common.stackWritable (off := 6160) call (by decide) (by decide) (by decide)).of_frame stack)
      (fun v hv => Common.fnCode_subset_programImage v (code_l101b0d v hv)) (by decide)
  have frame : RamWriteFrame s.external m' [Stack.region s ecdhDiffieHellman.minStackBytes] := by
    apply stack.memStore
    exact ⟨_, List.mem_cons_self, offset ▸ Common.stackRange (off := 6160) call.stackAvailable (by decide) (by decide)⟩
  have wrote : RamWriteFrame m m' [⟨addr.toNat, 8⟩] :=
    (RamWriteFrame.refl m _).memStore _ ⟨_, List.mem_cons_self, by exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_trans push.low (by decide)⟩⟩
  have saved' := saved.of_frame call wrote (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have eq := Common.stackOffset (off := 6160) call.stackAvailable (by decide)
    have room : 10088 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
    change addr.toNat + 8 ≤ _
    rw [offset]
    change (s.regValue .rsp - 6160).toNat = (s.regValue .rsp).toNat - 6160 at eq
    omega)
  obtain ⟨v, w, words, repr, eq⟩ := x
  have x' : Affine.XAt m' (localSp s + 4184) p :=
    ⟨v, w, words.write_apart _ _ (by apply RangeApart.of_diff; dsimp [addr, sp]; constructor <;> bv_omega), repr, eq⟩
  obtain ⟨child, run, tag, retSp, bx, direction, writes, slots, bytes⟩ :=
    serialize (a := serializeArgs a sp) call frame saved' (by simp [serializeArgs, sp])
      (by simp [serializeArgs, sp]) (by simp [serializeArgs, sp])
      (by simpa [serializeArgs] using rbx) (by simpa [serializeArgs] using df)
      (memLoad_memStore_same _ _ _ (by decide) (by decide)) x'
  obtain ⟨out, tail, post⟩ := copyAndReturn call writes slots retSp bx direction bytes
  refine ⟨out, ParseSignature.exec_call (serializeCall rsp r14 push) run ?_ tail, post⟩
  rw [tag]
  rfl

end K256.Proofs.Ecdh.Output
