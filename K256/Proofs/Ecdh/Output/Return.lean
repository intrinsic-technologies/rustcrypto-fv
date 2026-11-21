import K256.Proofs.Ecdh.Output.Memory
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Ecdh.LIR.EcdhDiffieHellman

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Ecdh.Wrapper

private theorem restored {s : RamState} {m : Ram} (saved : Saved s m)
    (off : Nat) (reg : Syntax.Reg) (memSlot : (off, reg) ∈ savedSlots)
    (hi : off ≤ 6152) :
    memLoad m (localSp s + BitVec.ofNat 64 (6152 - off)) 64 = s.regValue reg := by
  have addr := localAddr s (i := 6152 - off) (by omega)
  rw [Nat.sub_sub_self hi] at addr
  exact (congrArg (fun p => memLoad m p 64) addr).trans (saved.registers (off, reg) memSlot)

set_option maxHeartbeats 1400000 in
theorem copyAndReturn {s : RamState} {secret peer bytes : ByteArray}
    {m : Ram} {a : Vector Value Reg.count}
    (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (stack : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (saved : Saved s m) (rsp : a[4] = ⟨64, localSp s⟩)
    (rbx : a[3] = ⟨64, s.regValue .rdi⟩) (df : a[22] = ⟨1, 0⟩)
    (serialized : (⟨(localSp s + 344).toNat, 32⟩ : MemoryRegion).HasBytes m bytes) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l101b1d, a, m⟩, []⟩ out ∧
      Common.Returned s (regions s) out ∧ (outputRegion ecdhDiffieHellman s).HasBytes out.store bytes := by
  let sp := localSp s
  let dst := s.regValue .rdi
  let output := outputRegion ecdhDiffieHellman s
  let area := Stack.region s ecdhDiffieHellman.minStackBytes
  let scratch : MemoryRegion := ⟨(sp + 344).toNat, 32⟩
  let code := Extracted.programImage
  have room : 10088 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have apart : dst.toNat + 32 ≤ (s.regValue .rsp).toNat - 10088 ∨
      (s.regValue .rsp).toNat + 8 ≤ dst.toNat := outputStackApart call
  have initialDst : Writable code m dst 32 :=
    (Common.outputWritable call rfl (by decide)).of_frame stack
  have dstLow := initialDst.readable.low
  have stackRange {i n : Nat} (hi : i ≤ 6152) (hn : n ≤ 6152 - i + 8) :
      InRegion area (sp + BitVec.ofNat 64 i) n := by
    rw [localAddr s hi]
    exact Common.stackRange call.stackAvailable (by change 6152 - i ≤ 10088; omega) hn
  have stackWritable {i n : Nat} (hi : i ≤ 6152) (hn : n ≤ 6152 - i + 8) (pos : 0 < n) :
      Writable code m (sp + BitVec.ofNat 64 i) n := by
    rw [localAddr s hi]
    exact (Common.stackWritable call (by change 6152 - i ≤ 10088; omega) hn pos).of_frame stack
  have extend {t : Ram} (frame : RamWriteFrame m t [output]) (i : Nat)
      (hi : i + 8 ≤ 32) (x : BitVec 64) :
      RamWriteFrame m (memStore t (dst + BitVec.ofNat 64 i) x) [output] := by
    apply frame.memStore
    refine ⟨output, List.mem_cons_self, ?_⟩
    unfold InRegion
    rw [outputOffset dstLow (by omega)]
    change dst.toNat ≤ dst.toNat + i ∧ dst.toNat + i + 8 ≤ dst.toNat + 32 ∧
      dst.toNat + i + 8 ≤ 2^64
    omega
  have kept {t : Ram} (frame : RamWriteFrame m t [output]) (i : Nat) (hi : i ≤ 6152) :
      memLoad t (sp + BitVec.ofNat 64 i) 64 = memLoad m (sp + BitVec.ofNat 64 i) 64 := by
    have within := stackRange (n := 8) hi (by omega)
    apply frame.memLoad_eq
    refine ⟨within.2.2, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    have start : (s.regValue .rsp).toNat - 10088 ≤ (sp + BitVec.ofNat 64 i).toNat := within.1
    have stop : (sp + BitVec.ofNat 64 i).toNat + 8 ≤ (s.regValue .rsp).toNat + 8 := by
      have h := within.2.1
      change _ ≤ (s.regValue .rsp).toNat - 10088 +
        ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10088)) at h
      omega
    change (sp + BitVec.ofNat 64 i).toNat + 8 ≤ dst.toNat ∨
      dst.toNat + 32 ≤ (sp + BitVec.ofNat 64 i).toNat
    omega
  let m1 := memStore m (dst + 24) (memLoad m (sp + 368) 64)
  let m2 := memStore m1 (dst + 16) (memLoad m (sp + 360) 64)
  let m3 := memStore m2 (dst + 8) (memLoad m (sp + 352) 64)
  let copied := copyMemory m sp dst
  let cleared := clearMemory copied sp 32
  have w0 : RamWriteFrame m m [output] := .refl _ _
  have w1 : RamWriteFrame m m1 [output] := extend w0 24 (by decide) _
  have w2 : RamWriteFrame m m2 [output] := extend w1 16 (by decide) _
  have w3 : RamWriteFrame m m3 [output] := extend w2 8 (by decide) _
  have w4 : RamWriteFrame m copied [output] := extend w3 0 (by decide) _
  have scratchAt (i : Nat) (hi : i ≤ 32) :
      (sp + BitVec.ofNat 64 (344 + i)).toNat = scratch.start + i := by
    have low : (sp + BitVec.ofNat 64 344).toNat + 32 ≤ 2^32 :=
      (stackWritable (i := 344) (n := 32) (by decide) (by decide) (by decide)).readable.low
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, outputOffset low hi]
    rfl
  have cw (i : Nat) (hi : i ≤ 32) : RamWriteFrame copied (clearMemory copied sp i) [scratch] := by
    induction i with
    | zero => exact .refl _ _
    | succ i ih =>
      apply (ih (by omega)).memStore
      refine ⟨scratch, List.mem_cons_self, ?_⟩
      unfold InRegion
      rw [scratchAt i (by omega)]
      have h := (stackRange (i := 344) (n := 32) (by decide) (by decide)).2.2
      change scratch.start + 32 ≤ 2^64 at h
      change scratch.start ≤ scratch.start + i ∧
        scratch.start + i + 1 ≤ scratch.start + 32 ∧ scratch.start + i + 1 ≤ 2^64
      omega
  have totalFrame : RamWriteFrame s.external cleared (regions s).toList := by
    have base : RamWriteFrame s.external m (regions s).toList :=
      ⟨fun x hx => stack.outside x
        ⟨hx.1, fun r hr => hx.2 r (List.mem_cons_of_mem _ hr)⟩, stack.present⟩
    have copiedFrame := base.trans w4 (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨output, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
    apply copiedFrame.trans (cw 32 (by decide))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have h := stackRange (i := 344) (n := 32) (by decide) (by decide)
    exact ⟨area, List.mem_cons_of_mem _ List.mem_cons_self, h.1, h.2.1⟩
  have savedCopied : Saved s copied := by
    constructor
    · intro kv h
      have hi : kv.1 ≤ 48 := by
        simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have eq : sp + BitVec.ofNat 64 (6152 - kv.1) =
          s.regValue .rsp - BitVec.ofNat 64 kv.1 := by
        rw [localAddr s (by omega), Nat.sub_sub_self (by omega : kv.1 ≤ 6152)]
      rw [← eq, kept w4 (6152 - kv.1) (by omega), eq]
      exact saved.registers kv h
    · have h := kept w4 6152 (by decide)
      rw [localAddr s (by decide)] at h
      simpa only [Nat.sub_self, BitVec.sub_zero, saved.ret] using h
  have savedCleared : Saved s cleared := by
    apply savedCopied.of_frame call (cw 32 (by decide))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (sp + BitVec.ofNat 64 344).toNat + 32 ≤ _
    rw [localAddr s (i := 344) (by decide)]
    change (s.regValue .rsp - BitVec.ofNat 64 5808).toNat + 32 ≤ _
    have atOffset : (s.regValue .rsp - BitVec.ofNat 64 5808).toNat =
        (s.regValue .rsp).toNat - 5808 :=
      Common.stackOffset (off := 5808) call.stackAvailable (by decide)
    rw [atOffset]
    omega
  have finalBytes : output.HasBytes cleared bytes := by
    have data := copyHasBytes (dst := dst) serialized initialDst.readable
    refine ⟨data.1, fun i => ?_⟩
    have len : bytes.size = 32 := data.1
    have hi := i.isLt
    have addr : dst.toNat + i.val < 2^64 := by omega
    rw [(cw 32 (by decide)).outside _ ?_]
    · exact data.2 i
    · refine ⟨?_, fun r hr => ?_⟩
      · change (BitVec.ofNat 64 (dst.toNat + i.val)).toNat + 1 ≤ 2^64
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addr]
        omega
      · obtain rfl := List.mem_singleton.mp hr
        change (BitVec.ofNat 64 (dst.toNat + i.val)).toNat + 1 ≤ scratch.start ∨
          scratch.start + 32 ≤ (BitVec.ofNat 64 (dst.toNat + i.val)).toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addr]
        have h := stackRange (i := 344) (n := 32) (by decide) (by decide)
        have hlo : (s.regValue .rsp).toNat - 10088 ≤ scratch.start := h.1
        have hup := h.2.1
        change scratch.start + 32 ≤ (s.regValue .rsp).toNat - 10088 +
          ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10088)) at hup
        omega
  have codeIncluded := fun x hx => Common.fnCode_subset_programImage x (code_l101b1d x hx)
  have storeWord {t : Ram} (frame : RamWriteFrame m t [output]) (i off k : Nat)
      (hi : i + 8 ≤ 32) (hc : off + k ≤ bytes_l101b1d.length) :
      StoreOk code t (dst + BitVec.ofNat 64 i) 8 (0x101b1d + BitVec.ofNat 64 off) k := by
    have within := outputOffset dstLow (i := i) (by omega)
    have dest : Writable code t (dst + BitVec.ofNat 64 i) 8 :=
      (initialDst.sub (by rw [within]; omega) (by rw [within]; omega)).of_frame frame
    exact ParseSignature.storeOk_of_codeRange dest codeIncluded hc
  have loadWord {t : Ram} (frame : RamWriteFrame m t [output]) (i : Nat)
      (hi : i ≤ 6152) : LoadOk t (sp + BitVec.ofNat 64 i) 8 := by
    have rd := (stackWritable (n := 8) hi (by omega) (by decide)).readable.of_frame frame
    exact ⟨rd.low, rd.present⟩
  have clearGuard (i : Nat) (hi : i < 32) :
      StoreOk code (clearMemory copied sp i) (sp + BitVec.ofNat 64 (344 + i)) 1
        (0x101b1d + BitVec.ofNat 64 (47 + 8 * i)) 8 := by
    have dest := ((stackWritable (i := 344 + i) (n := 1) (by omega) (by omega)
      (by decide)).of_frame w4).of_frame (cw i (by omega))
    exact ParseSignature.storeOk_of_codeRange dest codeIncluded (by
      have len : bytes_l101b1d.length = 321 := by decide +kernel
      omega)
  have slotReady (i : BitVec 64) (hi : i.toNat ≤ 6152) :
      LoadOk (clearMemory copied sp 32) (sp + i) 8 := by
    have rd := ((stackWritable (n := 8) hi (by omega) (by decide)).readable.of_frame w4).of_frame
      (cw 32 (by decide))
    have ready := (show LoadOk cleared (sp + BitVec.ofNat 64 i.toNat) 8 from ⟨rd.low, rd.present⟩)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at ready
    exact ready
  obtain ⟨ret, slot, retLow, _⟩ := call.returnAddress
  have retAddr : sp + 6152 = s.regValue .rsp := by dsimp [sp, localSp]; exact BitVec.sub_add_cancel _ _
  have afterRet : sp + 6160 = (returnBoundary s).rsp := by
    change sp + 6160 = s.regValue .rsp + 8
    rw [show (6160 : BitVec 64) = 6152 + 8 by rfl, ← BitVec.add_assoc, retAddr]
  have lowTag : (memLoad (clearMemory copied sp 32) (sp + 6152) 64).toNat < 2^32 := by
    have eq : (returnBoundary s).rip = ret := memLoad_returnSlot slot
    change (memLoad cleared (sp + 6152) 64).toNat < 2^32
    rw [retAddr, savedCleared.ret, eq]
    exact retLow
  have rspBits : a[4].get 64 = sp := by rw [rsp]; rfl
  have dstBits : a[3].get 64 = dst := by rw [rbx]; rfl
  have folded1 : memStore m (dst + 24) (memLoad m (sp + 368) 64) = m1 := rfl
  have folded2 : memStore m1 (dst + 16) (memLoad m (sp + 360) 64) = m2 := rfl
  have folded3 : memStore m2 (dst + 8) (memLoad m (sp + 352) 64) = m3 := rfl
  have folded4 : memStore m3 dst (memLoad m (sp + 344) 64) = clearMemory copied sp 0 := by
    simp only [clearMemory, copied, copyMemory, BitVec.add_zero]
    rfl
  have foldClear {i : Nat} {disp : BitVec 64} (h : disp = BitVec.ofNat 64 (344 + i)) :
      memStore (clearMemory copied sp i) (sp + disp) (0 : BitVec 8) =
        clearMemory copied sp (i + 1) := by subst disp; rfl
  have guardClear {i : Nat} {disp pc : BitVec 64} (hi : i < 32)
      (hd : disp = BitVec.ofNat 64 (344 + i)) (hp : pc = 0x101b1d + BitVec.ofNat 64 (47 + 8 * i)) :
      StoreOk code (clearMemory copied sp i) (sp + disp) 1 pc 8 := by
    subst disp pc
    exact clearGuard i hi
  have l0 : LoadOk m (sp + 368) 8 := loadWord w0 368 (by decide)
  have l1 : LoadOk m1 (sp + 360) 8 := loadWord w1 360 (by decide)
  have l2 : LoadOk m2 (sp + 344) 8 := loadWord w2 344 (by decide)
  have l3 : LoadOk m2 (sp + 352) 8 := loadWord w2 352 (by decide)
  have st0 : StoreOk code m (dst + 24) 8 0x101b25 4 :=
    storeWord w0 24 8 4 (by decide) (by decide +kernel)
  have st1 : StoreOk code m1 (dst + 16) 8 0x101b31 4 :=
    storeWord w1 16 20 4 (by decide) (by decide +kernel)
  have st2 : StoreOk code m2 (dst + 8) 8 0x101b45 4 :=
    storeWord w2 8 40 4 (by decide) (by decide +kernel)
  have st3 : StoreOk code m3 dst 8 0x101b49 3 := by
    change StoreOk code m3 dst 8 (0x101b1d + BitVec.ofNat 64 44) 3
    simpa only [BitVec.add_zero] using storeWord w3 0 44 3 (by decide) (by decide +kernel)
  have r1 : memLoad m1 (sp + 360) 64 = memLoad m (sp + 360) 64 := kept w1 360 (by decide)
  have r2 : memLoad m2 (sp + 344) 64 = memLoad m (sp + 344) 64 := kept w2 344 (by decide)
  have r3 : memLoad m2 (sp + 352) 64 = memLoad m (sp + 352) 64 := kept w2 352 (by decide)
  have block : ∃ out, program.runBlock (dialect code) ⟨.l101b1d, a, m⟩ = .returned out ∧
      Common.Returned s (regions s) out ∧ output.HasBytes out.store bytes := by
    refine ⟨?out, ?eval, ?post⟩
    case eval =>
      cfg_eval [rspBits, dstBits, l0, l1, l2, l3, st0, st1, st2, st3, r1, r2, r3,
        folded1, folded2, folded3, folded4]
      simp (config := { maxSteps := 1000000 }) (disch := first | rfl | decide) only
        [guardClear, foldClear, ↓reduceIte, Nat.reduceAdd]
      simp (disch := decide) only [slotReady, lowTag, and_self, ↓reduceIte]
      rfl
    case post =>
      refine ⟨⟨?_, congrArg (fun x => (⟨64, x⟩ : Value)) afterRet, df, ?_, totalFrame, rfl⟩,
        finalBytes⟩
      · change some (⟨64, memLoad cleared (sp + 6152) 64⟩ : Value) = _
        rw [retAddr, savedCleared.ret]
      · intro ⟨i, hi⟩ hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
        · exact congrArg (fun x => (⟨64, x⟩ : Value)) (restored savedCleared 48 .rbx (by decide) (by decide))
        · exact congrArg (fun x => (⟨64, x⟩ : Value)) (restored savedCleared 8 .rbp (by decide) (by decide))
        · exact congrArg (fun x => (⟨64, x⟩ : Value)) (restored savedCleared 40 .r12 (by decide) (by decide))
        · exact congrArg (fun x => (⟨64, x⟩ : Value)) (restored savedCleared 32 .r13 (by decide) (by decide))
        · exact congrArg (fun x => (⟨64, x⟩ : Value)) (restored savedCleared 24 .r14 (by decide) (by decide))
        · exact congrArg (fun x => (⟨64, x⟩ : Value)) (restored savedCleared 16 .r15 (by decide) (by decide))
  obtain ⟨out, he, post⟩ := block
  exact ⟨out, .done (congrArg (Transfer.next _ []) he), post⟩

end K256.Proofs.Ecdh.Output
