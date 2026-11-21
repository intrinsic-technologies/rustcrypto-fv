import X86Proofs.Step.PrefixScan
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode31

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode30_run_of_memory (context : Instruction_Context) (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_30 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_30, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

theorem selectLegacy0Opcode80_run_of_r6_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

theorem selectLegacy0Opcode80_run_of_r7_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode30_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_30 ip context).run s =
      (X86.Instructions.XOR_MEMb_GPR8 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_30
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_30 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy0Opcode30_run_of_memory context hlock a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy0Opcode80_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.XOR_MEMb_IMMb_80r6 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_80 context mode a b c d e f modrm) _ 11 hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r6_memory context hlock a b c d e f modrm hmod hreg)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy0Opcode80_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.CMP_MEMb_IMMb_80r7 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_80 context mode a b c d e f modrm) _ 17 hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r7_memory context a b c d e f modrm hmod hreg)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy0_run_of_modrm_at [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (op modrm : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (dec form : X86.Runtime.SpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = some (dec.run u))
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → dec.run a = form.run u) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some (form.run (afterFetches (beforeFetch s) (j + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (j + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) hfeatures]

theorem decodeLegacy0_run_of_31_memory [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x31)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hlock : ctx.lock_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.XOR_MEMv_GPRv (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x31 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode31 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode31_run_of_memory a u _ ctx _ hmod hlock hmode hfe hf)

theorem decodeLegacy0_run_of_30_memory [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x30)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hlock : ctx.lock_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.XOR_MEMb_GPR8 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x30 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode30 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode30_run_of_memory a u _ ctx _ hmod hlock hmode hfe hf)

theorem decodeLegacy0_run_of_80_r6_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 6) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x80)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hlock : ctx.lock_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.XOR_MEMb_IMMb_80r6 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x80 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode80 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode80_run_of_r6_memory a u _ ctx _ hmod hreg hlock hmode hfe hf)

theorem decodeLegacy0_run_of_80_r7_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 7) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x80)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CMP_MEMb_IMMb_80r7 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x80 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode80 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode80_run_of_r7_memory a u _ ctx _ hmod hreg hmode hfe hf)

end X86Proofs
