import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Fixslice.Sbox
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.LIR.Fn100e90.Frame
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store
import AesGcm.Proofs.Copied.X86Proofs.Refine.Frame
import AesGcm.Proofs.Copied.X86Proofs.Refine.Tactic

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open AesGcm.Proofs.Machine.LIR AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.Instructions X86Proofs.Refine

def sboxSavedMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let rsp := (args[4]).get 64
  let mem := memStore mem (rsp - BitVec.ofNat 64 8) ((args[5]).get 64)
  let mem := memStore mem (rsp - BitVec.ofNat 64 16) ((args[15]).get 64)
  let mem := memStore mem (rsp - BitVec.ofNat 64 24) ((args[14]).get 64)
  let mem := memStore mem (rsp - BitVec.ofNat 64 32) ((args[13]).get 64)
  let mem := memStore mem (rsp - BitVec.ofNat 64 40) ((args[12]).get 64)
  memStore mem (rsp - BitVec.ofNat 64 48) ((args[3]).get 64)

private theorem lengthChecks_runBlock (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (l target : Label)
    (hlabel : (l, target) ∈ [(.l100ea7, .l100eb1),
        (.l100eb1, .l100ebb),
        (.l100ebb, .l100ec5),
        (.l100ec5, .l100ecf),
        (.l100ecf, .l100ed9),
        (.l100ed9, .l100ee3),
        (.l100ee3, .l100eed)])
    (hrsi : (args[6]).get 64 = 8) :
    ∃ out : Values Value Reg.count, program.runBlock (dialect code) ⟨l, args, mem⟩ = .jump ⟨target,
      out, mem⟩ ∧
      out[4] = args[4] ∧ out[5] = args[5] ∧ out[6] = args[6] ∧
      out[7] = args[7] ∧ out[22] = args[22] ∧
      out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
  rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cfg_eval
  all_goals simp only [hrsi]
  all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem lengthChecks_reaches (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) (hrsi : (args[6]).get 64 = 8) :
    ∃ out : Values Value Reg.count,
      (program.sem (dialect code)).Reaches
        ⟨⟨.l100ea7, args, mem⟩, []⟩
        ⟨⟨.l100eed, out, mem⟩, []⟩ ∧
      out[4] = args[4] ∧ out[5] = args[5] ∧ out[6] = args[6] ∧
      out[7] = args[7] ∧ out[22] = args[22] ∧
      out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51] := by
  change ∃ out : Values Value Reg.count,
    (program.sem (dialect code)).Reaches
      ⟨⟨.l100ea7, args, mem⟩, []⟩ ⟨⟨.l100eed, out, mem⟩, []⟩ ∧
    out[4] = args[4] ∧ out[5] = args[5] ∧ out[6] = args[6] ∧
    out[7] = args[7] ∧ out[22] = args[22] ∧
    out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51]
  obtain ⟨a1, hj1, h4_1, h5_1, h6_1, h7_1, h22_1, h39_1, h50_1, h51_1⟩ :=
    lengthChecks_runBlock code args mem .l100ea7 .l100eb1 (by simp) hrsi
  have hr1 : (a1[6]).get 64 = 8 := by rw [h6_1, hrsi]
  obtain ⟨a2, hj2, h4_2, h5_2, h6_2, h7_2, h22_2, h39_2, h50_2, h51_2⟩ :=
    lengthChecks_runBlock code a1 mem .l100eb1 .l100ebb (by simp) hr1
  have hr2 : (a2[6]).get 64 = 8 := by rw [h6_2, hr1]
  obtain ⟨a3, hj3, h4_3, h5_3, h6_3, h7_3, h22_3, h39_3, h50_3, h51_3⟩ :=
    lengthChecks_runBlock code a2 mem .l100ebb .l100ec5 (by simp) hr2
  have hr3 : (a3[6]).get 64 = 8 := by rw [h6_3, hr2]
  obtain ⟨a4, hj4, h4_4, h5_4, h6_4, h7_4, h22_4, h39_4, h50_4, h51_4⟩ :=
    lengthChecks_runBlock code a3 mem .l100ec5 .l100ecf (by simp) hr3
  have hr4 : (a4[6]).get 64 = 8 := by rw [h6_4, hr3]
  obtain ⟨a5, hj5, h4_5, h5_5, h6_5, h7_5, h22_5, h39_5, h50_5, h51_5⟩ :=
    lengthChecks_runBlock code a4 mem .l100ecf .l100ed9 (by simp) hr4
  have hr5 : (a5[6]).get 64 = 8 := by rw [h6_5, hr4]
  obtain ⟨a6, hj6, h4_6, h5_6, h6_6, h7_6, h22_6, h39_6, h50_6, h51_6⟩ :=
    lengthChecks_runBlock code a5 mem .l100ed9 .l100ee3 (by simp) hr5
  have hr6 : (a6[6]).get 64 = 8 := by rw [h6_6, hr5]
  obtain ⟨a7, hj7, h4_7, h5_7, h6_7, h7_7, h22_7, h39_7, h50_7, h51_7⟩ :=
    lengthChecks_runBlock code a6 mem .l100ee3 .l100eed (by simp) hr6
  have hs1 : program.step (dialect code) ⟨⟨.l100ea7, args, mem⟩, []⟩ =
      .next ⟨⟨.l100eb1, a1, mem⟩, []⟩ := by rw [Program.step, hj1]; rfl
  have hs2 : program.step (dialect code) ⟨⟨.l100eb1, a1, mem⟩, []⟩ =
      .next ⟨⟨.l100ebb, a2, mem⟩, []⟩ := by rw [Program.step, hj2]; rfl
  have hs3 : program.step (dialect code) ⟨⟨.l100ebb, a2, mem⟩, []⟩ =
      .next ⟨⟨.l100ec5, a3, mem⟩, []⟩ := by rw [Program.step, hj3]; rfl
  have hs4 : program.step (dialect code) ⟨⟨.l100ec5, a3, mem⟩, []⟩ =
      .next ⟨⟨.l100ecf, a4, mem⟩, []⟩ := by rw [Program.step, hj4]; rfl
  have hs5 : program.step (dialect code) ⟨⟨.l100ecf, a4, mem⟩, []⟩ =
      .next ⟨⟨.l100ed9, a5, mem⟩, []⟩ := by rw [Program.step, hj5]; rfl
  have hs6 : program.step (dialect code) ⟨⟨.l100ed9, a5, mem⟩, []⟩ =
      .next ⟨⟨.l100ee3, a6, mem⟩, []⟩ := by rw [Program.step, hj6]; rfl
  have hs7 : program.step (dialect code) ⟨⟨.l100ee3, a6, mem⟩, []⟩ =
      .next ⟨⟨.l100eed, a7, mem⟩, []⟩ := by rw [Program.step, hj7]; rfl
  refine ⟨a7, .step hs1 (.step hs2 (.step hs3 (.step hs4 (.step hs5 (.step hs6 (.step hs7 (.refl _))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h4_7.trans (h4_6.trans (h4_5.trans (h4_4.trans (h4_3.trans (h4_2.trans (h4_1))))))
  · exact h5_7.trans (h5_6.trans (h5_5.trans (h5_4.trans (h5_3.trans (h5_2.trans (h5_1))))))
  · exact h6_7.trans (h6_6.trans (h6_5.trans (h6_4.trans (h6_3.trans (h6_2.trans (h6_1))))))
  · exact h7_7.trans (h7_6.trans (h7_5.trans (h7_4.trans (h7_3.trans (h7_2.trans (h7_1))))))
  · exact h22_7.trans (h22_6.trans (h22_5.trans (h22_4.trans (h22_3.trans (h22_2.trans (h22_1))))))
  · exact h39_7.trans (h39_6.trans (h39_5.trans (h39_4.trans (h39_3.trans (h39_2.trans (h39_1))))))
  · exact h50_7.trans (h50_6.trans (h50_5.trans (h50_4.trans (h50_3.trans (h50_2.trans (h50_1))))))
  · exact h51_7.trans (h51_6.trans (h51_5.trans (h51_4.trans (h51_3.trans (h51_2.trans (h51_1))))))

theorem_by subBytes_body_eval (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

namespace SboxSSA
local instance : HXor Bool Bool Bool := ⟨Bool.xor⟩
local instance : HAnd Bool Bool Bool := ⟨Bool.and⟩
local instance : HOr Bool Bool Bool := ⟨Bool.or⟩
local instance : Complement Bool := ⟨Bool.not⟩
private def forward {α : Type} [HXor α α α] [HAnd α α α] [HOr α α α] [Complement α]
    (x : Fin 8 → α) : Fin 8 → α :=
  let v53 := x 1
  let v55 := x 2
  let v57 := x 4
  let v59 := x 6
  let v61 := x 7
  let v63 := v57
  let v65 := v57
  let v68 := (v63 ^^^ v55)
  let v70 := v61
  let v72 := (v70 ^^^ v53)
  let v75 := (v72 ^^^ v68)
  let v78 := v68
  let v81 := x 3
  let v83 := (v81 ^^^ v75)
  let v85 := v83
  let v87 := (v85 ^^^ v55)
  let v89 := (v83 ^^^ v59)
  let v91 := v61
  let v93 := (v91 ^^^ v65)
  let v96 := v89
  let v98 := (v96 ^^^ v93)
  let v100 := v98
  let v102 := v98
  let v105 := (v100 &&& v93)
  let v107 := (v59 ^^^ x 5)
  let v109 := (v55 ^^^ v61)
  let v111 := v87
  let v114 := (v111 ^^^ v107)
  let v116 := v102
  let v118 := (v116 ^^^ v114)
  let v121 := (v118 &&& v78)
  let v123 := (v121 ^^^ v105)
  let v125 := v114
  let v127 := (v125 &&& v109)
  let v129 := v109
  let v131 := (v127 ^^^ v105)
  let v133 := x 0
  let v135 := v102
  let v137 := (v135 ^^^ v133)
  let v139 := v137
  let v142 := v102
  let v144 := (v142 ^^^ v107)
  let v146 := v144
  let v149 := (v107 ^^^ v133)
  let v151 := v149
  let v153 := (v151 ^^^ v61)
  let v156 := v139
  let v158 := (v156 &&& v153)
  let v160 := (v158 ^^^ v61)
  let v162 := v87
  let v164 := (v162 &&& v75)
  let v166 := v146
  let v168 := v72
  let v170 := (v166 &&& v168)
  let v172 := v57
  let v174 := (v172 ^^^ v149)
  let v177 := (v174 &&& v133)
  let v180 := (v177 ^^^ v129)
  let v183 := (v180 ^^^ v164)
  let v185 := (v183 ^^^ v114)
  let v187 := (v185 ^^^ v131)
  let v189 := (v131 ^^^ v170)
  let v191 := (v189 ^^^ v160)
  let v193 := (v53 ^^^ v149)
  let v195 := v193
  let v197 := (v195 &&& v149)
  let v199 := (v197 ^^^ v168)
  let v201 := (v199 ^^^ v170)
  let v203 := (v89 ^^^ v164)
  let v205 := v87
  let v207 := (v205 ^^^ v133)
  let v209 := v193
  let v211 := (v209 ^^^ v129)
  let v213 := v207
  let v215 := (v213 &&& v211)
  let v217 := (v203 ^^^ v215)
  let v219 := (v201 ^^^ v123)
  let v221 := (v217 ^^^ v123)
  let v223 := v219
  let v225 := v144
  let v227 := (v223 ^^^ v225)
  let v229 := v227
  let v231 := (v229 &&& v221)
  let v233 := v231
  let v235 := (v233 ^^^ v187)
  let v237 := (v219 ^^^ v191)
  let v239 := (v237 &&& v235)
  let v241 := v191
  let v243 := (v241 ^^^ v225)
  let v245 := v239
  let v247 := (v239 ^^^ v231)
  let v249 := v231
  let v251 := (v249 ^^^ v243)
  let v253 := (v221 ^^^ v187)
  let v255 := v251
  let v257 := (v255 &&& v253)
  let v259 := (v257 ^^^ v187)
  let v261 := (v245 ^^^ v243)
  let v263 := (v247 &&& v243)
  let v265 := (v251 ^^^ v263)
  let v267 := (v265 &&& v259)
  let v269 := (v267 ^^^ v253)
  let v271 := v269
  let v273 := (v271 ^^^ v259)
  let v275 := (v225 &&& v273)
  let v278 := (v273 &&& v72)
  let v280 := (v263 ^^^ v227)
  let v282 := v87
  let v284 := (v282 &&& v280)
  let v286 := v280
  let v288 := (v280 &&& v75)
  let v290 := (v193 &&& v269)
  let v292 := (v149 &&& v269)
  let v294 := (v286 ^^^ v261)
  let v296 := (v269 ^^^ v294)
  let v298 := (v211 &&& v294)
  let v300 := (v294 &&& v207)
  let v302 := (v153 &&& v259)
  let v303 := (v137 &&& v259)
  let v304 := (v292 ^^^ v275)
  let v306 := (v114 &&& v296)
  let v308 := v129
  let v310 := (v308 &&& v296)
  let v312 := (v300 ^^^ v284)
  let v314 := (v312 ^^^ v304)
  let v316 := (v259 ^^^ v261)
  let v318 := (v296 ^^^ v316)
  let v320 := v118
  let v322 := (v320 &&& v318)
  let v324 := (v322 ^^^ v304)
  let v326 := (v318 &&& v68)
  let v328 := v98
  let v330 := (v328 &&& v316)
  let v332 := (v316 &&& v93)
  let v334 := v174
  let v336 := (v334 &&& v261)
  let v338 := (v326 ^^^ v332)
  let v340 := (v298 ^^^ v338)
  let v342 := (v336 ^^^ v340)
  let v344 := (v340 ^^^ v288)
  let v346 := (v261 &&& v133)
  let v348 := (v346 ^^^ v284)
  let v350 := (v330 ^^^ v324)
  let v352 := (v306 ^^^ v348)
  let v354 := (v352 ^^^ v278)
  let v356 := (v354 ^^^ v324)
  let v358 := (v332 ^^^ v310)
  let v360 := (v348 ^^^ v303)
  let v362 := (v360 ^^^ v275)
  let v364 := (v290 ^^^ v362)
  let v366 := (v364 ^^^ v338)
  let v368 := v302
  let v370 := (v368 ^^^ v356)
  let v372 := (v356 ^^^ v366)
  let v374 := (v366 ^^^ v278)
  let v378 := (v342 ^^^ v370)
  let v381 := (v314 ^^^ v344)
  let v383 := (v362 ^^^ v381)
  let v386 := (v344 ^^^ v350)
  let v389 := (v381 ^^^ v350)
  let v391 := (v358 ^^^ v350)
  let v393 := (v391 ^^^ v370)
  fun p ↦ match p.val with
  | 0 => v374
  | 1 => v372
  | 2 => v378
  | 3 => v383
  | 4 => v381
  | 5 => v393
  | 6 => v389
  | _ => v386
set_option maxRecDepth 8192 in
private theorem forward_bool : ∀ (a b c d e f g h : Bool) (p : Fin 8),
    forward (fun q ↦ match q.val with
      | 0 => a | 1 => b | 2 => c | 3 => d
      | 4 => e | 5 => f | 6 => g | _ => h) p =
    subBytesCircuit (fun q ↦ match q.val with
      | 0 => a | 1 => b | 2 => c | 3 => d
      | 4 => e | 5 => f | 6 => g | _ => h) p := by
  decide +kernel

private theorem forward_bool_fun (x : Fin 8 → Bool) (p : Fin 8) :
    forward x p = subBytesCircuit x p := by
  have hx : (fun q : Fin 8 ↦ match q.val with
      | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3
      | 4 => x 4 | 5 => x 5 | 6 => x 6 | _ => x 7) = x := by
    funext q
    rcases q with ⟨q, hq⟩
    have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
    rcases h with h | h | h | h | h | h | h | h <;> subst q <;> rfl
  simpa only [hx] using forward_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) p

private theorem getLsbD_forward (x : Planes) (p : Fin 8) (i : Fin 64) :
    (forward x p).getLsbD i.val = forward (fun q ↦ (x q).getLsbD i.val) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [forward, BitVec.getLsbD_xor, BitVec.getLsbD_and]; rfl)

private theorem forward_eq (x : Planes) : forward x = subBytes x := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_forward x p ⟨i, hi⟩, getLsbD_subBytes]
  exact forward_bool_fun _ _

end SboxSSA

private theorem stateWord_writable {code : CodeMap} {mem : Ram} {a : BitVec 64}
    (h : Writable code mem a 64) (p : Fin 8) :
    Writable code mem (a + BitVec.ofNat 64 (8 * p.val)) 8 := by
  apply h.of_offsets (x := a) (c := BitVec.ofNat 64 (8 * p.val)) (d := 0)
    rfl (addr_self a)
  exact (by decide +kernel : ∀ q : Fin 8,
    (BitVec.ofNat 64 (8 * q.val) - 0).toNat + 8 ≤ 64) p


set_option maxHeartbeats 1000000 in
private theorem entry_runBlock (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hc : ∀ x ∈ fnCode, x ∈ code)
    (hrsi : (args[6]).get 64 = 8)
    (hstack : Writable code mem
      ((args[4]).get 64 - BitVec.ofNat 64 (0x120))
      (0x120)) :
    let rsp := (args[4]).get 64
    let m1 := memStore mem (rsp - 8) ((args[5]).get 64)
    let m2 := memStore m1 (rsp - 16) ((args[15]).get 64)
    let m3 := memStore m2 (rsp - 24) ((args[14]).get 64)
    let m4 := memStore m3 (rsp - 32) ((args[13]).get 64)
    let m5 := memStore m4 (rsp - 40) ((args[12]).get 64)
    let m6 := memStore m5 (rsp - 48) ((args[3]).get 64)
    ∃ out : Values Value Reg.count,
      program.runBlock (dialect code)
        ⟨.l100e90, args, mem⟩ =
      .jump ⟨.l100ea7, out, m6⟩ ∧
      out[4] = ⟨64, rsp - (0x98)⟩ ∧
      out[5] = args[5] ∧ out[6] = args[6] ∧ out[7] = args[7] ∧ out[22] = args[22] ∧
      out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51] := by
  let pc : BitVec 64 := 0x100e90
  let bytes : List UInt8 := bytes_l100e90
  have hcode : ∀ x ∈ codeRange pc bytes, x ∈ code := by
    intro x hx
    apply hc x
    exact code_l100e90 x hx
  have hlen : bytes.length = 23 := by rfl
  have slot (k : Fin 6) : Writable code mem
      ((args[4]).get 64 - BitVec.ofNat 64 (8 * (k.val + 1))) 8 := by
    apply hstack.of_offsets
      (addr_sub ((args[4]).get 64) (BitVec.ofNat 64 (8 * (k.val + 1))))
      (addr_sub ((args[4]).get 64)
        (BitVec.ofNat 64 (0x120)))
    exact (by decide +kernel : ∀ j : Fin 6,
      ((0 - BitVec.ofNat 64 (8 * (j.val + 1))) -
        (0 - BitVec.ofNat 64 0x120)).toNat + 8 ≤
          0x120) k
  have g0 : StoreOk code mem
      ((args[4]).get 64 - 8) 8
      (pc + 0) 1 := by
    apply storeOk_of_writable (slot 0)
    exact X86Proofs.Refine.RangeApart.right_sub (storeOk_of_codeRange (slot 0)
      hcode).apart
      (off := 0) (by rw [hlen]; decide)
  have g1 : StoreOk code mem
      ((args[4]).get 64 - 16) 8
      (pc + 1) 2 := by
    apply storeOk_of_writable (slot 1)
    exact X86Proofs.Refine.RangeApart.right_sub (storeOk_of_codeRange (slot 1)
      hcode).apart
      (off := 1) (by rw [hlen]; decide)
  have g2 : StoreOk code mem
      ((args[4]).get 64 - 24) 8
      (pc + 3) 2 := by
    apply storeOk_of_writable (slot 2)
    exact X86Proofs.Refine.RangeApart.right_sub (storeOk_of_codeRange (slot 2)
      hcode).apart
      (off := 3) (by rw [hlen]; decide)
  have g3 : StoreOk code mem
      ((args[4]).get 64 - 32) 8
      (pc + 5) 2 := by
    apply storeOk_of_writable (slot 3)
    exact X86Proofs.Refine.RangeApart.right_sub (storeOk_of_codeRange (slot 3)
      hcode).apart
      (off := 5) (by rw [hlen]; decide)
  have g4 : StoreOk code mem
      ((args[4]).get 64 - 40) 8
      (pc + 7) 2 := by
    apply storeOk_of_writable (slot 4)
    exact X86Proofs.Refine.RangeApart.right_sub (storeOk_of_codeRange (slot 4)
      hcode).apart
      (off := 7) (by rw [hlen]; decide)
  have g5 : StoreOk code mem
      ((args[4]).get 64 - 48) 8
      (pc + 9) 1 := by
    apply storeOk_of_writable (slot 5)
    exact X86Proofs.Refine.RangeApart.right_sub (storeOk_of_codeRange (slot 5)
      hcode).apart
      (off := 9) (by rw [hlen]; decide)
  let saved := memStore
    (memStore
      (memStore
        (memStore
          (memStore
            (memStore mem ((args[4]).get 64 - 8) ((args[5]).get 64))
            ((args[4]).get 64 - 16) ((args[15]).get 64))
          ((args[4]).get 64 - 24) ((args[14]).get 64))
        ((args[4]).get 64 - 32) ((args[13]).get 64))
      ((args[4]).get 64 - 40) ((args[12]).get 64))
    ((args[4]).get 64 - 48) ((args[3]).get 64)
  dsimp only
  all_goals simp (config := {bitVecOfNat := false}) only [pc,
    BitVec.reduceAdd] at g0 g1 g2 g3 g4 g5
  change ∃ out : Values Value Reg.count,
        program.runBlock (dialect code) ⟨.l100e90, args, mem⟩ =
          .jump ⟨.l100ea7, out, saved⟩ ∧
        out[4] = ⟨64, (args[4]).get 64 - 0x98⟩ ∧ out[5] = args[5] ∧
        out[6] = args[6] ∧ out[7] = args[7] ∧ out[22] = args[22] ∧
    out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51]
  all_goals cfg_eval
  all_goals simp only [BitVec.ofNat_eq_ofNat] at g0 g1 g2 g3 g4 g5 ⊢
  all_goals simp (config := {bitVecOfNat := false, maxDischargeDepth := 20}) only
    [storeOk_memStore, g0, g1, g2, g3, g4, g5, ↓reduceIte]
  all_goals simp only [hrsi]
  all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


private theorem entry_reaches (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hc : ∀ x ∈ fnCode, x ∈ code) (hrsi : (args[6]).get 64 = 8)
    (hstack : Writable code mem
      ((args[4]).get 64 - BitVec.ofNat 64 (0x120))
      (0x120)) :
    let saved := sboxSavedMemory args mem
    ∃ out : Values Value Reg.count,
      (program.sem (dialect code)).Reaches
        ⟨⟨.l100e90, args, mem⟩, []⟩
        ⟨⟨.l100eed, out, saved⟩, []⟩ ∧
      out[4] = ⟨64, (args[4]).get 64 - (0x98)⟩ ∧
      out[5] = args[5] ∧ out[6] = args[6] ∧ out[7] = args[7] ∧ out[22] = args[22] ∧
      out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51] := by
  obtain ⟨mid, hm, h4, h5, h6, h7, h22, h39, h50, h51⟩ := entry_runBlock code args mem hc hrsi hstack
  have hmid : (mid[6]).get 64 = 8 := by rw [h6, hrsi]
  obtain ⟨out, ho, o4, o5, o6, o7, o22, o39, o50, o51⟩ := lengthChecks_reaches code mid _ hmid
  have hs : program.step (dialect code)
      ⟨⟨.l100e90, args, mem⟩, []⟩ =
      .next ⟨⟨.l100ea7, mid,
        sboxSavedMemory args mem⟩, []⟩ := by
    rw [Program.step, hm]
    rfl
  exact ⟨out, (Semantics.Reaches.single hs).trans ho,
    o4.trans h4, o5.trans h5, o6.trans h6, o7.trans h7, o22.trans h22, o39.trans h39, o50.trans h50, o51.trans h51⟩

private theorem stackSlot_inRegion (fr : Activation) (k : Nat)
    (hbound : fr.low.toNat + k ≤ fr.rsp.toNat) (hk : 8 ≤ k) :
    InRegion fr.region (fr.rsp - BitVec.ofNat 64 k) 8 := by
  have hklt : k < 2^64 := by have := fr.rsp.isLt; omega
  have hle : BitVec.ofNat 64 k ≤ fr.rsp := by
    simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt] using
      (show k ≤ fr.rsp.toNat by omega)
  have ha : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt]
  simp only [InRegion, Activation.region, ha]
  have := fr.rsp.isLt
  omega

private theorem stateWord_inRegion (fr : Activation) (p : Fin 8)
    (hlow : fr.rdi.toNat + 64 ≤ 2^32) :
    InRegion ⟨fr.rdi.toNat, 64⟩ (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 8 := by
  have hp := p.isLt
  have ha : (fr.rdi + BitVec.ofNat 64 (8 * p.val)).toNat = fr.rdi.toNat + 8 * p.val := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  simp only [InRegion, ha]
  omega


private theorem exactStoreGuard_of_codeRange {code : CodeMap} {mem : Ram}
    {a p : BitVec 64} {n off len : Nat} {bytes : List UInt8}
    (hw : Writable code mem a n)
    (hc : ∀ x ∈ codeRange p bytes, x ∈ code) (hoff : off + len ≤ bytes.length) :
    StoreOk code mem a n (p + BitVec.ofNat 64 off) len :=
  storeOk_of_writable hw
    (X86Proofs.Refine.RangeApart.right_sub
      (storeOk_of_codeRange hw hc).apart hoff)

set_option maxRecDepth 4096 in
private theorem subBytes_storeGuards (code : CodeMap) (mem : Ram)
    (rsp rdi : BitVec 64) (hc : ∀ x ∈ fnCode, x ∈ code)
    (hstack : Writable code mem rsp 104)
    (hstate : Writable code mem rdi 64) :
    StoreOk code mem (rsp + 8) 8 0x100f07 5 ∧
    StoreOk code mem (rsp + 16) 8 0x100f15 5 ∧
    StoreOk code mem (rsp + 40) 8 0x100f1d 5 ∧
    StoreOk code mem (rsp + 88) 8 0x100f25 5 ∧
    StoreOk code mem (rsp + 96) 8 0x100f40 5 ∧
    StoreOk code mem (rsp + 72) 8 0x100f51 5 ∧
    StoreOk code mem (rsp + 24) 8 0x100f63 5 ∧
    StoreOk code mem (rsp + 80) 8 0x100f71 5 ∧
    StoreOk code mem (rsp + 32) 8 0x100f94 5 ∧
    StoreOk code mem rsp 8 0x100fa2 4 ∧
    StoreOk code mem (rsp + 48) 8 0x100faf 5 ∧
    StoreOk code mem (rsp + 8) 8 0x100fd8 5 ∧
    StoreOk code mem (rsp + 64) 8 0x100fe0 5 ∧
    StoreOk code mem (rsp + 56) 8 0x100fe8 5 ∧
    StoreOk code mem rsp 8 0x10107d 4 ∧
    StoreOk code mem (rsp + 48) 8 0x1010ab 5 ∧
    StoreOk code mem (rsp + 32) 8 0x1010b0 5 ∧
    StoreOk code mem rdi 8 0x101134 3 ∧
    StoreOk code mem (rdi + 8) 8 0x101137 4 ∧
    StoreOk code mem (rdi + 16) 8 0x10113e 4 ∧
    StoreOk code mem (rdi + 24) 8 0x101148 4 ∧
    StoreOk code mem (rdi + 32) 8 0x10114f 4 ∧
    StoreOk code mem (rdi + 40) 8 0x10115c 4 ∧
    StoreOk code mem (rdi + 48) 8 0x101160 4 ∧
    StoreOk code mem (rdi + 56) 8 0x101164 4 := by
  have hbody : ∀ x ∈ codeRange 0x100eed bytes_l100eed, x ∈ code :=
    fun x hx ↦ hc x (code_l100eed x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 8) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 26) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 16) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 40) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 40) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 48) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 88) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 56) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 96) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 83) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 72) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 100) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 24) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 118) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 80) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 132) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 32) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 167) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 0) (d := 0) (n := 8)
        (addr_self rsp) (addr_self rsp) (by decide +kernel))
      hbody (off := 181) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 48) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 194) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 8) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 235) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 64) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 243) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 56) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 251) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 0) (d := 0) (n := 8)
        (addr_self rsp) (addr_self rsp) (by decide +kernel))
      hbody (off := 400) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 48) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 446) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstack.of_offsets (x := rsp) (c := 32) (d := 0) (n := 8)
        rfl (addr_self rsp) (by decide +kernel))
      hbody (off := 451) (len := 5) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 0) (d := 0) (n := 8)
        (addr_self rdi) (addr_self rdi) (by decide +kernel))
      hbody (off := 583) (len := 3) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 8) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 586) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 16) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 593) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 24) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 603) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 32) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 610) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 40) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 623) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 48) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 627) (len := 4) (by decide +kernel)
  · exact exactStoreGuard_of_codeRange
      (hstate.of_offsets (x := rdi) (c := 56) (d := 0) (n := 8)
        rfl (addr_self rdi) (by decide +kernel))
      hbody (off := 631) (len := 4) (by decide +kernel)

private theorem wordLoad_guard {mem : Ram} {base : BitVec 64} {n : Nat}
    (h : Readable mem base n) (off : Nat) (hoff : off + 8 ≤ n) :
    LoadOk mem (base + BitVec.ofNat 64 off) 8 := by
  apply LoadOk.of_offsets h (x := base) (c := BitVec.ofNat 64 off) (d := 0)
    rfl (addr_self base)
  have ho : off < 2^64 := by have := h.low; omega
  have he : (BitVec.ofNat 64 off - 0).toNat = off := by
    calc
      _ = (BitVec.ofNat 64 off).toNat :=
        congrArg BitVec.toNat (BitVec.sub_zero (BitVec.ofNat 64 off))
      _ = off := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  rw [he]
  exact hoff

private theorem bodyFrame_regions {code : CodeMap} {mem : Ram} {fr : Activation}
    {window depth alloc : Nat}
    (hstack : Writable code mem (fr.rsp - BitVec.ofNat 64 window) window)
    (hret : Readable mem fr.rsp 8) (hroom : fr.low.toNat + window ≤ fr.rsp.toNat)
    (halloc : alloc ≤ depth) (hdepth : depth ≤ window)
    (hdisjoint : (⟨fr.low.toNat, fr.rsp.toNat + 8 - fr.low.toNat⟩ : MemoryRegion).Disjoint
      ⟨fr.rdi.toNat, 64⟩) :
    Writable code mem (fr.rsp - BitVec.ofNat 64 depth) alloc ∧
    Readable mem (fr.rsp - BitVec.ofNat 64 depth) (depth + 8) ∧
    ((fr.rsp - BitVec.ofNat 64 depth).toNat + (depth + 8) ≤ fr.rdi.toNat ∨
      fr.rdi.toNat + 64 ≤ (fr.rsp - BitVec.ofNat 64 depth).toNat) ∧
    InRegion fr.region (fr.rsp - BitVec.ofNat 64 depth) alloc := by
  have hsub (k : Nat) (hk : k ≤ fr.rsp.toNat) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have ht : k < 2^64 := Nat.lt_of_le_of_lt hk fr.rsp.isLt
    have hle : BitVec.ofNat 64 k ≤ fr.rsp := by
      simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht] using hk
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
  have hw := hsub window (by omega)
  have hd := hsub depth (by omega)
  have hown : Writable code mem (fr.rsp - BitVec.ofNat 64 depth) alloc :=
    hstack.sub (by rw [hd, hw]; omega) (by rw [hd, hw]; omega)
  have hpref : Readable mem (fr.rsp - BitVec.ofNat 64 depth) depth :=
    hstack.readable.sub (by rw [hd, hw]; omega) (by rw [hd, hw]; omega)
  have hadd : fr.rsp - BitVec.ofNat 64 depth + BitVec.ofNat 64 depth = fr.rsp := by bv_omega
  have hlast : Readable mem
      (fr.rsp - BitVec.ofNat 64 depth + BitVec.ofNat 64 depth) 8 := by rwa [hadd]
  have hread := readable_append hpref hlast
  have hdj := Runtime.disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 64 (by omega) (by decide) hdisjoint
  have hin : InRegion fr.region (fr.rsp - BitVec.ofNat 64 depth) alloc := by
    simp only [InRegion, Activation.region, hd]
    have := fr.rsp.isLt
    omega
  refine ⟨hown, hread, ?_, hin⟩
  rw [hd]
  omega

open AesGcm.Proofs.Machine.Runtime

private theorem saved_writable {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {a : BitVec 64} {n : Nat} (h : Writable code mem a n) :
    Writable code (sboxSavedMemory args mem) a n := by
  unfold sboxSavedMemory
  exact (((((h.memStore _ _).memStore _ _).memStore _ _).memStore _ _).memStore _ _).memStore _ _

private theorem saved_readable {args : Values Value Reg.count}
    {mem : Ram} {a : BitVec 64} {n : Nat} (h : Readable mem a n) :
    Readable (sboxSavedMemory args mem) a n := by
  unfold sboxSavedMemory
  exact (((((h.memStore _ _).memStore _ _).memStore _ _).memStore _ _).memStore _ _).memStore _ _

private theorem saved_frame (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hrsp : (args[4]).get 64 = fr.rsp) (hroom : fr.low.toNat + 48 ≤ fr.rsp.toNat) :
    RamWriteFrame mem (sboxSavedMemory args mem) [fr.region] := by
  have slot (k : Nat) (hk : 8 ≤ k ∧ k ≤ 48) : InRegions [fr.region] (fr.rsp - BitVec.ofNat 64 k) 8 :=
    ⟨fr.region, by simp, stackSlot_inRegion fr k (by omega) hk.1⟩
  have h0 := RamWriteFrame.refl mem [fr.region]
  have h1 := h0.memStore ((args[5]).get 64) (slot 8 ⟨by decide, by decide⟩)
  have h2 := h1.memStore ((args[15]).get 64) (slot 16 ⟨by decide, by decide⟩)
  have h3 := h2.memStore ((args[14]).get 64) (slot 24 ⟨by decide, by decide⟩)
  have h4 := h3.memStore ((args[13]).get 64) (slot 32 ⟨by decide, by decide⟩)
  have h5 := h4.memStore ((args[12]).get 64) (slot 40 ⟨by decide, by decide⟩)
  have h6 := h5.memStore ((args[3]).get 64) (slot 48 ⟨by decide, by decide⟩)
  simpa only [sboxSavedMemory, hrsp] using h6

private theorem saved_word (args : Values Value Reg.count) (mem : Ram) (r : Fin Reg.count) (k : Nat)
    (hk : (r.val, k) ∈ [(3, 48), (12, 40), (13, 32), (14, 24), (15, 16), (5, 8)]) :
    memLoad (sboxSavedMemory args mem) ((args[4]).get 64 - BitVec.ofNat 64 k) 64 =
      (args[r]).get 64 := by
  rcases r with ⟨r, hr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [sboxSavedMemory]
  all_goals simp (disch := first | decide +kernel |
    (apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _); decide +kernel)) only
      [memLoad_memStore_same, memLoad_memStore_of_rangeApart, Fin.getElem_fin]

private theorem saved_return (args : Values Value Reg.count) (mem : Ram) :
    memLoad (sboxSavedMemory args mem) ((args[4]).get 64) 64 =
      memLoad mem ((args[4]).get 64) 64 := by
  simp only [sboxSavedMemory]
  simp (disch := first | decide +kernel |
    (apply RangeApart.of_offsets (addr_sub _ _) (addr_self _); decide +kernel)) only
      [memLoad_memStore_of_rangeApart]

private theorem saved_state (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hrsp : (args[4]).get 64 = fr.rsp) (hroom : fr.low.toNat + 48 ≤ fr.rsp.toNat)
    (hstate : Readable mem fr.rdi 64)
    (hap : (callStack fr).Disjoint (span fr.rdi 64)) (p : Fin 8) :
    memLoad (sboxSavedMemory args mem) (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 =
      memLoad mem (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 := by
  have hp := stateWord_inRegion fr p hstate.low
  change fr.rdi.toNat ≤ (fr.rdi + BitVec.ofNat 64 (8 * p.val)).toNat ∧
    (fr.rdi + BitVec.ofNat 64 (8 * p.val)).toNat + 8 ≤ fr.rdi.toNat + 64 ∧
    (fr.rdi + BitVec.ofNat 64 (8 * p.val)).toNat + 8 ≤ 2^64 at hp
  have hdis := Runtime.disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 64 (by omega) (by decide) hap
  apply (saved_frame fr args mem hrsp hroom).memLoad_eq
  refine ⟨hp.2.2, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  simp only [Activation.region]
  rcases hdis with hdis | hdis
  · right
    have := hp.1
    omega
  · left
    have := hp.2.1
    omega



runtime_ram_def AesGcm.Proofs.Machine.AES64.forwardRam from AesGcm.Proofs.Machine.AES64.subBytes_body_eval
open AesGcm.Proofs.Machine.LIR
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem forward_returned_store (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (out : Output Value Ram Reg.count)
    (h : program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = .returned out) :
    out.store = forwardRam code args mem := by
  rw [subBytes_body_eval] at h
  runtime_returned_store h

open AesGcm.Proofs.Machine.LIR
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem forwardRam_preserves_saved (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (ha : Readable mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) 160)
    (hap : ((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
      ((args[4]).get 64).toNat + 160 ≤ ((args[7]).get 64).toNat)
    (j : Fin 7) :
    memLoad (forwardRam code args mem) ((args[4]).get 64 + BitVec.ofNat 64 (104 + 8 * j.val)) 64 =
      memLoad mem ((args[4]).get 64 + BitVec.ofNat 64 (104 + 8 * j.val)) 64 := by
  generalize hbase : (args[7]).get 64 = a at *
  generalize hstack : (args[4]).get 64 = sp at *
  rcases j with ⟨j, hj⟩
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;> subst j <;>
    (unfold forwardRam
     extract_lets
     simp only [Nat.reduceMul, Nat.reduceAdd]
     runtime_local_memory_norm)

private theorem state_words_explicit (a : BitVec 64) (mem : Ram) :
    (fun p : Fin 8 ↦ memLoad mem (a + BitVec.ofNat 64 (8 * p.val)) 64) =
    (fun p : Fin 8 ↦ match p.val with
      | 0 => memLoad mem a 64
      | 1 => memLoad mem (a + 8) 64
      | 2 => memLoad mem (a + 16) 64
      | 3 => memLoad mem (a + 24) 64
      | 4 => memLoad mem (a + 32) 64
      | 5 => memLoad mem (a + 40) 64
      | 6 => memLoad mem (a + 48) 64
      | _ => memLoad mem (a + 56) 64) := by
  funext ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;> simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem forwardRam_words (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (ha : Readable mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) 160)
    (hap : ((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
      ((args[4]).get 64).toNat + 160 ≤ ((args[7]).get 64).toNat)
    (p : Fin 8) :
    memLoad (forwardRam code args mem) ((args[7]).get 64 + BitVec.ofNat 64 (8 * p.val)) 64 =
      subBytes (fun q ↦ memLoad mem ((args[7]).get 64 + BitVec.ofNat 64 (8 * q.val)) 64) p := by
  rw [← SboxSSA.forward_eq]
  generalize hbase : (args[7]).get 64 = a at *
  generalize hstack : (args[4]).get 64 = sp at *
  rw [state_words_explicit]
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (unfold forwardRam
     extract_lets
     simp only [Nat.reduceMul]
     runtime_local_memory_norm
     all_goals unfold SboxSSA.forward
     all_goals runtime_local_memory_norm
     all_goals simp (config := { zetaHave := true, maxSteps := 1000000 }) only [BitVec.ofNat_eq_ofNat]
     all_goals rfl)

private theorem forward_returned_words (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (out : Output Value Ram Reg.count)
    (hrun : program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = .returned out)
    (ha : Readable mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) 160)
    (hap : ((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
      ((args[4]).get 64).toNat + 160 ≤ ((args[7]).get 64).toNat)
    (p : Fin 8) :
    memLoad out.store ((args[7]).get 64 + BitVec.ofNat 64 (8 * p.val)) 64 =
      subBytes (fun q ↦ memLoad mem ((args[7]).get 64 + BitVec.ofNat 64 (8 * q.val)) 64) p := by
  rw [forward_returned_store code args mem out hrun]
  exact forwardRam_words code args mem ha hs hap p

private theorem forward_returned_preserves_saved (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (out : Output Value Ram Reg.count)
    (hrun : program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = .returned out)
    (ha : Readable mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) 160)
    (hap : ((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
      ((args[4]).get 64).toNat + 160 ≤ ((args[7]).get 64).toNat)
    (j : Fin 7) :
    memLoad out.store ((args[4]).get 64 + BitVec.ofNat 64 (104 + 8 * j.val)) 64 =
      memLoad mem ((args[4]).get 64 + BitVec.ofNat 64 (104 + 8 * j.val)) 64 := by
  rw [forward_returned_store code args mem out hrun]
  exact forwardRam_preserves_saved code args mem ha hs hap j

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem forwardRam_frame (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (ha : Readable mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) 160) :
    RamWriteFrame mem (forwardRam code args mem)
      [⟨((args[4]).get 64).toNat, 104⟩, ⟨((args[7]).get 64).toNat, 64⟩] := by
  generalize hbase : (args[7]).get 64 = a at *
  generalize hstack : (args[4]).get 64 = sp at *
  have haLow := ha.low
  have hsLow := hs.low
  unfold forwardRam
  extract_lets
  runtime_local_frame


runtime_output_def AesGcm.Proofs.Machine.AES64.forwardOutput from AesGcm.Proofs.Machine.AES64.subBytes_body_eval
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift AesGcm.Proofs.Machine.LIR
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem forward_returned_output (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (out : Output Value Ram Reg.count)
    (h : program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = .returned out) :
    out = forwardOutput code args mem := by
  rw [subBytes_body_eval] at h
  runtime_returned_store h
set_option maxRecDepth 8192 in
private theorem forwardOutput_registers (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    (forwardOutput code args mem).values[4] = ⟨64, (args[4]).get 64 + 160⟩ ∧
    (forwardOutput code args mem).values[22] = args[22] := by
  simp only [forwardOutput]
  exact ⟨rfl, rfl⟩
set_option maxRecDepth 8192 in
private theorem forwardOutput_tag (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    (forwardOutput code args mem).tag =
      some ⟨64, memLoad (forwardRam code args mem) ((args[4]).get 64 + 152) 64⟩ := by
  simp only [forwardOutput, forwardRam]
set_option maxRecDepth 8192 in
private theorem forwardOutput_saved (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (j : Fin 6) :
    (forwardOutput code args mem).values[
      (match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) =
      ⟨64, memLoad (forwardRam code args mem)
        ((args[4]).get 64 + BitVec.ofNat 64 (104 + 8 * j.val)) 64⟩ := by
  rcases j with ⟨j, hj⟩
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases h with h | h | h | h | h | h <;> subst j <;>
    (simp only [forwardOutput, forwardRam, Nat.reduceMul, Nat.reduceAdd]; rfl)
set_option maxRecDepth 8192 in
private theorem forwardOutput_typed (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (h7 : (args[7]).width = 64) :
    Runtime.GPRsTyped (forwardOutput code args mem).values := by
  intro ⟨r, hr⟩
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
      r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst r <;> first | exact h7 | rfl


open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift AesGcm.Proofs.Machine.LIR X86Proofs.Refine
set_option maxRecDepth 8192 in
private theorem body_result (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) (out : Output Value Ram Reg.count)
    (hrun : program.runBlock (dialect code)
      ⟨.l100eed, args, mem⟩ = .returned out)
    (ha : Readable mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) (160))
    (hap : ((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
      ((args[4]).get 64).toNat + (160) ≤ ((args[7]).get 64).toNat)
    (h7 : (args[7]).width = 64) :
    out.tag = some ⟨64, memLoad mem
      ((args[4]).get 64 + (152)) 64⟩ ∧
    out.values[4] = ⟨64, (args[4]).get 64 + (160)⟩ ∧
    out.values[22] = args[22] ∧
    out.values[39] = args[39] ∧ out.values[50] = args[50] ∧ out.values[51] = args[51] ∧
    (∀ j : Fin 6, out.values[
      (match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) =
      ⟨64, memLoad mem ((args[4]).get 64 +
        BitVec.ofNat 64 ((104) + 8 * j.val)) 64⟩) ∧
    Runtime.GPRsTyped out.values ∧
    RamWriteFrame mem out.store
      [⟨((args[4]).get 64).toNat, 104⟩,
       ⟨((args[7]).get 64).toNat, 64⟩] ∧
    (∀ p : Fin 8, memLoad out.store ((args[7]).get 64 + BitVec.ofNat 64 (8 * p.val)) 64 =
      (subBytes)
        (fun q ↦ memLoad mem ((args[7]).get 64 + BitVec.ofNat 64 (8 * q.val)) 64) p) := by
  have hout := forward_returned_output code args mem out hrun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout, forwardOutput_tag]
    have hret := forwardRam_preserves_saved code args mem ha hs hap (6 : Fin 7)
    exact congrArg (fun x => some (Value.mk 64 x)) hret
  · rw [hout]
    exact (forwardOutput_registers code args mem).1
  · rw [hout]
    exact (forwardOutput_registers code args mem).2
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · intro j
    rw [hout, forwardOutput_saved]
    exact congrArg (Value.mk 64)
      (forwardRam_preserves_saved code args mem ha hs hap ⟨j.val, by have := j.isLt; omega⟩)
  · rw [hout]
    exact forwardOutput_typed code args mem h7
  · rw [forward_returned_store code args mem out hrun]
    exact forwardRam_frame code args mem ha hs
  · exact forward_returned_words code args mem out hrun ha hs hap


open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open X86Proofs.Refine AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.Instructions AesGcm.Proofs.Machine.LIR
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem forward_body_returns (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hc : ∀ x ∈ fnCode, x ∈ code)
    (hstack : Writable code mem ((args[4]).get 64) 104)
    (hread : Readable mem ((args[4]).get 64) 160)
    (hstate : Writable code mem ((args[7]).get 64) 64)
    (hap : ((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
      ((args[4]).get 64).toNat + 160 ≤ ((args[7]).get 64).toNat)
    (hret : (memLoad mem ((args[4]).get 64 + 152) 64).toNat < 2^32) :
    ∃ out : Output Value Ram Reg.count,
      program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = .returned out := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24⟩ :=
    subBytes_storeGuards code mem ((args[4]).get 64) ((args[7]).get 64) hc hstack hstate
  have s0 := wordLoad_guard hread 0 (by decide +kernel)
  have s1 := wordLoad_guard hread 8 (by decide +kernel)
  have s2 := wordLoad_guard hread 16 (by decide +kernel)
  have s3 := wordLoad_guard hread 24 (by decide +kernel)
  have s4 := wordLoad_guard hread 32 (by decide +kernel)
  have s5 := wordLoad_guard hread 40 (by decide +kernel)
  have s6 := wordLoad_guard hread 48 (by decide +kernel)
  have s7 := wordLoad_guard hread 56 (by decide +kernel)
  have s8 := wordLoad_guard hread 64 (by decide +kernel)
  have s9 := wordLoad_guard hread 72 (by decide +kernel)
  have s10 := wordLoad_guard hread 80 (by decide +kernel)
  have s11 := wordLoad_guard hread 88 (by decide +kernel)
  have s12 := wordLoad_guard hread 96 (by decide +kernel)
  have s13 := wordLoad_guard hread 104 (by decide +kernel)
  have s14 := wordLoad_guard hread 112 (by decide +kernel)
  have s15 := wordLoad_guard hread 120 (by decide +kernel)
  have s16 := wordLoad_guard hread 128 (by decide +kernel)
  have s17 := wordLoad_guard hread 136 (by decide +kernel)
  have s18 := wordLoad_guard hread 144 (by decide +kernel)
  have s19 := wordLoad_guard hread 152 (by decide +kernel)
  have d0 := wordLoad_guard hstate.readable 0 (by decide +kernel)
  have d1 := wordLoad_guard hstate.readable 8 (by decide +kernel)
  have d2 := wordLoad_guard hstate.readable 16 (by decide +kernel)
  have d3 := wordLoad_guard hstate.readable 24 (by decide +kernel)
  have d4 := wordLoad_guard hstate.readable 32 (by decide +kernel)
  have d5 := wordLoad_guard hstate.readable 40 (by decide +kernel)
  have d6 := wordLoad_guard hstate.readable 48 (by decide +kernel)
  have d7 := wordLoad_guard hstate.readable 56 (by decide +kernel)
  have hretFinal :
      (memLoad (forwardRam code args mem) ((args[4]).get 64 + 152) 64).toNat < 2^32 := by
    have he := forwardRam_preserves_saved code args mem hstate.readable hread hap (6 : Fin 7)
    change memLoad (forwardRam code args mem) ((args[4]).get 64 + 152) 64 = _ at he
    rw [he]
    exact hret
  generalize hbase : (args[7]).get 64 = a at hstate hap
  generalize hstackBase : (args[4]).get 64 = sp at hread hap hret
  have ha := hstate.readable
  have haLow := ha.low
  have hsLow := hread.low
  simp only [BitVec.add_zero] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 d0 d1 d2 d3 d4 d5 d6 d7
  runtime_return_exists subBytes_body_eval


open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open AesGcm.Proofs.Machine.LIR AesGcm.Proofs.Machine.Runtime X86Proofs.Refine

private theorem sbox_entry_facts (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (fr : Activation)
    (hentry : Atom.All code args mem (Fn100e90.frameInfo.entryAtoms fr)) :
    args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧
    args[1] = ⟨64, fr.rcx⟩ ∧ args[2] = ⟨64, fr.rdx⟩ ∧
    args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧
    args[8] = ⟨64, fr.r8⟩ ∧ args[9] = ⟨64, fr.r9⟩ ∧
    args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧
    Writable code mem (fr.rsp - BitVec.ofNat 64 (288))
      (288) ∧
    fr.low.toNat + (288) ≤ fr.rsp.toNat ∧
    fr.rsp.toNat % 16 = 8 ∧ True := by
  simp only [↓reduceIte, Fn100e90.frameInfo,
      FrameInfo.entryAtoms, FrameInfo.frameAtoms, FrameInfo.entryFrame, FrameInfo.entryRegs,
      FrameInfo.stackAtoms, FrameInfo.window, FrameInfo.callSlotAtoms, Activation.below,
      Activation.entryReg, Activation.entryValue, Option.getD, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, List.append_nil, Atom.All, Atom.Holds, Atom.gpr, Atom.Holds,
      Nat.reduceEqDiff, ↓reduceIte] at hentry
  rcases hentry with ⟨e4, e22, e1, e2, e3, e5, e6, e7, e8, e9, e12, e13, e14, e15,
    e39, e50, e51, er, ert, erl, es, erm, ea, _⟩
  exact ⟨e4, e22, e1, e2, e3, e5, e6, e7, e8, e9, e12, e13, e14, e15,
    e39, e50, e51, er, ert, erl, es, erm, ea, trivial⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem sbox_callContract (code : CodeMap)
    (hc : ∀ x ∈ fnCode, x ∈ code)
    (bodyExists : ∀ (args : Values Value Reg.count) (mem : Ram),
      Writable code mem ((args[7]).get 64) 64 →
      Writable code mem ((args[4]).get 64) (104) →
      Readable mem ((args[4]).get 64) (160) →
      (((args[7]).get 64).toNat + 64 ≤ ((args[4]).get 64).toNat ∨
        ((args[4]).get 64).toNat + (160) ≤ ((args[7]).get 64).toNat) →
      (memLoad mem ((args[4]).get 64 + (152)) 64).toNat < 2^32 →
      ∃ out, program.runBlock (dialect code)
        ⟨.l100eed, args, mem⟩ = .returned out) :
    CallContract lifted code (.l100e90)
      (Fn100e90.frameInfo)
      (fun fr => [span fr.rdi 64])
      (fun fr mem => fr.rsi = 8 ∧ Writable code mem fr.rdi 64 ∧
        (callStack fr).Disjoint (span fr.rdi 64))
      (fun fr mem => ∀ p : Fin 8,
        memLoad mem (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 =
          (subBytes)
            (fun q => memLoad fr.original (fr.rdi + BitVec.ofNat 64 (8 * q.val)) 64) p) := by
  intro fr loc hlabel hstore hentry htyped hpre
  rcases loc with ⟨l, args, mem⟩
  change l = _ at hlabel
  change mem = _ at hstore
  subst l
  change Values Value Reg.count at args
  rcases hpre with ⟨hlen, hstate, hdis⟩
  have hflat := sbox_entry_facts code args mem fr hentry
  rcases hflat with ⟨h4, h22, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15, h39, h50, h51,
    hretRead, hretWord, hretLow, hstack, hroom, _, _⟩
  have hrsp : (args[4]).get 64 = fr.rsp := by rw [h4]; rfl
  have hrdi : (args[7]).get 64 = fr.rdi := by rw [h7]; rfl
  have hrsi : (args[6]).get 64 = 8 := by rw [h6]; exact hlen
  have hdepth : (152 : Nat) ≤ (288) := by
    decide
  have halloc : (104 : Nat) ≤ (152) := by
    decide
  have hroom48 : fr.low.toNat + 48 ≤ fr.rsp.toNat := by
    have : 48 ≤ (288 : Nat) := by decide
    omega
  obtain ⟨body, hreach, b4, b5, b6, b7, b22, b39, b50, b51⟩ :=
    entry_reaches code args mem hc hrsi (by simpa only [hrsp] using hstack)
  have hbsp : (body[4]).get 64 = fr.rsp - BitVec.ofNat 64 (152) := by
    rw [b4, hrsp]
    rfl
  have hbdi : (body[7]).get 64 = fr.rdi := by rw [b7, hrdi]
  have hb7 : (body[7]).width = 64 := by rw [b7, h7]
  have hsavedState : Writable code (sboxSavedMemory args mem) fr.rdi 64 :=
    saved_writable hstate
  obtain ⟨hbodyWrite, hbodyRead, hbodyApart, hbodyIn⟩ :=
    bodyFrame_regions (saved_writable hstack) (saved_readable hretRead) hroom halloc hdepth hdis
  have hbodySize : (152 : Nat) + 8 =
      (160) := by rfl
  rw [hbodySize] at hbodyRead hbodyApart
  have hretAddress : (body[4]).get 64 + (152) = fr.rsp := by
    rw [hbsp]
    bv_omega
  have hsavedRet : memLoad (sboxSavedMemory args mem) ((body[4]).get 64 +
      (152)) 64 = fr.ret := by
    rw [hretAddress, ← hrsp, saved_return, hrsp, hretWord]
  have hap : ((body[7]).get 64).toNat + 64 ≤ ((body[4]).get 64).toNat ∨
      ((body[4]).get 64).toNat + (160) ≤ ((body[7]).get 64).toNat := by
    rw [hbdi, hbsp]
    exact hbodyApart.symm
  obtain ⟨out, hrun⟩ := bodyExists body (sboxSavedMemory args mem)
    (by simpa only [hbdi] using hsavedState)
    (by simpa only [hbsp] using hbodyWrite)
    (by simpa only [hbsp] using hbodyRead) hap (by rw [hsavedRet]; exact hretLow)
  obtain ⟨otag, o4, o22, o39, o50, o51, osaved, otyped, oframe, owords⟩ :=
    body_result code body (sboxSavedMemory args mem) out hrun
      (by simpa only [hbdi] using hsavedState.readable)
      (by simpa only [hbsp] using hbodyRead) hap hb7
  have hreturned : (program.sem (dialect code)).Exec
      ⟨⟨.l100eed, body, sboxSavedMemory args mem⟩, []⟩ out := by
    apply Semantics.Exec.ret
    change program.step (dialect code) _ = .done out
    rw [Program.step, hrun]
    rfl
  have o4' : out.values[4] = ⟨64, fr.rsp + 8⟩ := by
    rw [o4, hbsp]
    congr 1
    bv_omega
  have osaved' (j : Fin 6) : out.values[
      (match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) =
        args[(match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) := by
    rw [osaved j, hbsp]
    have ha : fr.rsp - BitVec.ofNat 64 (152) +
        BitVec.ofNat 64 ((104) + 8 * j.val) =
        fr.rsp - BitVec.ofNat 64 (48 - 8 * j.val) := by
      have hj := j.isLt
      bv_omega
    let rj : Nat := match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5
    have hrj : rj < 16 := by dsimp only [rj]; split <;> decide
    have hslot : (rj, 48 - 8 * j.val) ∈ [(3, 48), (12, 40), (13, 32), (14, 24), (15, 16), (5, 8)] := by
      rcases j with ⟨j, hj⟩
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [rj, Nat.reduceMul, Nat.reduceSub] <;> decide
    have hload := saved_word args mem ⟨rj, by change rj < 53; omega⟩ (48 - 8 * j.val) hslot
    rw [ha, ← hrsp, hload]
    exact (htyped.value ⟨rj, hrj⟩).symm
  have savedFrame := saved_frame fr args mem hrsp hroom48
  have written : RamWriteFrame mem out.store [fr.region, span fr.rdi 64] := by
    have hfirst : RamWriteFrame mem (sboxSavedMemory args mem) [fr.region, span fr.rdi 64] := by
      apply (RamWriteFrame.refl mem [fr.region, span fr.rdi 64]).trans savedFrame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
    apply hfirst.trans oframe
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region, by simp, ?_⟩
      rw [hbsp]
      exact ⟨hbodyIn.1, hbodyIn.2.1⟩
    · rw [hbdi]
      exact ⟨span fr.rdi 64, by simp, Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨out, Program.Exec.of_sem (hreach.exec hreturned), ?_, ?_, otyped, ?_, ?_⟩
  · rw [otag, hsavedRet]
  · have ob3 := osaved' 0
    have ob12 := osaved' 1
    have ob13 := osaved' 2
    have ob14 := osaved' 3
    have ob15 := osaved' 4
    have ob5 := osaved' 5
    simp only [Fn100e90.frameInfo,
        FrameInfo.doneAtoms, List.map_cons, List.map_nil, Activation.entryReg, Activation.entryValue, Atom.gpr]
    all_goals exact ⟨o4', o22.trans (b22.trans h22), ob3.trans h3, ob5.trans h5,
      ob12.trans h12, ob13.trans h13, ob14.trans h14, ob15.trans h15,
      o39.trans (b39.trans h39), o50.trans (b50.trans h50), o51.trans (b51.trans h51), trivial⟩
  · rw [hstore] at written
    exact written
  · intro p
    have hw := owords p
    rw [hbdi] at hw
    rw [hw]
    apply congrArg (fun x => (subBytes) x p)
    funext q
    rw [saved_state fr args mem hrsp hroom48 hstate.readable hdis q, hstore]


open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open AesGcm.Proofs.Machine.LIR AesGcm.Proofs.Machine.Runtime X86Proofs.Refine

theorem subBytes_callContract (code : CodeMap) (hc : ∀ x ∈ fnCode, x ∈ code)
    :
    CallContract lifted code .l100e90 Fn100e90.frameInfo
      (fun fr => [span fr.rdi 64])
      (fun fr mem => fr.rsi = 8 ∧ Writable code mem fr.rdi 64 ∧
        (callStack fr).Disjoint (span fr.rdi 64))
      (fun fr mem => ∀ p : Fin 8,
        memLoad mem (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 =
          subBytes (fun q => memLoad fr.original (fr.rdi + BitVec.ofNat 64 (8 * q.val)) 64) p) :=
by
  apply sbox_callContract code hc
  intro args mem hstate hstack hread hap hret
  exact forward_body_returns code args mem hc hstack hread hstate hap hret


end AesGcm.Proofs.Machine.AES64
