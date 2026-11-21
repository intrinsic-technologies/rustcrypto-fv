import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Labels
import AesGcm.Proofs.Copied.X86Proofs.CFG.EvalAttr
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Footprints

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

@[cfg_block] def b_l100000_8 : Block Op Label signature Reg.count 363 :=
  .letOp (n := 363) (.exec 0x100261 (StorePre 0x100261 4 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x100261 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100261 4 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[361, 7]
    (.letOp (n := 364) (.out 0x100265 (movR32R32Effect 0x100265 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[209]
    (.letOp (n := 365) (.exec 0x100265 (fun s => s.RIP = 0x100265) (movR32R32Effect 0x100265 3 0 11) (Reg.operands [.gpr 11] [])) #v[209]
    (.letOp (n := 366) (.out 0x100268 (rolR16Effect 0x100268 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 367) (.exec 0x100268 (fun s => s.RIP = 0x100268) (rolR16Effect 0x100268 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[364]
    (.letOp (n := 368) (.out 0x10026c (andEaxImm32Effect 0x10026c 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[366]
    (.letOp (n := 369) (.exec 0x10026c (fun s => s.RIP = 0x10026c) (andEaxImm32Effect 0x10026c 0x3333) (Reg.operands [.gpr 0] [])) #v[366]
    (.letOp (n := 370) (.out 0x100271 (rolR16Effect 0x100271 5 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[209]
    (.letOp (n := 371) (.exec 0x100271 (fun s => s.RIP = 0x100271) (rolR16Effect 0x100271 5 11 10) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[209]
    (.letOp (n := 372) (.out 0x100276 (andR32Imm32Effect 0x100276 7 11 0xffffcccc) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[370]
    (.letOp (n := 373) (.exec 0x100276 (fun s => s.RIP = 0x100276) (andR32Imm32Effect 0x100276 7 11 0xffffcccc) (Reg.operands [.gpr 11] [])) #v[370]
    (.letOp (n := 374) (.out 0x10027d (orR32R32Effect 0x10027d 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[372, 368]
    (.letOp (n := 375) (.exec 0x10027d (fun s => s.RIP = 0x10027d) (orR32R32Effect 0x10027d 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[372, 368]
    (.letOp (n := 376) (.out 0x100280 (movR32R32Effect 0x100280 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[338]
    (.letOp (n := 377) (.exec 0x100280 (fun s => s.RIP = 0x100280) (movR32R32Effect 0x100280 2 0 2) (Reg.operands [.gpr 2] [])) #v[338]
    (.letOp (n := 378) (.out 0x100282 (xorR32R32Effect 0x100282 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[376, 191]
    (.letOp (n := 379) (.exec 0x100282 (fun s => s.RIP = 0x100282) (xorR32R32Effect 0x100282 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[376, 191]
    (.letOp (n := 380) (.out 0x100284 (xorR32R32Effect 0x100284 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[378, 374]
    (.letOp (n := 381) (.exec 0x100284 (fun s => s.RIP = 0x100284) (xorR32R32Effect 0x100284 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[378, 374]
    (.letOp (n := 382) (.exec 0x100287 (StorePre 0x100287 4 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x100287 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100287 4 0 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[380, 7]
    (.letOp (n := 383) (.out 0x10028b (addR64Imm8Effect 0x10028b 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 384) (.exec 0x10028b (fun s => s.RIP = 0x10028b) (addR64Imm8Effect 0x10028b 4 0x10) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 385) (.out 0x10028f (popR64Effect 0x10028f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[383]
    (.letOp (n := 386) (.out 0x10028f (popR64Effect 0x10028f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[383]
    (.letOp (n := 387) (.exec 0x10028f (PopPre 0x10028f) (popR64Effect 0x10028f 1 3) (Reg.operands [.gpr 4] [])) #v[383]
    (.letOp (n := 388) (.out 0x100290 (popR64Effect 0x100290 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[386]
    (.letOp (n := 389) (.out 0x100290 (popR64Effect 0x100290 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[386]
    (.letOp (n := 390) (.exec 0x100290 (PopPre 0x100290) (popR64Effect 0x100290 2 12) (Reg.operands [.gpr 4] [])) #v[386]
    (.letOp (n := 391) (.out 0x100292 (popR64Effect 0x100292 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[389]
    (.letOp (n := 392) (.out 0x100292 (popR64Effect 0x100292 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[389]
    (.letOp (n := 393) (.exec 0x100292 (PopPre 0x100292) (popR64Effect 0x100292 2 13) (Reg.operands [.gpr 4] [])) #v[389]
    (.letOp (n := 394) (.out 0x100294 (popR64Effect 0x100294 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[392]
    (.letOp (n := 395) (.out 0x100294 (popR64Effect 0x100294 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[392]
    (.letOp (n := 396) (.exec 0x100294 (PopPre 0x100294) (popR64Effect 0x100294 2 14) (Reg.operands [.gpr 4] [])) #v[392]
    (.letOp (n := 397) (.out 0x100296 (popR64Effect 0x100296 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[395]
    (.letOp (n := 398) (.out 0x100296 (popR64Effect 0x100296 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[395]
    (.letOp (n := 399) (.exec 0x100296 (PopPre 0x100296) (popR64Effect 0x100296 2 15) (Reg.operands [.gpr 4] [])) #v[395]
    (.letOp (n := 400) (.out 0x100298 (popR64Effect 0x100298 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[398]
    (.letOp (n := 401) (.out 0x100298 (popR64Effect 0x100298 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[398]
    (.letOp (n := 402) (.exec 0x100298 (PopPre 0x100298) (popR64Effect 0x100298 1 5) (Reg.operands [.gpr 4] [])) #v[398]
    (.letOp (n := 403) (.out 0x100299 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[401]
    (.letOp (n := 404) (.out 0x100299 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[401]
    (.letOp (n := 405) (.exec 0x100299 (RetPre 0x100299) (retEffect) (Reg.operands [.gpr 4] [])) #v[401]
    (.terminate (.ret (RegMap.args [(0, 380), (1, 355), (2, 338), (3, 385), (4, 404), (5, 400), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 394), (15, 397), (22, 22), (39, 39), (50, 50), (51, 51)] 406) (some ⟨403, by decide⟩)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l100000_8 : List UInt8 :=
  [0x66, 0x89, 0x47, 0x0C, 0x44, 0x89, 0xD8, 0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00,
    0x66, 0x41, 0xC1, 0xC3, 0x0A, 0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x09, 0xC3, 0x89,
    0xD0, 0x31, 0xE8, 0x44, 0x31, 0xD8, 0x66, 0x89, 0x47, 0x0E, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41,
    0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l100000_8 : ∀ x ∈ codeRange 0x100261 bytes_l100000_8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x261 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100000_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x10021d (rolR16Effect 0x10021d 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[320]
    (.letOp (n := 325) (.exec 0x10021d (fun s => s.RIP = 0x10021d) (rolR16Effect 0x10021d 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[320]
    (.letOp (n := 326) (.out 0x100221 (andR32Imm32Effect 0x100221 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[324]
    (.letOp (n := 327) (.exec 0x100221 (fun s => s.RIP = 0x100221) (andR32Imm32Effect 0x100221 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[324]
    (.letOp (n := 328) (.out 0x100227 (orR32R32Effect 0x100227 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[326, 318]
    (.letOp (n := 329) (.exec 0x100227 (fun s => s.RIP = 0x100227) (orR32R32Effect 0x100227 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[326, 318]
    (.letOp (n := 330) (.out 0x100229 (movR32R32Effect 0x100229 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 331) (.exec 0x100229 (fun s => s.RIP = 0x100229) (movR32R32Effect 0x100229 3 0 8) (Reg.operands [.gpr 8] [])) #v[293]
    (.letOp (n := 332) (.out 0x10022c (xorR32R32Effect 0x10022c 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[330, 161]
    (.letOp (n := 333) (.exec 0x10022c (fun s => s.RIP = 0x10022c) (xorR32R32Effect 0x10022c 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[330, 161]
    (.letOp (n := 334) (.out 0x10022f (movR32M32LowEffect 0x10022f 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 335) (.exec 0x10022f (LoadPre 0x10022f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10022f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10022f 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 336) (.out 0x100233 (movR32M32Effect 0x100233 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 337) (.exec 0x100233 (LoadPre 0x100233 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100233 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100233 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 338) (.out 0x100238 (xorR32R32Effect 0x100238 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[334, 336]
    (.letOp (n := 339) (.exec 0x100238 (fun s => s.RIP = 0x100238) (xorR32R32Effect 0x100238 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[334, 336]
    (.letOp (n := 340) (.out 0x10023b (xorR32R32Effect 0x10023b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[332, 328]
    (.letOp (n := 341) (.exec 0x10023b (fun s => s.RIP = 0x10023b) (xorR32R32Effect 0x10023b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[332, 328]
    (.letOp (n := 342) (.exec 0x10023d (StorePre 0x10023d 4 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10023d + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10023d 4 0 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[340, 7]
    (.letOp (n := 343) (.out 0x100241 (movR32R32Effect 0x100241 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[338]
    (.letOp (n := 344) (.exec 0x100241 (fun s => s.RIP = 0x100241) (movR32R32Effect 0x100241 2 0 2) (Reg.operands [.gpr 2] [])) #v[338]
    (.letOp (n := 345) (.out 0x100243 (rolR16Effect 0x100243 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[343]
    (.letOp (n := 346) (.exec 0x100243 (fun s => s.RIP = 0x100243) (rolR16Effect 0x100243 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[343]
    (.letOp (n := 347) (.out 0x100247 (andEaxImm32Effect 0x100247 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[345]
    (.letOp (n := 348) (.exec 0x100247 (fun s => s.RIP = 0x100247) (andEaxImm32Effect 0x100247 0x3333) (Reg.operands [.gpr 0] [])) #v[345]
    (.letOp (n := 349) (.out 0x10024c (movR32R32Effect 0x10024c 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[338]
    (.letOp (n := 350) (.exec 0x10024c (fun s => s.RIP = 0x10024c) (movR32R32Effect 0x10024c 2 1 2) (Reg.operands [.gpr 2] [])) #v[338]
    (.letOp (n := 351) (.out 0x10024e (rolR16Effect 0x10024e 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[349]
    (.letOp (n := 352) (.exec 0x10024e (fun s => s.RIP = 0x10024e) (rolR16Effect 0x10024e 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[349]
    (.letOp (n := 353) (.out 0x100252 (andR32Imm32Effect 0x100252 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[351]
    (.letOp (n := 354) (.exec 0x100252 (fun s => s.RIP = 0x100252) (andR32Imm32Effect 0x100252 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[351]
    (.letOp (n := 355) (.out 0x100258 (orR32R32Effect 0x100258 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[353, 347]
    (.letOp (n := 356) (.exec 0x100258 (fun s => s.RIP = 0x100258) (orR32R32Effect 0x100258 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[353, 347]
    (.letOp (n := 357) (.out 0x10025a (movR32R32Effect 0x10025a 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[322]
    (.letOp (n := 358) (.exec 0x10025a (fun s => s.RIP = 0x10025a) (movR32R32Effect 0x10025a 2 0 6) (Reg.operands [.gpr 6] [])) #v[322]
    (.letOp (n := 359) (.out 0x10025c (xorR32R32Effect 0x10025c 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[357, 336]
    (.letOp (n := 360) (.exec 0x10025c (fun s => s.RIP = 0x10025c) (xorR32R32Effect 0x10025c 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[357, 336]
    (.letOp (n := 361) (.out 0x10025f (xorR32R32Effect 0x10025f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[359, 355]
    (.letOp (n := 362) (.exec 0x10025f (fun s => s.RIP = 0x10025f) (xorR32R32Effect 0x10025f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[359, 355]
    (b_l100000_8)))))))))))))))))))))))))))))))))))))))

def bytes_l100000_7 : List UInt8 :=
  [0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC1, 0x44, 0x89, 0xC0, 0x44,
    0x31, 0xF0, 0x8B, 0x54, 0x24, 0x0C, 0x44, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x31, 0xC2, 0x31, 0xC8,
    0x66, 0x89, 0x47, 0x0A, 0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x89,
    0xD1, 0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC1, 0x89, 0xF0, 0x44,
    0x31, 0xC0, 0x31, 0xC8] ++ bytes_l100000_8

theorem code_l100000_7 : ∀ x ∈ codeRange 0x10021d bytes_l100000_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21d 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_8

@[cfg_block] def b_l100000_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x1001da (movR32R32Effect 0x1001da 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[280]
    (.letOp (n := 287) (.exec 0x1001da (fun s => s.RIP = 0x1001da) (movR32R32Effect 0x1001da 2 0 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 288) (.out 0x1001dc (rolR16Effect 0x1001dc 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[286]
    (.letOp (n := 289) (.exec 0x1001dc (fun s => s.RIP = 0x1001dc) (rolR16Effect 0x1001dc 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[286]
    (.letOp (n := 290) (.exec 0x1001e0 (StorePre 0x1001e0 5 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x1001e0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1001e0 5 8 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[284, 7]
    (.letOp (n := 291) (.out 0x1001e5 (movR32R32Effect 0x1001e5 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[280]
    (.letOp (n := 292) (.exec 0x1001e5 (fun s => s.RIP = 0x1001e5) (movR32R32Effect 0x1001e5 2 1 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 293) (.out 0x1001e7 (movR32R32Effect 0x1001e7 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[280]
    (.letOp (n := 294) (.exec 0x1001e7 (fun s => s.RIP = 0x1001e7) (movR32R32Effect 0x1001e7 3 8 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 295) (.out 0x1001ea (rolR16Effect 0x1001ea 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[291]
    (.letOp (n := 296) (.exec 0x1001ea (fun s => s.RIP = 0x1001ea) (rolR16Effect 0x1001ea 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[291]
    (.letOp (n := 297) (.out 0x1001ee (andEaxImm32Effect 0x1001ee 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[288]
    (.letOp (n := 298) (.exec 0x1001ee (fun s => s.RIP = 0x1001ee) (andEaxImm32Effect 0x1001ee 0x3333) (Reg.operands [.gpr 0] [])) #v[288]
    (.letOp (n := 299) (.out 0x1001f3 (andR32Imm32Effect 0x1001f3 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[295]
    (.letOp (n := 300) (.exec 0x1001f3 (fun s => s.RIP = 0x1001f3) (andR32Imm32Effect 0x1001f3 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[295]
    (.letOp (n := 301) (.out 0x1001f9 (orR32R32Effect 0x1001f9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[299, 297]
    (.letOp (n := 302) (.exec 0x1001f9 (fun s => s.RIP = 0x1001f9) (orR32R32Effect 0x1001f9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[299, 297]
    (.letOp (n := 303) (.out 0x1001fb (xorR32R32Effect 0x1001fb 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[257, 153]
    (.letOp (n := 304) (.exec 0x1001fb (fun s => s.RIP = 0x1001fb) (xorR32R32Effect 0x1001fb 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[257, 153]
    (.letOp (n := 305) (.out 0x1001fe (movR32M32LowEffect 0x1001fe 2 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 306) (.exec 0x1001fe (LoadPre 0x1001fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1001fe + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1001fe 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 307) (.out 0x100202 (xorR32R32Effect 0x100202 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[305, 161]
    (.letOp (n := 308) (.exec 0x100202 (fun s => s.RIP = 0x100202) (xorR32R32Effect 0x100202 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[305, 161]
    (.letOp (n := 309) (.out 0x100205 (xorR32R32Effect 0x100205 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[303, 209]
    (.letOp (n := 310) (.exec 0x100205 (fun s => s.RIP = 0x100205) (xorR32R32Effect 0x100205 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[303, 209]
    (.letOp (n := 311) (.out 0x100208 (xorR32R32Effect 0x100208 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[309, 301]
    (.letOp (n := 312) (.exec 0x100208 (fun s => s.RIP = 0x100208) (xorR32R32Effect 0x100208 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[309, 301]
    (.letOp (n := 313) (.exec 0x10020a (StorePre 0x10020a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10020a + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10020a 4 6 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[311, 7]
    (.letOp (n := 314) (.out 0x10020e (movR32R32Effect 0x10020e 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[307]
    (.letOp (n := 315) (.exec 0x10020e (fun s => s.RIP = 0x10020e) (movR32R32Effect 0x10020e 2 0 2) (Reg.operands [.gpr 2] [])) #v[307]
    (.letOp (n := 316) (.out 0x100210 (rolR16Effect 0x100210 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[314]
    (.letOp (n := 317) (.exec 0x100210 (fun s => s.RIP = 0x100210) (rolR16Effect 0x100210 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[314]
    (.letOp (n := 318) (.out 0x100214 (andEaxImm32Effect 0x100214 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[316]
    (.letOp (n := 319) (.exec 0x100214 (fun s => s.RIP = 0x100214) (andEaxImm32Effect 0x100214 0x3333) (Reg.operands [.gpr 0] [])) #v[316]
    (.letOp (n := 320) (.out 0x100219 (movR32R32Effect 0x100219 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[307]
    (.letOp (n := 321) (.exec 0x100219 (fun s => s.RIP = 0x100219) (movR32R32Effect 0x100219 2 1 2) (Reg.operands [.gpr 2] [])) #v[307]
    (.letOp (n := 322) (.out 0x10021b (movR32R32Effect 0x10021b 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[307]
    (.letOp (n := 323) (.exec 0x10021b (fun s => s.RIP = 0x10021b) (movR32R32Effect 0x10021b 2 6 2) (Reg.operands [.gpr 2] [])) #v[307]
    (b_l100000_7))))))))))))))))))))))))))))))))))))))

def bytes_l100000_6 : List UInt8 :=
  [0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x06, 0x66, 0x44, 0x89, 0x47, 0x06, 0x89, 0xD1, 0x41, 0x89, 0xD0,
    0x66, 0xC1, 0xC1, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09,
    0xC1, 0x44, 0x31, 0xFE, 0x8B, 0x54, 0x24, 0x04, 0x44, 0x31, 0xF2, 0x44, 0x31, 0xDE, 0x31, 0xCE,
    0x66, 0x89, 0x77, 0x08, 0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x89,
    0xD1, 0x89, 0xD6] ++ bytes_l100000_7

theorem code_l100000_6 : ∀ x ∈ codeRange 0x1001da bytes_l100000_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1da 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_7

@[cfg_block] def b_l100000_5 : Block Op Label signature Reg.count 247 :=
  .letOp (n := 247) (.out 0x100197 (movR32R32Effect 0x100197 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[238]
    (.letOp (n := 248) (.exec 0x100197 (fun s => s.RIP = 0x100197) (movR32R32Effect 0x100197 3 1 8) (Reg.operands [.gpr 8] [])) #v[238]
    (.letOp (n := 249) (.out 0x10019a (rolR16Effect 0x10019a 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[247]
    (.letOp (n := 250) (.exec 0x10019a (fun s => s.RIP = 0x10019a) (rolR16Effect 0x10019a 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 251) (.out 0x10019e (andR32Imm32Effect 0x10019e 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[249]
    (.letOp (n := 252) (.exec 0x10019e (fun s => s.RIP = 0x10019e) (andR32Imm32Effect 0x10019e 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[249]
    (.letOp (n := 253) (.out 0x1001a4 (orR32R32Effect 0x1001a4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[251, 245]
    (.letOp (n := 254) (.exec 0x1001a4 (fun s => s.RIP = 0x1001a4) (orR32R32Effect 0x1001a4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[251, 245]
    (.letOp (n := 255) (.out 0x1001a6 (xorR32R32Effect 0x1001a6 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[216, 121]
    (.letOp (n := 256) (.exec 0x1001a6 (fun s => s.RIP = 0x1001a6) (xorR32R32Effect 0x1001a6 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[216, 121]
    (.letOp (n := 257) (.out 0x1001a9 (xorR32R32Effect 0x1001a9 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[73, 135]
    (.letOp (n := 258) (.exec 0x1001a9 (fun s => s.RIP = 0x1001a9) (xorR32R32Effect 0x1001a9 3 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[73, 135]
    (.letOp (n := 259) (.out 0x1001ac (xorR32R32Effect 0x1001ac 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[255, 253]
    (.letOp (n := 260) (.exec 0x1001ac (fun s => s.RIP = 0x1001ac) (xorR32R32Effect 0x1001ac 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[255, 253]
    (.letOp (n := 261) (.exec 0x1001ae (StorePre 0x1001ae 4 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x1001ae + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1001ae 4 2 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[259, 7]
    (.letOp (n := 262) (.out 0x1001b2 (movR32R32Effect 0x1001b2 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[257]
    (.letOp (n := 263) (.exec 0x1001b2 (fun s => s.RIP = 0x1001b2) (movR32R32Effect 0x1001b2 2 0 6) (Reg.operands [.gpr 6] [])) #v[257]
    (.letOp (n := 264) (.out 0x1001b4 (rolR16Effect 0x1001b4 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[262]
    (.letOp (n := 265) (.exec 0x1001b4 (fun s => s.RIP = 0x1001b4) (rolR16Effect 0x1001b4 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[262]
    (.letOp (n := 266) (.out 0x1001b8 (andEaxImm32Effect 0x1001b8 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[264]
    (.letOp (n := 267) (.exec 0x1001b8 (fun s => s.RIP = 0x1001b8) (andEaxImm32Effect 0x1001b8 0x3333) (Reg.operands [.gpr 0] [])) #v[264]
    (.letOp (n := 268) (.out 0x1001bd (movR32R32Effect 0x1001bd 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[257]
    (.letOp (n := 269) (.exec 0x1001bd (fun s => s.RIP = 0x1001bd) (movR32R32Effect 0x1001bd 2 1 6) (Reg.operands [.gpr 6] [])) #v[257]
    (.letOp (n := 270) (.out 0x1001bf (rolR16Effect 0x1001bf 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[268]
    (.letOp (n := 271) (.exec 0x1001bf (fun s => s.RIP = 0x1001bf) (rolR16Effect 0x1001bf 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[268]
    (.letOp (n := 272) (.out 0x1001c3 (andR32Imm32Effect 0x1001c3 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[270]
    (.letOp (n := 273) (.exec 0x1001c3 (fun s => s.RIP = 0x1001c3) (andR32Imm32Effect 0x1001c3 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[270]
    (.letOp (n := 274) (.out 0x1001c9 (orR32R32Effect 0x1001c9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[272, 266]
    (.letOp (n := 275) (.exec 0x1001c9 (fun s => s.RIP = 0x1001c9) (orR32R32Effect 0x1001c9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[272, 266]
    (.letOp (n := 276) (.out 0x1001cb (xorR32R32Effect 0x1001cb 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[238, 135]
    (.letOp (n := 277) (.exec 0x1001cb (fun s => s.RIP = 0x1001cb) (xorR32R32Effect 0x1001cb 3 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[238, 135]
    (.letOp (n := 278) (.out 0x1001ce (movR32M32LowEffect 0x1001ce 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 279) (.exec 0x1001ce (LoadPre 0x1001ce (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1001ce + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1001ce 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 280) (.out 0x1001d1 (xorR32R32Effect 0x1001d1 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[278, 153]
    (.letOp (n := 281) (.exec 0x1001d1 (fun s => s.RIP = 0x1001d1) (xorR32R32Effect 0x1001d1 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[278, 153]
    (.letOp (n := 282) (.out 0x1001d4 (xorR32R32Effect 0x1001d4 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[276, 209]
    (.letOp (n := 283) (.exec 0x1001d4 (fun s => s.RIP = 0x1001d4) (xorR32R32Effect 0x1001d4 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[276, 209]
    (.letOp (n := 284) (.out 0x1001d7 (xorR32R32Effect 0x1001d7 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[282, 274]
    (.letOp (n := 285) (.exec 0x1001d7 (fun s => s.RIP = 0x1001d7) (xorR32R32Effect 0x1001d7 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[282, 274]
    (b_l100000_6)))))))))))))))))))))))))))))))))))))))

def bytes_l100000_5 : List UInt8 :=
  [0x44, 0x89, 0xC1, 0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC1, 0x44,
    0x31, 0xEA, 0x44, 0x31, 0xE6, 0x31, 0xCA, 0x66, 0x89, 0x57, 0x04, 0x89, 0xF0, 0x66, 0xC1, 0xC0,
    0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x89, 0xF1, 0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x09, 0xC1, 0x45, 0x31, 0xE0, 0x8B, 0x14, 0x24, 0x44, 0x31, 0xFA, 0x45, 0x31, 0xD8,
    0x41, 0x31, 0xC8] ++ bytes_l100000_6

theorem code_l100000_5 : ∀ x ∈ codeRange 0x100197 bytes_l100000_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x197 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_6

@[cfg_block] def b_l100000_4 : Block Op Label signature Reg.count 209 :=
  .letOp (n := 209) (.out 0x100150 (xorR32R32Effect 0x100150 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[177, 191]
    (.letOp (n := 210) (.exec 0x100150 (fun s => s.RIP = 0x100150) (xorR32R32Effect 0x100150 3 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[177, 191]
    (.letOp (n := 211) (.out 0x100153 (xorR32R32Effect 0x100153 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[97, 209]
    (.letOp (n := 212) (.exec 0x100153 (fun s => s.RIP = 0x100153) (xorR32R32Effect 0x100153 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[97, 209]
    (.letOp (n := 213) (.out 0x100156 (xorR32R32Effect 0x100156 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[211, 207]
    (.letOp (n := 214) (.exec 0x100156 (fun s => s.RIP = 0x100156) (xorR32R32Effect 0x100156 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[211, 207]
    (.letOp (n := 215) (.exec 0x100158 (StorePre 0x100158 3 (fun s => AddrMode.addr (.base 7 .none) s (0x100158 + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x100158 3 3 (.base 7 .none)) (Reg.operands [.gpr 3, .gpr 7] [])) #v[213, 7]
    (.letOp (n := 216) (.out 0x10015b (xorR32R32Effect 0x10015b 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[69, 107]
    (.letOp (n := 217) (.exec 0x10015b (fun s => s.RIP = 0x10015b) (xorR32R32Effect 0x10015b 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[69, 107]
    (.letOp (n := 218) (.out 0x10015e (movR32R32Effect 0x10015e 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[216]
    (.letOp (n := 219) (.exec 0x10015e (fun s => s.RIP = 0x10015e) (movR32R32Effect 0x10015e 2 0 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 220) (.out 0x100160 (rolR16Effect 0x100160 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[218]
    (.letOp (n := 221) (.exec 0x100160 (fun s => s.RIP = 0x100160) (rolR16Effect 0x100160 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[218]
    (.letOp (n := 222) (.out 0x100164 (andEaxImm32Effect 0x100164 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[220]
    (.letOp (n := 223) (.exec 0x100164 (fun s => s.RIP = 0x100164) (andEaxImm32Effect 0x100164 0x3333) (Reg.operands [.gpr 0] [])) #v[220]
    (.letOp (n := 224) (.out 0x100169 (movR32R32Effect 0x100169 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[216]
    (.letOp (n := 225) (.exec 0x100169 (fun s => s.RIP = 0x100169) (movR32R32Effect 0x100169 3 10 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 226) (.out 0x10016c (rolR16Effect 0x10016c 5 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[224]
    (.letOp (n := 227) (.exec 0x10016c (fun s => s.RIP = 0x10016c) (rolR16Effect 0x10016c 5 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[224]
    (.letOp (n := 228) (.out 0x100171 (andR32Imm32Effect 0x100171 7 10 0xffffcccc) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[226]
    (.letOp (n := 229) (.exec 0x100171 (fun s => s.RIP = 0x100171) (andR32Imm32Effect 0x100171 7 10 0xffffcccc) (Reg.operands [.gpr 10] [])) #v[226]
    (.letOp (n := 230) (.out 0x100178 (orR32R32Effect 0x100178 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[228, 222]
    (.letOp (n := 231) (.exec 0x100178 (fun s => s.RIP = 0x100178) (orR32R32Effect 0x100178 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[228, 222]
    (.letOp (n := 232) (.out 0x10017b (xorR32R32Effect 0x10017b 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[193, 107]
    (.letOp (n := 233) (.exec 0x10017b (fun s => s.RIP = 0x10017b) (xorR32R32Effect 0x10017b 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[193, 107]
    (.letOp (n := 234) (.out 0x10017e (xorR32R32Effect 0x10017e 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[232, 209]
    (.letOp (n := 235) (.exec 0x10017e (fun s => s.RIP = 0x10017e) (xorR32R32Effect 0x10017e 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[232, 209]
    (.letOp (n := 236) (.out 0x100181 (xorR32R32Effect 0x100181 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[234, 230]
    (.letOp (n := 237) (.exec 0x100181 (fun s => s.RIP = 0x100181) (xorR32R32Effect 0x100181 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[234, 230]
    (.letOp (n := 238) (.out 0x100184 (xorR32R32Effect 0x100184 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[71, 121]
    (.letOp (n := 239) (.exec 0x100184 (fun s => s.RIP = 0x100184) (xorR32R32Effect 0x100184 3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[71, 121]
    (.letOp (n := 240) (.exec 0x100187 (StorePre 0x100187 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100187 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100187 4 1 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[236, 7]
    (.letOp (n := 241) (.out 0x10018b (movR32R32Effect 0x10018b 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[238]
    (.letOp (n := 242) (.exec 0x10018b (fun s => s.RIP = 0x10018b) (movR32R32Effect 0x10018b 3 0 8) (Reg.operands [.gpr 8] [])) #v[238]
    (.letOp (n := 243) (.out 0x10018e (rolR16Effect 0x10018e 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[241]
    (.letOp (n := 244) (.exec 0x10018e (fun s => s.RIP = 0x10018e) (rolR16Effect 0x10018e 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[241]
    (.letOp (n := 245) (.out 0x100192 (andEaxImm32Effect 0x100192 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[243]
    (.letOp (n := 246) (.exec 0x100192 (fun s => s.RIP = 0x100192) (andEaxImm32Effect 0x100192 0x3333) (Reg.operands [.gpr 0] [])) #v[243]
    (b_l100000_5))))))))))))))))))))))))))))))))))))))

def bytes_l100000_4 : List UInt8 :=
  [0x41, 0x31, 0xEB, 0x44, 0x31, 0xDB, 0x31, 0xC3, 0x66, 0x89, 0x1F, 0x44, 0x31, 0xCA, 0x89, 0xD0,
    0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x41, 0x89, 0xD2, 0x66, 0x41, 0xC1, 0xC2,
    0x0A, 0x41, 0x81, 0xE2, 0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x09, 0xC2, 0x44, 0x31, 0xC9, 0x44, 0x31,
    0xD9, 0x44, 0x31, 0xD1, 0x45, 0x31, 0xE8, 0x66, 0x89, 0x4F, 0x02, 0x44, 0x89, 0xC0, 0x66, 0xC1,
    0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00] ++ bytes_l100000_5

theorem code_l100000_4 : ∀ x ∈ codeRange 0x100150 bytes_l100000_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x150 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_5

@[cfg_block] def b_l100000_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x1000ff (rorR16Effect 0x1000ff 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 171) (.exec 0x1000ff (fun s => s.RIP = 0x1000ff) (rorR16Effect 0x1000ff 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 172) (.out 0x100102 (andEaxImm32Effect 0x100102 0xffff8888) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[170]
    (.letOp (n := 173) (.exec 0x100102 (fun s => s.RIP = 0x100102) (andEaxImm32Effect 0x100102 0xffff8888) (Reg.operands [.gpr 0] [])) #v[170]
    (.letOp (n := 174) (.out 0x100107 (orR32R32Effect 0x100107 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[172, 168]
    (.letOp (n := 175) (.exec 0x100107 (fun s => s.RIP = 0x100107) (orR32R32Effect 0x100107 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[172, 168]
    (.letOp (n := 176) (.exec 0x10010a (StorePre 0x10010a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10010a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10010a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[174, 65]
    (.letOp (n := 177) (.out 0x10010e (movzxR32M16Effect 0x10010e 5 11 (.base 7 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7]
    (.letOp (n := 178) (.exec 0x10010e (LoadPre 0x10010e (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10010e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10010e 5 11 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 179) (.out 0x100113 (movR32R32Effect 0x100113 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[177]
    (.letOp (n := 180) (.exec 0x100113 (fun s => s.RIP = 0x100113) (movR32R32Effect 0x100113 3 10 11) (Reg.operands [.gpr 11] [])) #v[177]
    (.letOp (n := 181) (.out 0x100116 (rolR16Effect 0x100116 5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[179]
    (.letOp (n := 182) (.exec 0x100116 (fun s => s.RIP = 0x100116) (rolR16Effect 0x100116 5 10 11) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x10011b (andR32Imm32Effect 0x10011b 7 10 0x7777) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[181]
    (.letOp (n := 184) (.exec 0x10011b (fun s => s.RIP = 0x10011b) (andR32Imm32Effect 0x10011b 7 10 0x7777) (Reg.operands [.gpr 10] [])) #v[181]
    (.letOp (n := 185) (.out 0x100122 (movR32R32Effect 0x100122 3 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 11] []) (.reg (.gpr 5))) #v[177]
    (.letOp (n := 186) (.exec 0x100122 (fun s => s.RIP = 0x100122) (movR32R32Effect 0x100122 3 5 11) (Reg.operands [.gpr 11] [])) #v[177]
    (.letOp (n := 187) (.out 0x100125 (rorR16Effect 0x100125 3 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[185]
    (.letOp (n := 188) (.exec 0x100125 (fun s => s.RIP = 0x100125) (rorR16Effect 0x100125 3 5 1) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 189) (.out 0x100128 (andR32Imm32Effect 0x100128 6 5 0xffff8888) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[187]
    (.letOp (n := 190) (.exec 0x100128 (fun s => s.RIP = 0x100128) (andR32Imm32Effect 0x100128 6 5 0xffff8888) (Reg.operands [.gpr 5] [])) #v[187]
    (.letOp (n := 191) (.out 0x10012e (orR32R32Effect 0x10012e 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[189, 183]
    (.letOp (n := 192) (.exec 0x10012e (fun s => s.RIP = 0x10012e) (orR32R32Effect 0x10012e 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[189, 183]
    (.letOp (n := 193) (.out 0x100131 (xorR32R32Effect 0x100131 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[67, 97]
    (.letOp (n := 194) (.exec 0x100131 (fun s => s.RIP = 0x100131) (xorR32R32Effect 0x100131 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[67, 97]
    (.letOp (n := 195) (.out 0x100133 (movR32R32Effect 0x100133 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[193]
    (.letOp (n := 196) (.exec 0x100133 (fun s => s.RIP = 0x100133) (movR32R32Effect 0x100133 3 10 1) (Reg.operands [.gpr 1] [])) #v[193]
    (.letOp (n := 197) (.out 0x100136 (rolR16Effect 0x100136 5 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[195]
    (.letOp (n := 198) (.exec 0x100136 (fun s => s.RIP = 0x100136) (rolR16Effect 0x100136 5 10 6) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 199) (.out 0x10013b (andR32Imm32Effect 0x10013b 7 10 0x3333) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[197]
    (.letOp (n := 200) (.exec 0x10013b (fun s => s.RIP = 0x10013b) (andR32Imm32Effect 0x10013b 7 10 0x3333) (Reg.operands [.gpr 10] [])) #v[197]
    (.letOp (n := 201) (.out 0x100142 (movR32R32Effect 0x100142 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[193]
    (.letOp (n := 202) (.exec 0x100142 (fun s => s.RIP = 0x100142) (movR32R32Effect 0x100142 2 0 1) (Reg.operands [.gpr 1] [])) #v[193]
    (.letOp (n := 203) (.out 0x100144 (rolR16Effect 0x100144 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[201]
    (.letOp (n := 204) (.exec 0x100144 (fun s => s.RIP = 0x100144) (rolR16Effect 0x100144 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[201]
    (.letOp (n := 205) (.out 0x100148 (andEaxImm32Effect 0x100148 0xffffcccc) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[203]
    (.letOp (n := 206) (.exec 0x100148 (fun s => s.RIP = 0x100148) (andEaxImm32Effect 0x100148 0xffffcccc) (Reg.operands [.gpr 0] [])) #v[203]
    (.letOp (n := 207) (.out 0x10014d (orR32R32Effect 0x10014d 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[205, 199]
    (.letOp (n := 208) (.exec 0x10014d (fun s => s.RIP = 0x10014d) (orR32R32Effect 0x10014d 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[205, 199]
    (b_l100000_4)))))))))))))))))))))))))))))))))))))))

def bytes_l100000_3 : List UInt8 :=
  [0x66, 0xD1, 0xC8, 0x25, 0x88, 0x88, 0xFF, 0xFF, 0x44, 0x09, 0xD0, 0x89, 0x44, 0x24, 0x08, 0x44,
    0x0F, 0xB7, 0x5F, 0x0E, 0x45, 0x89, 0xDA, 0x66, 0x41, 0xC1, 0xC2, 0x0B, 0x41, 0x81, 0xE2, 0x77,
    0x77, 0x00, 0x00, 0x44, 0x89, 0xDD, 0x66, 0xD1, 0xCD, 0x81, 0xE5, 0x88, 0x88, 0xFF, 0xFF, 0x44,
    0x09, 0xD5, 0x31, 0xD9, 0x41, 0x89, 0xCA, 0x66, 0x41, 0xC1, 0xC2, 0x06, 0x41, 0x81, 0xE2, 0x33,
    0x33, 0x00, 0x00, 0x89, 0xC8, 0x66, 0xC1, 0xC0, 0x0A, 0x25, 0xCC, 0xCC, 0xFF, 0xFF, 0x44, 0x09,
    0xD0] ++ bytes_l100000_4

theorem code_l100000_3 : ∀ x ∈ codeRange 0x1000ff bytes_l100000_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xff 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_4

@[cfg_block] def b_l100000_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x10009f (andR32Imm32Effect 0x10009f 7 12 0xffff8888) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[131]
    (.letOp (n := 134) (.exec 0x10009f (fun s => s.RIP = 0x10009f) (andR32Imm32Effect 0x10009f 7 12 0xffff8888) (Reg.operands [.gpr 12] [])) #v[131]
    (.letOp (n := 135) (.out 0x1000a6 (orR32R32Effect 0x1000a6 3 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[133, 127]
    (.letOp (n := 136) (.exec 0x1000a6 (fun s => s.RIP = 0x1000a6) (orR32R32Effect 0x1000a6 3 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[133, 127]
    (.letOp (n := 137) (.exec 0x1000a9 (StorePre 0x1000a9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1000a9 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1000a9 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 138) (.out 0x1000ad (movR32R32Effect 0x1000ad 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[75]
    (.letOp (n := 139) (.exec 0x1000ad (fun s => s.RIP = 0x1000ad) (movR32R32Effect 0x1000ad 3 10 15) (Reg.operands [.gpr 15] [])) #v[75]
    (.letOp (n := 140) (.out 0x1000b0 (rolR16Effect 0x1000b0 5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[138]
    (.letOp (n := 141) (.exec 0x1000b0 (fun s => s.RIP = 0x1000b0) (rolR16Effect 0x1000b0 5 10 11) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138]
    (.letOp (n := 142) (.out 0x1000b5 (andR32Imm32Effect 0x1000b5 7 10 0x7777) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[140]
    (.letOp (n := 143) (.exec 0x1000b5 (fun s => s.RIP = 0x1000b5) (andR32Imm32Effect 0x1000b5 7 10 0x7777) (Reg.operands [.gpr 10] [])) #v[140]
    (.letOp (n := 144) (.out 0x1000bc (rorR16Effect 0x1000bc 4 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[75]
    (.letOp (n := 145) (.exec 0x1000bc (fun s => s.RIP = 0x1000bc) (rorR16Effect 0x1000bc 4 15 1) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 146) (.out 0x1000c0 (andR32Imm32Effect 0x1000c0 7 15 0xffff8888) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[144]
    (.letOp (n := 147) (.exec 0x1000c0 (fun s => s.RIP = 0x1000c0) (andR32Imm32Effect 0x1000c0 7 15 0xffff8888) (Reg.operands [.gpr 15] [])) #v[144]
    (.letOp (n := 148) (.exec 0x1000c7 (StorePre 0x1000c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1000c7 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1000c7 14 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 149) (.out 0x1000cc (movR32R32Effect 0x1000cc 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[77]
    (.letOp (n := 150) (.exec 0x1000cc (fun s => s.RIP = 0x1000cc) (movR32R32Effect 0x1000cc 3 11 14) (Reg.operands [.gpr 14] [])) #v[77]
    (.letOp (n := 151) (.out 0x1000cf (rolR16Effect 0x1000cf 5 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[149]
    (.letOp (n := 152) (.exec 0x1000cf (fun s => s.RIP = 0x1000cf) (rolR16Effect 0x1000cf 5 11 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 153) (.out 0x1000d4 (orR32R32Effect 0x1000d4 3 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[146, 142]
    (.letOp (n := 154) (.exec 0x1000d4 (fun s => s.RIP = 0x1000d4) (orR32R32Effect 0x1000d4 3 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[146, 142]
    (.letOp (n := 155) (.out 0x1000d7 (rorR16Effect 0x1000d7 4 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[77]
    (.letOp (n := 156) (.exec 0x1000d7 (fun s => s.RIP = 0x1000d7) (rorR16Effect 0x1000d7 4 14 1) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 157) (.out 0x1000db (andR32Imm32Effect 0x1000db 7 11 0x7777) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[151]
    (.letOp (n := 158) (.exec 0x1000db (fun s => s.RIP = 0x1000db) (andR32Imm32Effect 0x1000db 7 11 0x7777) (Reg.operands [.gpr 11] [])) #v[151]
    (.letOp (n := 159) (.out 0x1000e2 (andR32Imm32Effect 0x1000e2 7 14 0xffff8888) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[155]
    (.letOp (n := 160) (.exec 0x1000e2 (fun s => s.RIP = 0x1000e2) (andR32Imm32Effect 0x1000e2 7 14 0xffff8888) (Reg.operands [.gpr 14] [])) #v[155]
    (.letOp (n := 161) (.out 0x1000e9 (orR32R32Effect 0x1000e9 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x1000e9 (fun s => s.RIP = 0x1000e9) (orR32R32Effect 0x1000e9 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[159, 157]
    (.letOp (n := 163) (.exec 0x1000ec (StorePre 0x1000ec 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1000ec + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1000ec 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 164) (.out 0x1000f0 (movR32R32Effect 0x1000f0 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[79]
    (.letOp (n := 165) (.exec 0x1000f0 (fun s => s.RIP = 0x1000f0) (movR32R32Effect 0x1000f0 3 10 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 166) (.out 0x1000f3 (rolR16Effect 0x1000f3 5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[164]
    (.letOp (n := 167) (.exec 0x1000f3 (fun s => s.RIP = 0x1000f3) (rolR16Effect 0x1000f3 5 10 11) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164]
    (.letOp (n := 168) (.out 0x1000f8 (andR32Imm32Effect 0x1000f8 7 10 0x7777) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[166]
    (.letOp (n := 169) (.exec 0x1000f8 (fun s => s.RIP = 0x1000f8) (andR32Imm32Effect 0x1000f8 7 10 0x7777) (Reg.operands [.gpr 10] [])) #v[166]
    (b_l100000_3)))))))))))))))))))))))))))))))))))))

def bytes_l100000_2 : List UInt8 :=
  [0x41, 0x81, 0xE4, 0x88, 0x88, 0xFF, 0xFF, 0x45, 0x09, 0xD4, 0x44, 0x89, 0x3C, 0x24, 0x45, 0x89,
    0xFA, 0x66, 0x41, 0xC1, 0xC2, 0x0B, 0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00, 0x66, 0x41, 0xD1,
    0xCF, 0x41, 0x81, 0xE7, 0x88, 0x88, 0xFF, 0xFF, 0x44, 0x89, 0x74, 0x24, 0x04, 0x45, 0x89, 0xF3,
    0x66, 0x41, 0xC1, 0xC3, 0x0B, 0x45, 0x09, 0xD7, 0x66, 0x41, 0xD1, 0xCE, 0x41, 0x81, 0xE3, 0x77,
    0x77, 0x00, 0x00, 0x41, 0x81, 0xE6, 0x88, 0x88, 0xFF, 0xFF, 0x45, 0x09, 0xDE, 0x89, 0x44, 0x24,
    0x0C, 0x41, 0x89, 0xC2, 0x66, 0x41, 0xC1, 0xC2, 0x0B, 0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] ++ bytes_l100000_3

theorem code_l100000_2 : ∀ x ∈ codeRange 0x10009f bytes_l100000_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9f 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_3

@[cfg_block] def b_l100000_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x100046 (movR32R32Effect 0x100046 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[69]
    (.letOp (n := 94) (.exec 0x100046 (fun s => s.RIP = 0x100046) (movR32R32Effect 0x100046 3 10 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 95) (.out 0x100049 (rolR16Effect 0x100049 5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[93]
    (.letOp (n := 96) (.exec 0x100049 (fun s => s.RIP = 0x100049) (rolR16Effect 0x100049 5 10 11) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x10004e (orR32R32Effect 0x10004e 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[91, 85]
    (.letOp (n := 98) (.exec 0x10004e (fun s => s.RIP = 0x10004e) (orR32R32Effect 0x10004e 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[91, 85]
    (.letOp (n := 99) (.out 0x100051 (movR32R32Effect 0x100051 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 100) (.exec 0x100051 (fun s => s.RIP = 0x100051) (movR32R32Effect 0x100051 3 9 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 101) (.out 0x100054 (rorR16Effect 0x100054 4 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[99]
    (.letOp (n := 102) (.exec 0x100054 (fun s => s.RIP = 0x100054) (rorR16Effect 0x100054 4 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[99]
    (.letOp (n := 103) (.out 0x100058 (andR32Imm32Effect 0x100058 7 10 0x7777) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[95]
    (.letOp (n := 104) (.exec 0x100058 (fun s => s.RIP = 0x100058) (andR32Imm32Effect 0x100058 7 10 0x7777) (Reg.operands [.gpr 10] [])) #v[95]
    (.letOp (n := 105) (.out 0x10005f (andR32Imm32Effect 0x10005f 7 9 0xffff8888) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[101]
    (.letOp (n := 106) (.exec 0x10005f (fun s => s.RIP = 0x10005f) (andR32Imm32Effect 0x10005f 7 9 0xffff8888) (Reg.operands [.gpr 9] [])) #v[101]
    (.letOp (n := 107) (.out 0x100066 (orR32R32Effect 0x100066 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x100066 (fun s => s.RIP = 0x100066) (orR32R32Effect 0x100066 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x100069 (movR32R32Effect 0x100069 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[71]
    (.letOp (n := 110) (.exec 0x100069 (fun s => s.RIP = 0x100069) (movR32R32Effect 0x100069 3 10 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 111) (.out 0x10006c (rolR16Effect 0x10006c 5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[109]
    (.letOp (n := 112) (.exec 0x10006c (fun s => s.RIP = 0x10006c) (rolR16Effect 0x10006c 5 10 11) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x100071 (andR32Imm32Effect 0x100071 7 10 0x7777) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[111]
    (.letOp (n := 114) (.exec 0x100071 (fun s => s.RIP = 0x100071) (andR32Imm32Effect 0x100071 7 10 0x7777) (Reg.operands [.gpr 10] [])) #v[111]
    (.letOp (n := 115) (.out 0x100078 (movR32R32Effect 0x100078 3 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 116) (.exec 0x100078 (fun s => s.RIP = 0x100078) (movR32R32Effect 0x100078 3 13 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 117) (.out 0x10007b (rorR16Effect 0x10007b 4 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[115]
    (.letOp (n := 118) (.exec 0x10007b (fun s => s.RIP = 0x10007b) (rorR16Effect 0x10007b 4 13 1) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x10007f (andR32Imm32Effect 0x10007f 7 13 0xffff8888) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[117]
    (.letOp (n := 120) (.exec 0x10007f (fun s => s.RIP = 0x10007f) (andR32Imm32Effect 0x10007f 7 13 0xffff8888) (Reg.operands [.gpr 13] [])) #v[117]
    (.letOp (n := 121) (.out 0x100086 (orR32R32Effect 0x100086 3 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[119, 113]
    (.letOp (n := 122) (.exec 0x100086 (fun s => s.RIP = 0x100086) (orR32R32Effect 0x100086 3 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[119, 113]
    (.letOp (n := 123) (.out 0x100089 (movR32R32Effect 0x100089 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[73]
    (.letOp (n := 124) (.exec 0x100089 (fun s => s.RIP = 0x100089) (movR32R32Effect 0x100089 3 10 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 125) (.out 0x10008c (rolR16Effect 0x10008c 5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[123]
    (.letOp (n := 126) (.exec 0x10008c (fun s => s.RIP = 0x10008c) (rolR16Effect 0x10008c 5 10 11) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 127) (.out 0x100091 (andR32Imm32Effect 0x100091 7 10 0x7777) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[125]
    (.letOp (n := 128) (.exec 0x100091 (fun s => s.RIP = 0x100091) (andR32Imm32Effect 0x100091 7 10 0x7777) (Reg.operands [.gpr 10] [])) #v[125]
    (.letOp (n := 129) (.out 0x100098 (movR32R32Effect 0x100098 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[73]
    (.letOp (n := 130) (.exec 0x100098 (fun s => s.RIP = 0x100098) (movR32R32Effect 0x100098 3 12 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 131) (.out 0x10009b (rorR16Effect 0x10009b 4 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[129]
    (.letOp (n := 132) (.exec 0x10009b (fun s => s.RIP = 0x10009b) (rorR16Effect 0x10009b 4 12 1) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (b_l100000_2))))))))))))))))))))))))))))))))))))))))

def bytes_l100000_1 : List UInt8 :=
  [0x41, 0x89, 0xD2, 0x66, 0x41, 0xC1, 0xC2, 0x0B, 0x44, 0x09, 0xCB, 0x41, 0x89, 0xD1, 0x66, 0x41,
    0xD1, 0xC9, 0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00, 0x41, 0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF,
    0x45, 0x09, 0xD1, 0x45, 0x89, 0xC2, 0x66, 0x41, 0xC1, 0xC2, 0x0B, 0x41, 0x81, 0xE2, 0x77, 0x77,
    0x00, 0x00, 0x45, 0x89, 0xC5, 0x66, 0x41, 0xD1, 0xCD, 0x41, 0x81, 0xE5, 0x88, 0x88, 0xFF, 0xFF,
    0x45, 0x09, 0xD5, 0x41, 0x89, 0xF2, 0x66, 0x41, 0xC1, 0xC2, 0x0B, 0x41, 0x81, 0xE2, 0x77, 0x77,
    0x00, 0x00, 0x41, 0x89, 0xF4, 0x66, 0x41, 0xD1, 0xCC] ++ bytes_l100000_2

theorem code_l100000_1 : ∀ x ∈ codeRange 0x100046 bytes_l100000_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x46 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_2

@[cfg_block] def b_l100000 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100000 (pushR64Effect 0x100000 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100000 (PushPre 0x100000 1) (pushR64Effect 0x100000 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100001 (pushR64Effect 0x100001 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100001 (PushPre 0x100001 2) (pushR64Effect 0x100001 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100003 (pushR64Effect 0x100003 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100003 (PushPre 0x100003 2) (pushR64Effect 0x100003 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100005 (pushR64Effect 0x100005 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100005 (PushPre 0x100005 2) (pushR64Effect 0x100005 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100007 (pushR64Effect 0x100007 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100007 (PushPre 0x100007 2) (pushR64Effect 0x100007 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100009 (pushR64Effect 0x100009 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100009 (PushPre 0x100009 1) (pushR64Effect 0x100009 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10000a (subR64Imm8Effect 0x10000a 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10000a (fun s => s.RIP = 0x10000a) (subR64Imm8Effect 0x10000a 4 0x10) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10000e (movzxR32M16Effect 0x10000e 3 1 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 68) (.exec 0x10000e (LoadPre 0x10000e (fun s => AddrMode.addr (.base 7 .none) s (0x10000e + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x10000e 3 1 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x100011 (movzxR32M16Effect 0x100011 4 2 (.base 7 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 70) (.exec 0x100011 (LoadPre 0x100011 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100011 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100011 4 2 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x100015 (movzxR32M16Effect 0x100015 5 8 (.base 7 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 72) (.exec 0x100015 (LoadPre 0x100015 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x100015 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100015 5 8 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x10001a (movzxR32M16Effect 0x10001a 4 6 (.base 7 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 74) (.exec 0x10001a (LoadPre 0x10001a (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10001a + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10001a 4 6 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x10001e (movzxR32M16Effect 0x10001e 5 15 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 76) (.exec 0x10001e (LoadPre 0x10001e (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10001e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10001e 5 15 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.out 0x100023 (movzxR32M16Effect 0x100023 5 14 (.base 7 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 78) (.exec 0x100023 (LoadPre 0x100023 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x100023 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100023 5 14 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x100028 (movzxR32M16Effect 0x100028 4 0 (.base 7 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 80) (.exec 0x100028 (LoadPre 0x100028 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x100028 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100028 4 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 81) (.out 0x10002c (movR32R32Effect 0x10002c 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 82) (.exec 0x10002c (fun s => s.RIP = 0x10002c) (movR32R32Effect 0x10002c 3 9 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 83) (.out 0x10002f (rolR16Effect 0x10002f 5 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[81]
    (.letOp (n := 84) (.exec 0x10002f (fun s => s.RIP = 0x10002f) (rolR16Effect 0x10002f 5 9 11) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x100034 (andR32Imm32Effect 0x100034 7 9 0x7777) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[83]
    (.letOp (n := 86) (.exec 0x100034 (fun s => s.RIP = 0x100034) (andR32Imm32Effect 0x100034 7 9 0x7777) (Reg.operands [.gpr 9] [])) #v[83]
    (.letOp (n := 87) (.out 0x10003b (movR32R32Effect 0x10003b 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[67]
    (.letOp (n := 88) (.exec 0x10003b (fun s => s.RIP = 0x10003b) (movR32R32Effect 0x10003b 2 3 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 89) (.out 0x10003d (rorR16Effect 0x10003d 3 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[87]
    (.letOp (n := 90) (.exec 0x10003d (fun s => s.RIP = 0x10003d) (rorR16Effect 0x10003d 3 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x100040 (andR32Imm32Effect 0x100040 6 3 0xffff8888) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[89]
    (.letOp (n := 92) (.exec 0x100040 (fun s => s.RIP = 0x100040) (andR32Imm32Effect 0x100040 6 3 0xffff8888) (Reg.operands [.gpr 3] [])) #v[89]
    (b_l100000_1))))))))))))))))))))))))))))))))))))))))

def bytes_l100000 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x0F, 0xB7,
    0x0F, 0x0F, 0xB7, 0x57, 0x02, 0x44, 0x0F, 0xB7, 0x47, 0x04, 0x0F, 0xB7, 0x77, 0x06, 0x44, 0x0F,
    0xB7, 0x7F, 0x08, 0x44, 0x0F, 0xB7, 0x77, 0x0A, 0x0F, 0xB7, 0x47, 0x0C, 0x41, 0x89, 0xC9, 0x66,
    0x41, 0xC1, 0xC1, 0x0B, 0x41, 0x81, 0xE1, 0x77, 0x77, 0x00, 0x00, 0x89, 0xCB, 0x66, 0xD1, 0xCB,
    0x81, 0xE3, 0x88, 0x88, 0xFF, 0xFF] ++ bytes_l100000_1

theorem code_l100000 : ∀ x ∈ codeRange 0x100000 bytes_l100000, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x0 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_1

@[cfg_block] def b_l1002a0_9 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x100549 (rolR64Effect 0x100549 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[399]
    (.letOp (n := 402) (.exec 0x100549 (fun s => s.RIP = 0x100549) (rolR64Effect 0x100549 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[399]
    (.letOp (n := 403) (.exec 0x10054d (StorePre 0x10054d 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10054d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10054d 5 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[397, 359]
    (.letOp (n := 404) (.out 0x100551 (andR64R64Effect 0x100551 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[401, 289]
    (.letOp (n := 405) (.exec 0x100551 (fun s => s.RIP = 0x100551) (andR64R64Effect 0x100551 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[401, 289]
    (.letOp (n := 406) (.out 0x100554 (rolR64Effect 0x100554 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[239]
    (.letOp (n := 407) (.exec 0x100554 (fun s => s.RIP = 0x100554) (rolR64Effect 0x100554 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239]
    (.letOp (n := 408) (.out 0x100558 (andR64R64Effect 0x100558 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[406, 322]
    (.letOp (n := 409) (.exec 0x100558 (fun s => s.RIP = 0x100558) (andR64R64Effect 0x100558 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[406, 322]
    (.letOp (n := 410) (.out 0x10055b (orR64R64Effect 0x10055b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[408, 404]
    (.letOp (n := 411) (.exec 0x10055b (fun s => s.RIP = 0x10055b) (orR64R64Effect 0x10055b 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[408, 404]
    (.letOp (n := 412) (.out 0x10055e (xorR64R64Effect 0x10055e 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[410, 389]
    (.letOp (n := 413) (.exec 0x10055e (fun s => s.RIP = 0x10055e) (xorR64R64Effect 0x10055e 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[410, 389]
    (.letOp (n := 414) (.exec 0x100561 (StorePre 0x100561 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100561 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100561 10 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[412, 359]
    (.letOp (n := 415) (.out 0x100565 (addR64Imm8Effect 0x100565 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 416) (.exec 0x100565 (fun s => s.RIP = 0x100565) (addR64Imm8Effect 0x100565 4 0x30) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 417) (.out 0x100569 (popR64Effect 0x100569 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[415]
    (.letOp (n := 418) (.out 0x100569 (popR64Effect 0x100569 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[415]
    (.letOp (n := 419) (.exec 0x100569 (PopPre 0x100569) (popR64Effect 0x100569 1 3) (Reg.operands [.gpr 4] [])) #v[415]
    (.letOp (n := 420) (.out 0x10056a (popR64Effect 0x10056a 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[418]
    (.letOp (n := 421) (.out 0x10056a (popR64Effect 0x10056a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[418]
    (.letOp (n := 422) (.exec 0x10056a (PopPre 0x10056a) (popR64Effect 0x10056a 2 12) (Reg.operands [.gpr 4] [])) #v[418]
    (.letOp (n := 423) (.out 0x10056c (popR64Effect 0x10056c 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[421]
    (.letOp (n := 424) (.out 0x10056c (popR64Effect 0x10056c 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[421]
    (.letOp (n := 425) (.exec 0x10056c (PopPre 0x10056c) (popR64Effect 0x10056c 2 13) (Reg.operands [.gpr 4] [])) #v[421]
    (.letOp (n := 426) (.out 0x10056e (popR64Effect 0x10056e 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[424]
    (.letOp (n := 427) (.out 0x10056e (popR64Effect 0x10056e 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[424]
    (.letOp (n := 428) (.exec 0x10056e (PopPre 0x10056e) (popR64Effect 0x10056e 2 14) (Reg.operands [.gpr 4] [])) #v[424]
    (.letOp (n := 429) (.out 0x100570 (popR64Effect 0x100570 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[427]
    (.letOp (n := 430) (.out 0x100570 (popR64Effect 0x100570 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[427]
    (.letOp (n := 431) (.exec 0x100570 (PopPre 0x100570) (popR64Effect 0x100570 2 15) (Reg.operands [.gpr 4] [])) #v[427]
    (.letOp (n := 432) (.out 0x100572 (popR64Effect 0x100572 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[430]
    (.letOp (n := 433) (.out 0x100572 (popR64Effect 0x100572 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[430]
    (.letOp (n := 434) (.exec 0x100572 (PopPre 0x100572) (popR64Effect 0x100572 1 5) (Reg.operands [.gpr 4] [])) #v[430]
    (.letOp (n := 435) (.out 0x100573 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[433]
    (.letOp (n := 436) (.out 0x100573 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[433]
    (.letOp (n := 437) (.exec 0x100573 (RetPre 0x100573) (retEffect) (Reg.operands [.gpr 4] [])) #v[433]
    (.terminate (.ret (RegMap.args [(0, 404), (1, 389), (2, 370), (3, 417), (4, 436), (5, 432), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 426), (15, 429), (22, 22), (39, 39), (50, 50), (51, 51)] 438) (some ⟨435, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_9 : List UInt8 :=
  [0x48, 0xC1, 0xC0, 0x18, 0x48, 0x89, 0x6F, 0x30, 0x48, 0x21, 0xD8, 0x49, 0xC1, 0xC2, 0x28, 0x4D,
    0x21, 0xC2, 0x49, 0x09, 0xC2, 0x49, 0x31, 0xCA, 0x4C, 0x89, 0x57, 0x38, 0x48, 0x83, 0xC4, 0x30,
    0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1002a0_9 : ∀ x ∈ codeRange 0x100549 bytes_l1002a0_9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x549 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1002a0_8 : Block Op Label signature Reg.count 362 :=
  .letOp (n := 362) (.out 0x100506 (movR64R64Effect 0x100506 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[332]
    (.letOp (n := 363) (.exec 0x100506 (fun s => s.RIP = 0x100506) (movR64R64Effect 0x100506 0 14) (Reg.operands [.gpr 14] [])) #v[332]
    (.letOp (n := 364) (.out 0x100509 (rolR64Effect 0x100509 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[362]
    (.letOp (n := 365) (.exec 0x100509 (fun s => s.RIP = 0x100509) (rolR64Effect 0x100509 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[362]
    (.letOp (n := 366) (.out 0x10050d (andR64R64Effect 0x10050d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[364, 289]
    (.letOp (n := 367) (.exec 0x10050d (fun s => s.RIP = 0x10050d) (andR64R64Effect 0x10050d 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[364, 289]
    (.letOp (n := 368) (.out 0x100510 (xorR64R64Effect 0x100510 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[355, 332]
    (.letOp (n := 369) (.exec 0x100510 (fun s => s.RIP = 0x100510) (xorR64R64Effect 0x100510 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[355, 332]
    (.letOp (n := 370) (.out 0x100513 (movR64R64Effect 0x100513 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[368]
    (.letOp (n := 371) (.exec 0x100513 (fun s => s.RIP = 0x100513) (movR64R64Effect 0x100513 2 1) (Reg.operands [.gpr 1] [])) #v[368]
    (.letOp (n := 372) (.out 0x100516 (rolR64Effect 0x100516 4 14 40) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[332]
    (.letOp (n := 373) (.exec 0x100516 (fun s => s.RIP = 0x100516) (rolR64Effect 0x100516 4 14 40) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[332]
    (.letOp (n := 374) (.out 0x10051a (andR64R64Effect 0x10051a 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[372, 322]
    (.letOp (n := 375) (.exec 0x10051a (fun s => s.RIP = 0x10051a) (andR64R64Effect 0x10051a 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[372, 322]
    (.letOp (n := 376) (.out 0x10051d (orR64R64Effect 0x10051d 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[374, 366]
    (.letOp (n := 377) (.exec 0x10051d (fun s => s.RIP = 0x10051d) (orR64R64Effect 0x10051d 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[374, 366]
    (.letOp (n := 378) (.out 0x100520 (xorR64R64Effect 0x100520 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[376, 343]
    (.letOp (n := 379) (.exec 0x100520 (fun s => s.RIP = 0x100520) (xorR64R64Effect 0x100520 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[376, 343]
    (.letOp (n := 380) (.exec 0x100523 (StorePre 0x100523 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100523 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100523 14 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[378, 359]
    (.letOp (n := 381) (.out 0x100527 (movR64R64Effect 0x100527 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[357]
    (.letOp (n := 382) (.exec 0x100527 (fun s => s.RIP = 0x100527) (movR64R64Effect 0x100527 0 5) (Reg.operands [.gpr 5] [])) #v[357]
    (.letOp (n := 383) (.out 0x10052a (rolR64Effect 0x10052a 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[381]
    (.letOp (n := 384) (.exec 0x10052a (fun s => s.RIP = 0x10052a) (rolR64Effect 0x10052a 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[381]
    (.letOp (n := 385) (.out 0x10052e (andR64R64Effect 0x10052e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[383, 289]
    (.letOp (n := 386) (.exec 0x10052e (fun s => s.RIP = 0x10052e) (andR64R64Effect 0x10052e 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[383, 289]
    (.letOp (n := 387) (.out 0x100531 (movR64M64Effect 0x100531 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 388) (.exec 0x100531 (LoadPre 0x100531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100531 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100531 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 389) (.out 0x100536 (xorR64R64Effect 0x100536 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[387, 357]
    (.letOp (n := 390) (.exec 0x100536 (fun s => s.RIP = 0x100536) (xorR64R64Effect 0x100536 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[387, 357]
    (.letOp (n := 391) (.out 0x100539 (rolR64Effect 0x100539 4 5 40) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[357]
    (.letOp (n := 392) (.exec 0x100539 (fun s => s.RIP = 0x100539) (rolR64Effect 0x100539 4 5 40) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[357]
    (.letOp (n := 393) (.out 0x10053d (andR64R64Effect 0x10053d 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[391, 322]
    (.letOp (n := 394) (.exec 0x10053d (fun s => s.RIP = 0x10053d) (andR64R64Effect 0x10053d 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[391, 322]
    (.letOp (n := 395) (.out 0x100540 (orR64R64Effect 0x100540 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[393, 385]
    (.letOp (n := 396) (.exec 0x100540 (fun s => s.RIP = 0x100540) (orR64R64Effect 0x100540 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[393, 385]
    (.letOp (n := 397) (.out 0x100543 (xorR64R64Effect 0x100543 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[395, 370]
    (.letOp (n := 398) (.exec 0x100543 (fun s => s.RIP = 0x100543) (xorR64R64Effect 0x100543 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[395, 370]
    (.letOp (n := 399) (.out 0x100546 (movR64R64Effect 0x100546 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[239]
    (.letOp (n := 400) (.exec 0x100546 (fun s => s.RIP = 0x100546) (movR64R64Effect 0x100546 0 10) (Reg.operands [.gpr 10] [])) #v[239]
    (b_l1002a0_9)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_8 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x21, 0xD8, 0x4C, 0x31, 0xF1, 0x48, 0x89, 0xCA,
    0x49, 0xC1, 0xC6, 0x28, 0x4D, 0x21, 0xC6, 0x49, 0x09, 0xC6, 0x49, 0x31, 0xF6, 0x4C, 0x89, 0x77,
    0x28, 0x48, 0x89, 0xE8, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x21, 0xD8, 0x48, 0x8B, 0x4C, 0x24, 0x10,
    0x48, 0x31, 0xE9, 0x48, 0xC1, 0xC5, 0x28, 0x4C, 0x21, 0xC5, 0x48, 0x09, 0xC5, 0x48, 0x31, 0xD5,
    0x4C, 0x89, 0xD0] ++ bytes_l1002a0_9

theorem code_l1002a0_8 : ∀ x ∈ codeRange 0x100506 bytes_l1002a0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x506 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_9

@[cfg_block] def b_l1002a0_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x1004c2 (orR64R64Effect 0x1004c2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[320, 318]
    (.letOp (n := 325) (.exec 0x1004c2 (fun s => s.RIP = 0x1004c2) (orR64R64Effect 0x1004c2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[320, 318]
    (.letOp (n := 326) (.out 0x1004c5 (xorR64R64Effect 0x1004c5 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[293, 239]
    (.letOp (n := 327) (.exec 0x1004c5 (fun s => s.RIP = 0x1004c5) (xorR64R64Effect 0x1004c5 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[293, 239]
    (.letOp (n := 328) (.out 0x1004c8 (xorR64R64Effect 0x1004c8 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[326, 324]
    (.letOp (n := 329) (.exec 0x1004c8 (fun s => s.RIP = 0x1004c8) (xorR64R64Effect 0x1004c8 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[326, 324]
    (.letOp (n := 330) (.out 0x1004cb (movR64M64Effect 0x1004cb 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 331) (.exec 0x1004cb (LoadPre 0x1004cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1004cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004cb 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 332) (.out 0x1004d0 (xorR64R64Effect 0x1004d0 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[79, 330]
    (.letOp (n := 333) (.exec 0x1004d0 (fun s => s.RIP = 0x1004d0) (xorR64R64Effect 0x1004d0 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[79, 330]
    (.letOp (n := 334) (.exec 0x1004d3 (StorePre 0x1004d3 4 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1004d3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004d3 13 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[328, 277]
    (.letOp (n := 335) (.out 0x1004d7 (movR64R64Effect 0x1004d7 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[312]
    (.letOp (n := 336) (.exec 0x1004d7 (fun s => s.RIP = 0x1004d7) (movR64R64Effect 0x1004d7 0 11) (Reg.operands [.gpr 11] [])) #v[312]
    (.letOp (n := 337) (.out 0x1004da (rolR64Effect 0x1004da 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[335]
    (.letOp (n := 338) (.exec 0x1004da (fun s => s.RIP = 0x1004da) (rolR64Effect 0x1004da 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335]
    (.letOp (n := 339) (.out 0x1004de (andR64R64Effect 0x1004de 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[337, 289]
    (.letOp (n := 340) (.exec 0x1004de (fun s => s.RIP = 0x1004de) (andR64R64Effect 0x1004de 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[337, 289]
    (.letOp (n := 341) (.out 0x1004e1 (xorR64R64Effect 0x1004e1 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[330, 312]
    (.letOp (n := 342) (.exec 0x1004e1 (fun s => s.RIP = 0x1004e1) (xorR64R64Effect 0x1004e1 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[330, 312]
    (.letOp (n := 343) (.out 0x1004e4 (movR64R64Effect 0x1004e4 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[341]
    (.letOp (n := 344) (.exec 0x1004e4 (fun s => s.RIP = 0x1004e4) (movR64R64Effect 0x1004e4 6 1) (Reg.operands [.gpr 1] [])) #v[341]
    (.letOp (n := 345) (.out 0x1004e7 (rolR64Effect 0x1004e7 4 11 40) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[312]
    (.letOp (n := 346) (.exec 0x1004e7 (fun s => s.RIP = 0x1004e7) (rolR64Effect 0x1004e7 4 11 40) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 347) (.out 0x1004eb (andR64R64Effect 0x1004eb 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[345, 322]
    (.letOp (n := 348) (.exec 0x1004eb (fun s => s.RIP = 0x1004eb) (andR64R64Effect 0x1004eb 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[345, 322]
    (.letOp (n := 349) (.out 0x1004ee (orR64R64Effect 0x1004ee 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[347, 339]
    (.letOp (n := 350) (.exec 0x1004ee (fun s => s.RIP = 0x1004ee) (orR64R64Effect 0x1004ee 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[347, 339]
    (.letOp (n := 351) (.out 0x1004f1 (xorR64R64Effect 0x1004f1 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[314, 239]
    (.letOp (n := 352) (.exec 0x1004f1 (fun s => s.RIP = 0x1004f1) (xorR64R64Effect 0x1004f1 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[314, 239]
    (.letOp (n := 353) (.out 0x1004f4 (xorR64R64Effect 0x1004f4 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[351, 349]
    (.letOp (n := 354) (.exec 0x1004f4 (fun s => s.RIP = 0x1004f4) (xorR64R64Effect 0x1004f4 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[351, 349]
    (.letOp (n := 355) (.out 0x1004f7 (movR64M64Effect 0x1004f7 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 356) (.exec 0x1004f7 (LoadPre 0x1004f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1004f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004f7 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 357) (.out 0x1004fc (xorR64R64Effect 0x1004fc 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[172, 355]
    (.letOp (n := 358) (.exec 0x1004fc (fun s => s.RIP = 0x1004fc) (xorR64R64Effect 0x1004fc 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[172, 355]
    (.letOp (n := 359) (.out 0x1004ff (movR64R64Effect 0x1004ff 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[277]
    (.letOp (n := 360) (.exec 0x1004ff (fun s => s.RIP = 0x1004ff) (movR64R64Effect 0x1004ff 7 2) (Reg.operands [.gpr 2] [])) #v[277]
    (.letOp (n := 361) (.exec 0x100502 (StorePre 0x100502 4 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x100502 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100502 15 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[353, 277]
    (b_l1002a0_8))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_7 : List UInt8 :=
  [0x48, 0x09, 0xC7, 0x4D, 0x31, 0xD5, 0x49, 0x31, 0xFD, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x49, 0x31,
    0xCE, 0x4C, 0x89, 0x6A, 0x18, 0x4C, 0x89, 0xD8, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x21, 0xD8, 0x4C,
    0x31, 0xD9, 0x48, 0x89, 0xCE, 0x49, 0xC1, 0xC3, 0x28, 0x4D, 0x21, 0xC3, 0x49, 0x09, 0xC3, 0x4D,
    0x31, 0xD7, 0x4D, 0x31, 0xDF, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0x31, 0xCD, 0x48, 0x89, 0xD7,
    0x4C, 0x89, 0x7A, 0x20] ++ bytes_l1002a0_8

theorem code_l1002a0_7 : ∀ x ∈ codeRange 0x1004c2 bytes_l1002a0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4c2 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_8

@[cfg_block] def b_l1002a0_6 : Block Op Label signature Reg.count 285 :=
  .letOp (n := 285) (.out 0x100473 (movR64R64Effect 0x100473 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[281]
    (.letOp (n := 286) (.exec 0x100473 (fun s => s.RIP = 0x100473) (movR64R64Effect 0x100473 0 9) (Reg.operands [.gpr 9] [])) #v[281]
    (.letOp (n := 287) (.out 0x100476 (rolR64Effect 0x100476 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 288) (.exec 0x100476 (fun s => s.RIP = 0x100476) (rolR64Effect 0x100476 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[285]
    (.letOp (n := 289) (.out 0x10047a (movR64Imm64Effect 0x10047a 3 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 290) (.exec 0x10047a (fun s => s.RIP = 0x10047a) (movR64Imm64Effect 0x10047a 3 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 291) (.out 0x100484 (andR64R64Effect 0x100484 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[287, 289]
    (.letOp (n := 292) (.exec 0x100484 (fun s => s.RIP = 0x100484) (andR64R64Effect 0x100484 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[287, 289]
    (.letOp (n := 293) (.out 0x100487 (xorR64R64Effect 0x100487 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[142, 281]
    (.letOp (n := 294) (.exec 0x100487 (fun s => s.RIP = 0x100487) (xorR64R64Effect 0x100487 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[142, 281]
    (.letOp (n := 295) (.out 0x10048a (rolR64Effect 0x10048a 4 9 40) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[281]
    (.letOp (n := 296) (.exec 0x10048a (fun s => s.RIP = 0x10048a) (rolR64Effect 0x10048a 4 9 40) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[281]
    (.letOp (n := 297) (.out 0x10048e (movR64Imm64Effect 0x10048e 6 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 298) (.exec 0x10048e (fun s => s.RIP = 0x10048e) (movR64Imm64Effect 0x10048e 6 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 299) (.out 0x100498 (andR64R64Effect 0x100498 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[295, 297]
    (.letOp (n := 300) (.exec 0x100498 (fun s => s.RIP = 0x100498) (andR64R64Effect 0x100498 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[295, 297]
    (.letOp (n := 301) (.out 0x10049b (orR64R64Effect 0x10049b 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[299, 291]
    (.letOp (n := 302) (.exec 0x10049b (fun s => s.RIP = 0x10049b) (orR64R64Effect 0x10049b 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[299, 291]
    (.letOp (n := 303) (.out 0x10049e (xorR64R64Effect 0x10049e 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[247, 279]
    (.letOp (n := 304) (.exec 0x10049e (fun s => s.RIP = 0x10049e) (xorR64R64Effect 0x10049e 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[247, 279]
    (.letOp (n := 305) (.out 0x1004a1 (xorR64R64Effect 0x1004a1 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[303, 301]
    (.letOp (n := 306) (.exec 0x1004a1 (fun s => s.RIP = 0x1004a1) (xorR64R64Effect 0x1004a1 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[303, 301]
    (.letOp (n := 307) (.exec 0x1004a4 (StorePre 0x1004a4 4 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1004a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004a4 8 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 2] [])) #v[305, 277]
    (.letOp (n := 308) (.out 0x1004a8 (movR64R64Effect 0x1004a8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[283]
    (.letOp (n := 309) (.exec 0x1004a8 (fun s => s.RIP = 0x1004a8) (movR64R64Effect 0x1004a8 0 7) (Reg.operands [.gpr 7] [])) #v[283]
    (.letOp (n := 310) (.out 0x1004ab (rolR64Effect 0x1004ab 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[308]
    (.letOp (n := 311) (.exec 0x1004ab (fun s => s.RIP = 0x1004ab) (rolR64Effect 0x1004ab 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[308]
    (.letOp (n := 312) (.out 0x1004af (xorR64R64Effect 0x1004af 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[77, 158]
    (.letOp (n := 313) (.exec 0x1004af (fun s => s.RIP = 0x1004af) (xorR64R64Effect 0x1004af 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[77, 158]
    (.letOp (n := 314) (.out 0x1004b2 (xorR64R64Effect 0x1004b2 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[158, 283]
    (.letOp (n := 315) (.exec 0x1004b2 (fun s => s.RIP = 0x1004b2) (xorR64R64Effect 0x1004b2 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[158, 283]
    (.letOp (n := 316) (.out 0x1004b5 (rolR64Effect 0x1004b5 4 7 40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[283]
    (.letOp (n := 317) (.exec 0x1004b5 (fun s => s.RIP = 0x1004b5) (rolR64Effect 0x1004b5 4 7 40) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[283]
    (.letOp (n := 318) (.out 0x1004b9 (andR64R64Effect 0x1004b9 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[310, 289]
    (.letOp (n := 319) (.exec 0x1004b9 (fun s => s.RIP = 0x1004b9) (andR64R64Effect 0x1004b9 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[310, 289]
    (.letOp (n := 320) (.out 0x1004bc (andR64R64Effect 0x1004bc 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[316, 297]
    (.letOp (n := 321) (.exec 0x1004bc (fun s => s.RIP = 0x1004bc) (andR64R64Effect 0x1004bc 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[316, 297]
    (.letOp (n := 322) (.out 0x1004bf (movR64R64Effect 0x1004bf 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[297]
    (.letOp (n := 323) (.exec 0x1004bf (fun s => s.RIP = 0x1004bf) (movR64R64Effect 0x1004bf 8 6) (Reg.operands [.gpr 6] [])) #v[297]
    (b_l1002a0_7)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_6 : List UInt8 :=
  [0x4C, 0x89, 0xC8, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0xBB, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0x00, 0x48, 0x21, 0xD8, 0x4D, 0x31, 0xCD, 0x49, 0xC1, 0xC1, 0x28, 0x48, 0xBE, 0x00, 0xFF, 0x00,
    0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x49, 0x21, 0xF1, 0x49, 0x09, 0xC1, 0x49, 0x31, 0xC8, 0x4D, 0x31,
    0xC8, 0x4C, 0x89, 0x42, 0x10, 0x48, 0x89, 0xF8, 0x48, 0xC1, 0xC0, 0x18, 0x4D, 0x31, 0xFB, 0x49,
    0x31, 0xFF, 0x48, 0xC1, 0xC7, 0x28, 0x48, 0x21, 0xD8, 0x48, 0x21, 0xF7, 0x49, 0x89, 0xF0] ++ bytes_l1002a0_7

theorem code_l1002a0_6 : ∀ x ∈ codeRange 0x100473 bytes_l1002a0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x473 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_7

@[cfg_block] def b_l1002a0_5 : Block Op Label signature Reg.count 247 :=
  .letOp (n := 247) (.out 0x100422 (xorR64R64Effect 0x100422 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[71, 245]
    (.letOp (n := 248) (.exec 0x100422 (fun s => s.RIP = 0x100422) (xorR64R64Effect 0x100422 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[71, 245]
    (.letOp (n := 249) (.out 0x100425 (movR64R64Effect 0x100425 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[247]
    (.letOp (n := 250) (.exec 0x100425 (fun s => s.RIP = 0x100425) (movR64R64Effect 0x100425 0 8) (Reg.operands [.gpr 8] [])) #v[247]
    (.letOp (n := 251) (.out 0x100428 (rolR64Effect 0x100428 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[249]
    (.letOp (n := 252) (.exec 0x100428 (fun s => s.RIP = 0x100428) (rolR64Effect 0x100428 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[249]
    (.letOp (n := 253) (.out 0x10042c (movR64M64Effect 0x10042c 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 254) (.exec 0x10042c (LoadPre 0x10042c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10042c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10042c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 255) (.exec 0x100431 (StorePre 0x100431 3 (fun s => AddrMode.addr (.base 1 .none) s (0x100431 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x100431 12 (.base 1 .none)) (Reg.operands [.gpr 12, .gpr 1] [])) #v[243, 253]
    (.letOp (n := 256) (.out 0x100434 (movR64R64Effect 0x100434 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[247]
    (.letOp (n := 257) (.exec 0x100434 (fun s => s.RIP = 0x100434) (movR64R64Effect 0x100434 6 8) (Reg.operands [.gpr 8] [])) #v[247]
    (.letOp (n := 258) (.out 0x100437 (rolR64Effect 0x100437 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[256]
    (.letOp (n := 259) (.exec 0x100437 (fun s => s.RIP = 0x100437) (rolR64Effect 0x100437 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[256]
    (.letOp (n := 260) (.out 0x10043b (movR64Imm64Effect 0x10043b 12 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 261) (.exec 0x10043b (fun s => s.RIP = 0x10043b) (movR64Imm64Effect 0x10043b 12 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 262) (.out 0x100445 (andR64R64Effect 0x100445 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[251, 260]
    (.letOp (n := 263) (.exec 0x100445 (fun s => s.RIP = 0x100445) (andR64R64Effect 0x100445 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[251, 260]
    (.letOp (n := 264) (.out 0x100448 (movR64Imm64Effect 0x100448 12 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 265) (.exec 0x100448 (fun s => s.RIP = 0x100448) (movR64Imm64Effect 0x100448 12 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 266) (.out 0x100452 (andR64R64Effect 0x100452 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[258, 264]
    (.letOp (n := 267) (.exec 0x100452 (fun s => s.RIP = 0x100452) (andR64R64Effect 0x100452 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[258, 264]
    (.letOp (n := 268) (.out 0x100455 (orR64R64Effect 0x100455 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[266, 262]
    (.letOp (n := 269) (.exec 0x100455 (fun s => s.RIP = 0x100455) (orR64R64Effect 0x100455 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[266, 262]
    (.letOp (n := 270) (.out 0x100458 (xorR64R64Effect 0x100458 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[216, 245]
    (.letOp (n := 271) (.exec 0x100458 (fun s => s.RIP = 0x100458) (xorR64R64Effect 0x100458 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[216, 245]
    (.letOp (n := 272) (.out 0x10045b (xorR64R64Effect 0x10045b 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[270, 239]
    (.letOp (n := 273) (.exec 0x10045b (fun s => s.RIP = 0x10045b) (xorR64R64Effect 0x10045b 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[270, 239]
    (.letOp (n := 274) (.out 0x10045e (xorR64R64Effect 0x10045e 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[272, 268]
    (.letOp (n := 275) (.exec 0x10045e (fun s => s.RIP = 0x10045e) (xorR64R64Effect 0x10045e 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[272, 268]
    (.letOp (n := 276) (.exec 0x100461 (StorePre 0x100461 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x100461 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100461 2 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 1] [])) #v[274, 253]
    (.letOp (n := 277) (.out 0x100465 (movR64R64Effect 0x100465 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[253]
    (.letOp (n := 278) (.exec 0x100465 (fun s => s.RIP = 0x100465) (movR64R64Effect 0x100465 2 1) (Reg.operands [.gpr 1] [])) #v[253]
    (.letOp (n := 279) (.out 0x100468 (movR64M64Effect 0x100468 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 280) (.exec 0x100468 (LoadPre 0x100468 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100468 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100468 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 281) (.out 0x10046d (xorR64R64Effect 0x10046d 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[73, 279]
    (.letOp (n := 282) (.exec 0x10046d (fun s => s.RIP = 0x10046d) (xorR64R64Effect 0x10046d 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[73, 279]
    (.letOp (n := 283) (.out 0x100470 (xorR64R64Effect 0x100470 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[75, 142]
    (.letOp (n := 284) (.exec 0x100470 (fun s => s.RIP = 0x100470) (xorR64R64Effect 0x100470 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[75, 142]
    (b_l1002a0_6))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_5 : List UInt8 :=
  [0x49, 0x31, 0xD8, 0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x4C,
    0x89, 0x21, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xC6, 0x28, 0x49, 0xBC, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0x00, 0xFF, 0x00, 0x4C, 0x21, 0xE0, 0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0x4C, 0x21, 0xE6, 0x48, 0x09, 0xC6, 0x48, 0x31, 0xDA, 0x4C, 0x31, 0xD2, 0x48, 0x31, 0xF2, 0x48,
    0x89, 0x51, 0x08, 0x48, 0x89, 0xCA, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x31, 0xC9, 0x4C, 0x31,
    0xEF] ++ bytes_l1002a0_6

theorem code_l1002a0_5 : ∀ x ∈ codeRange 0x100422 bytes_l1002a0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x422 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_6

@[cfg_block] def b_l1002a0_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x1003cb (rolR64Effect 0x1003cb 4 0 60) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[206]
    (.letOp (n := 209) (.exec 0x1003cb (fun s => s.RIP = 0x1003cb) (rolR64Effect 0x1003cb 4 0 60) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[206]
    (.letOp (n := 210) (.out 0x1003cf (movR64Imm64Effect 0x1003cf 1 0xf000f000f000f000) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 211) (.exec 0x1003cf (fun s => s.RIP = 0x1003cf) (movR64Imm64Effect 0x1003cf 1 0xf000f000f000f000) (Reg.operands [] [])) #v[]
    (.letOp (n := 212) (.out 0x1003d9 (andR64R64Effect 0x1003d9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[208, 210]
    (.letOp (n := 213) (.exec 0x1003d9 (fun s => s.RIP = 0x1003d9) (andR64R64Effect 0x1003d9 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[208, 210]
    (.letOp (n := 214) (.out 0x1003dc (movR64R64Effect 0x1003dc 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[212]
    (.letOp (n := 215) (.exec 0x1003dc (fun s => s.RIP = 0x1003dc) (movR64R64Effect 0x1003dc 1 0) (Reg.operands [.gpr 0] [])) #v[212]
    (.letOp (n := 216) (.out 0x1003df (xorR64R64Effect 0x1003df 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[69, 98]
    (.letOp (n := 217) (.exec 0x1003df (fun s => s.RIP = 0x1003df) (xorR64R64Effect 0x1003df 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[69, 98]
    (.letOp (n := 218) (.out 0x1003e2 (movR64R64Effect 0x1003e2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[216]
    (.letOp (n := 219) (.exec 0x1003e2 (fun s => s.RIP = 0x1003e2) (movR64R64Effect 0x1003e2 0 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 220) (.out 0x1003e5 (rolR64Effect 0x1003e5 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[218]
    (.letOp (n := 221) (.exec 0x1003e5 (fun s => s.RIP = 0x1003e5) (rolR64Effect 0x1003e5 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[218]
    (.letOp (n := 222) (.out 0x1003e9 (orR64R64Effect 0x1003e9 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[214, 204]
    (.letOp (n := 223) (.exec 0x1003e9 (fun s => s.RIP = 0x1003e9) (orR64R64Effect 0x1003e9 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[214, 204]
    (.letOp (n := 224) (.exec 0x1003ec (StorePre 0x1003ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1003ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003ec 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[222, 65]
    (.letOp (n := 225) (.out 0x1003f1 (movR64Imm64Effect 0x1003f1 6 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 226) (.exec 0x1003f1 (fun s => s.RIP = 0x1003f1) (movR64Imm64Effect 0x1003f1 6 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 227) (.out 0x1003fb (andR64R64Effect 0x1003fb 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[220, 225]
    (.letOp (n := 228) (.exec 0x1003fb (fun s => s.RIP = 0x1003fb) (andR64R64Effect 0x1003fb 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[220, 225]
    (.letOp (n := 229) (.out 0x1003fe (movR64R64Effect 0x1003fe 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[216]
    (.letOp (n := 230) (.exec 0x1003fe (fun s => s.RIP = 0x1003fe) (movR64R64Effect 0x1003fe 6 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 231) (.out 0x100401 (rolR64Effect 0x100401 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[229]
    (.letOp (n := 232) (.exec 0x100401 (fun s => s.RIP = 0x100401) (rolR64Effect 0x100401 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[229]
    (.letOp (n := 233) (.out 0x100405 (movR64Imm64Effect 0x100405 3 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 234) (.exec 0x100405 (fun s => s.RIP = 0x100405) (movR64Imm64Effect 0x100405 3 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 235) (.out 0x10040f (andR64R64Effect 0x10040f 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[231, 233]
    (.letOp (n := 236) (.exec 0x10040f (fun s => s.RIP = 0x10040f) (andR64R64Effect 0x10040f 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[231, 233]
    (.letOp (n := 237) (.out 0x100412 (orR64R64Effect 0x100412 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[235, 227]
    (.letOp (n := 238) (.exec 0x100412 (fun s => s.RIP = 0x100412) (orR64R64Effect 0x100412 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[235, 227]
    (.letOp (n := 239) (.out 0x100415 (xorR64R64Effect 0x100415 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[196, 222]
    (.letOp (n := 240) (.exec 0x100415 (fun s => s.RIP = 0x100415) (xorR64R64Effect 0x100415 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[196, 222]
    (.letOp (n := 241) (.out 0x100418 (xorR64R64Effect 0x100418 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[98, 239]
    (.letOp (n := 242) (.exec 0x100418 (fun s => s.RIP = 0x100418) (xorR64R64Effect 0x100418 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[98, 239]
    (.letOp (n := 243) (.out 0x10041b (xorR64R64Effect 0x10041b 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[241, 237]
    (.letOp (n := 244) (.exec 0x10041b (fun s => s.RIP = 0x10041b) (xorR64R64Effect 0x10041b 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[241, 237]
    (.letOp (n := 245) (.out 0x10041e (movR64M64Effect 0x10041e 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 246) (.exec 0x10041e (LoadPre 0x10041e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10041e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10041e 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1002a0_5)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_4 : List UInt8 :=
  [0x48, 0xC1, 0xC0, 0x3C, 0x48, 0xB9, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x48, 0x21,
    0xC8, 0x48, 0x89, 0xC1, 0x4C, 0x31, 0xE2, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x09,
    0xF1, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0xBE, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00,
    0x48, 0x21, 0xF0, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xC6, 0x28, 0x48, 0xBB, 0x00, 0xFF, 0x00, 0xFF,
    0x00, 0xFF, 0x00, 0xFF, 0x48, 0x21, 0xDE, 0x48, 0x09, 0xC6, 0x49, 0x31, 0xCA, 0x4D, 0x31, 0xD4,
    0x49, 0x31, 0xF4, 0x48, 0x8B, 0x1C, 0x24] ++ bytes_l1002a0_5

theorem code_l1002a0_4 : ∀ x ∈ codeRange 0x1003cb bytes_l1002a0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3cb 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_5

@[cfg_block] def b_l1002a0_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x100371 (andR64R64Effect 0x100371 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[168, 94]
    (.letOp (n := 171) (.exec 0x100371 (fun s => s.RIP = 0x100371) (andR64R64Effect 0x100371 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[168, 94]
    (.letOp (n := 172) (.out 0x100374 (movR64M64Effect 0x100374 5 (.base 1 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[67]
    (.letOp (n := 173) (.exec 0x100374 (LoadPre 0x100374 (fun s => AddrMode.addr (.base 1 (.d8 0x30)) s (0x100374 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100374 5 (.base 1 (.d8 0x30))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 174) (.out 0x100378 (movR64R64Effect 0x100378 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[172]
    (.letOp (n := 175) (.exec 0x100378 (fun s => s.RIP = 0x100378) (movR64R64Effect 0x100378 6 5) (Reg.operands [.gpr 5] [])) #v[172]
    (.letOp (n := 176) (.out 0x10037b (rolR64Effect 0x10037b 4 6 44) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[174]
    (.letOp (n := 177) (.exec 0x10037b (fun s => s.RIP = 0x10037b) (rolR64Effect 0x10037b 4 6 44) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[174]
    (.letOp (n := 178) (.out 0x10037f (orR64R64Effect 0x10037f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[170, 164]
    (.letOp (n := 179) (.exec 0x10037f (fun s => s.RIP = 0x10037f) (orR64R64Effect 0x10037f 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[170, 164]
    (.letOp (n := 180) (.exec 0x100382 (StorePre 0x100382 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100382 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100382 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[178, 65]
    (.letOp (n := 181) (.out 0x100387 (movR64R64Effect 0x100387 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[172]
    (.letOp (n := 182) (.exec 0x100387 (fun s => s.RIP = 0x100387) (movR64R64Effect 0x100387 0 5) (Reg.operands [.gpr 5] [])) #v[172]
    (.letOp (n := 183) (.out 0x10038a (rolR64Effect 0x10038a 4 0 60) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[181]
    (.letOp (n := 184) (.exec 0x10038a (fun s => s.RIP = 0x10038a) (rolR64Effect 0x10038a 4 0 60) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[181]
    (.letOp (n := 185) (.out 0x10038e (movR64Imm64Effect 0x10038e 10 0xfff0fff0fff0fff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 186) (.exec 0x10038e (fun s => s.RIP = 0x10038e) (movR64Imm64Effect 0x10038e 10 0xfff0fff0fff0fff) (Reg.operands [] [])) #v[]
    (.letOp (n := 187) (.out 0x100398 (andR64R64Effect 0x100398 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[176, 185]
    (.letOp (n := 188) (.exec 0x100398 (fun s => s.RIP = 0x100398) (andR64R64Effect 0x100398 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[176, 185]
    (.letOp (n := 189) (.out 0x10039b (movR64Imm64Effect 0x10039b 10 0xf000f000f000f000) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 190) (.exec 0x10039b (fun s => s.RIP = 0x10039b) (movR64Imm64Effect 0x10039b 10 0xf000f000f000f000) (Reg.operands [] [])) #v[]
    (.letOp (n := 191) (.out 0x1003a5 (andR64R64Effect 0x1003a5 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[183, 189]
    (.letOp (n := 192) (.exec 0x1003a5 (fun s => s.RIP = 0x1003a5) (andR64R64Effect 0x1003a5 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[183, 189]
    (.letOp (n := 193) (.out 0x1003a8 (orR64R64Effect 0x1003a8 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[191, 187]
    (.letOp (n := 194) (.exec 0x1003a8 (fun s => s.RIP = 0x1003a8) (orR64R64Effect 0x1003a8 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[191, 187]
    (.letOp (n := 195) (.exec 0x1003ab (StorePre 0x1003ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1003ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003ab 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[193, 65]
    (.letOp (n := 196) (.out 0x1003b0 (movR64M64Effect 0x1003b0 10 (.base 1 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[67]
    (.letOp (n := 197) (.exec 0x1003b0 (LoadPre 0x1003b0 (fun s => AddrMode.addr (.base 1 (.d8 0x38)) s (0x1003b0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1003b0 10 (.base 1 (.d8 0x38))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 198) (.out 0x1003b4 (movR64R64Effect 0x1003b4 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[196]
    (.letOp (n := 199) (.exec 0x1003b4 (fun s => s.RIP = 0x1003b4) (movR64R64Effect 0x1003b4 6 10) (Reg.operands [.gpr 10] [])) #v[196]
    (.letOp (n := 200) (.out 0x1003b7 (rolR64Effect 0x1003b7 4 6 44) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[198]
    (.letOp (n := 201) (.exec 0x1003b7 (fun s => s.RIP = 0x1003b7) (rolR64Effect 0x1003b7 4 6 44) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[198]
    (.letOp (n := 202) (.out 0x1003bb (movR64Imm64Effect 0x1003bb 0 0xfff0fff0fff0fff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 203) (.exec 0x1003bb (fun s => s.RIP = 0x1003bb) (movR64Imm64Effect 0x1003bb 0 0xfff0fff0fff0fff) (Reg.operands [] [])) #v[]
    (.letOp (n := 204) (.out 0x1003c5 (andR64R64Effect 0x1003c5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[200, 202]
    (.letOp (n := 205) (.exec 0x1003c5 (fun s => s.RIP = 0x1003c5) (andR64R64Effect 0x1003c5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[200, 202]
    (.letOp (n := 206) (.out 0x1003c8 (movR64R64Effect 0x1003c8 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[196]
    (.letOp (n := 207) (.exec 0x1003c8 (fun s => s.RIP = 0x1003c8) (movR64R64Effect 0x1003c8 0 10) (Reg.operands [.gpr 10] [])) #v[196]
    (b_l1002a0_4))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_3 : List UInt8 :=
  [0x48, 0x21, 0xE8, 0x48, 0x8B, 0x69, 0x30, 0x48, 0x89, 0xEE, 0x48, 0xC1, 0xC6, 0x2C, 0x4C, 0x09,
    0xD0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xE8, 0x48, 0xC1, 0xC0, 0x3C, 0x49, 0xBA, 0xFF,
    0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0x4C, 0x21, 0xD6, 0x49, 0xBA, 0x00, 0xF0, 0x00, 0xF0,
    0x00, 0xF0, 0x00, 0xF0, 0x4C, 0x21, 0xD0, 0x48, 0x09, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C,
    0x8B, 0x51, 0x38, 0x4C, 0x89, 0xD6, 0x48, 0xC1, 0xC6, 0x2C, 0x48, 0xB8, 0xFF, 0x0F, 0xFF, 0x0F,
    0xFF, 0x0F, 0xFF, 0x0F, 0x48, 0x21, 0xC6, 0x4C, 0x89, 0xD0] ++ bytes_l1002a0_4

theorem code_l1002a0_3 : ∀ x ∈ codeRange 0x100371 bytes_l1002a0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x371 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_4

@[cfg_block] def b_l1002a0_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x10032e (orR64R64Effect 0x10032e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[125, 119]
    (.letOp (n := 132) (.exec 0x10032e (fun s => s.RIP = 0x10032e) (orR64R64Effect 0x10032e 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[125, 119]
    (.letOp (n := 133) (.exec 0x100331 (StorePre 0x100331 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100331 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100331 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[131, 65]
    (.letOp (n := 134) (.out 0x100336 (movR64R64Effect 0x100336 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[75]
    (.letOp (n := 135) (.exec 0x100336 (fun s => s.RIP = 0x100336) (movR64R64Effect 0x100336 13 7) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 136) (.out 0x100339 (rolR64Effect 0x100339 4 13 60) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[134]
    (.letOp (n := 137) (.exec 0x100339 (fun s => s.RIP = 0x100339) (rolR64Effect 0x100339 4 13 60) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 138) (.out 0x10033d (andR64R64Effect 0x10033d 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[129, 86]
    (.letOp (n := 139) (.exec 0x10033d (fun s => s.RIP = 0x10033d) (andR64R64Effect 0x10033d 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[129, 86]
    (.letOp (n := 140) (.out 0x100340 (andR64R64Effect 0x100340 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[136, 94]
    (.letOp (n := 141) (.exec 0x100340 (fun s => s.RIP = 0x100340) (andR64R64Effect 0x100340 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[136, 94]
    (.letOp (n := 142) (.out 0x100343 (orR64R64Effect 0x100343 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[140, 138]
    (.letOp (n := 143) (.exec 0x100343 (fun s => s.RIP = 0x100343) (orR64R64Effect 0x100343 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[140, 138]
    (.letOp (n := 144) (.out 0x100346 (movR64R64Effect 0x100346 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[77]
    (.letOp (n := 145) (.exec 0x100346 (fun s => s.RIP = 0x100346) (movR64R64Effect 0x100346 6 11) (Reg.operands [.gpr 11] [])) #v[77]
    (.letOp (n := 146) (.out 0x100349 (rolR64Effect 0x100349 4 6 44) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[144]
    (.letOp (n := 147) (.exec 0x100349 (fun s => s.RIP = 0x100349) (rolR64Effect 0x100349 4 6 44) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[144]
    (.letOp (n := 148) (.out 0x10034d (andR64R64Effect 0x10034d 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[146, 86]
    (.letOp (n := 149) (.exec 0x10034d (fun s => s.RIP = 0x10034d) (andR64R64Effect 0x10034d 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[146, 86]
    (.letOp (n := 150) (.out 0x100350 (movR64R64Effect 0x100350 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[86]
    (.letOp (n := 151) (.exec 0x100350 (fun s => s.RIP = 0x100350) (movR64R64Effect 0x100350 0 15) (Reg.operands [.gpr 15] [])) #v[86]
    (.letOp (n := 152) (.out 0x100353 (movR64R64Effect 0x100353 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 153) (.exec 0x100353 (fun s => s.RIP = 0x100353) (movR64R64Effect 0x100353 15 11) (Reg.operands [.gpr 11] [])) #v[77]
    (.letOp (n := 154) (.out 0x100356 (rolR64Effect 0x100356 4 15 60) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[152]
    (.letOp (n := 155) (.exec 0x100356 (fun s => s.RIP = 0x100356) (rolR64Effect 0x100356 4 15 60) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[152]
    (.letOp (n := 156) (.out 0x10035a (andR64R64Effect 0x10035a 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[154, 94]
    (.letOp (n := 157) (.exec 0x10035a (fun s => s.RIP = 0x10035a) (andR64R64Effect 0x10035a 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[154, 94]
    (.letOp (n := 158) (.out 0x10035d (orR64R64Effect 0x10035d 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[156, 148]
    (.letOp (n := 159) (.exec 0x10035d (fun s => s.RIP = 0x10035d) (orR64R64Effect 0x10035d 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[156, 148]
    (.letOp (n := 160) (.out 0x100360 (movR64R64Effect 0x100360 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[79]
    (.letOp (n := 161) (.exec 0x100360 (fun s => s.RIP = 0x100360) (movR64R64Effect 0x100360 10 14) (Reg.operands [.gpr 14] [])) #v[79]
    (.letOp (n := 162) (.out 0x100363 (rolR64Effect 0x100363 4 10 44) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[160]
    (.letOp (n := 163) (.exec 0x100363 (fun s => s.RIP = 0x100363) (rolR64Effect 0x100363 4 10 44) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[160]
    (.letOp (n := 164) (.out 0x100367 (andR64R64Effect 0x100367 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[162, 150]
    (.letOp (n := 165) (.exec 0x100367 (fun s => s.RIP = 0x100367) (andR64R64Effect 0x100367 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[162, 150]
    (.letOp (n := 166) (.out 0x10036a (movR64R64Effect 0x10036a 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 167) (.exec 0x10036a (fun s => s.RIP = 0x10036a) (movR64R64Effect 0x10036a 0 14) (Reg.operands [.gpr 14] [])) #v[79]
    (.letOp (n := 168) (.out 0x10036d (rolR64Effect 0x10036d 4 0 60) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[166]
    (.letOp (n := 169) (.exec 0x10036d (fun s => s.RIP = 0x10036d) (rolR64Effect 0x10036d 4 0 60) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[166]
    (b_l1002a0_3)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_2 : List UInt8 :=
  [0x48, 0x09, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x49, 0x89, 0xFD, 0x49, 0xC1, 0xC5, 0x3C, 0x4D,
    0x21, 0xFA, 0x49, 0x21, 0xED, 0x4D, 0x09, 0xD5, 0x4C, 0x89, 0xDE, 0x48, 0xC1, 0xC6, 0x2C, 0x4C,
    0x21, 0xFE, 0x4C, 0x89, 0xF8, 0x4D, 0x89, 0xDF, 0x49, 0xC1, 0xC7, 0x3C, 0x49, 0x21, 0xEF, 0x49,
    0x09, 0xF7, 0x4D, 0x89, 0xF2, 0x49, 0xC1, 0xC2, 0x2C, 0x49, 0x21, 0xC2, 0x4C, 0x89, 0xF0, 0x48,
    0xC1, 0xC0, 0x3C] ++ bytes_l1002a0_3

theorem code_l1002a0_2 : ∀ x ∈ codeRange 0x10032e bytes_l1002a0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x32e 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_3

@[cfg_block] def b_l1002a0_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x1002e5 (andR64R64Effect 0x1002e5 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[84, 86]
    (.letOp (n := 93) (.exec 0x1002e5 (fun s => s.RIP = 0x1002e5) (andR64R64Effect 0x1002e5 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[84, 86]
    (.letOp (n := 94) (.out 0x1002e8 (movR64Imm64Effect 0x1002e8 5 0xf000f000f000f000) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 95) (.exec 0x1002e8 (fun s => s.RIP = 0x1002e8) (movR64Imm64Effect 0x1002e8 5 0xf000f000f000f000) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.out 0x1002f2 (andR64R64Effect 0x1002f2 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[90, 94]
    (.letOp (n := 97) (.exec 0x1002f2 (fun s => s.RIP = 0x1002f2) (andR64R64Effect 0x1002f2 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[90, 94]
    (.letOp (n := 98) (.out 0x1002f5 (orR64R64Effect 0x1002f5 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[96, 92]
    (.letOp (n := 99) (.exec 0x1002f5 (fun s => s.RIP = 0x1002f5) (orR64R64Effect 0x1002f5 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[96, 92]
    (.letOp (n := 100) (.out 0x1002f8 (movR64R64Effect 0x1002f8 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 101) (.exec 0x1002f8 (fun s => s.RIP = 0x1002f8) (movR64R64Effect 0x1002f8 6 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 102) (.out 0x1002fb (rolR64Effect 0x1002fb 4 6 44) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[100]
    (.letOp (n := 103) (.exec 0x1002fb (fun s => s.RIP = 0x1002fb) (rolR64Effect 0x1002fb 4 6 44) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100]
    (.letOp (n := 104) (.out 0x1002ff (andR64R64Effect 0x1002ff 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[102, 86]
    (.letOp (n := 105) (.exec 0x1002ff (fun s => s.RIP = 0x1002ff) (andR64R64Effect 0x1002ff 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[102, 86]
    (.letOp (n := 106) (.out 0x100302 (movR64R64Effect 0x100302 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 107) (.exec 0x100302 (fun s => s.RIP = 0x100302) (movR64R64Effect 0x100302 0 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 108) (.out 0x100305 (rolR64Effect 0x100305 4 0 60) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[106]
    (.letOp (n := 109) (.exec 0x100305 (fun s => s.RIP = 0x100305) (rolR64Effect 0x100305 4 0 60) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[106]
    (.letOp (n := 110) (.out 0x100309 (andR64R64Effect 0x100309 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[108, 94]
    (.letOp (n := 111) (.exec 0x100309 (fun s => s.RIP = 0x100309) (andR64R64Effect 0x100309 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[108, 94]
    (.letOp (n := 112) (.out 0x10030c (orR64R64Effect 0x10030c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[110, 104]
    (.letOp (n := 113) (.exec 0x10030c (fun s => s.RIP = 0x10030c) (orR64R64Effect 0x10030c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[110, 104]
    (.letOp (n := 114) (.exec 0x10030f (StorePre 0x10030f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10030f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10030f 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[112, 65]
    (.letOp (n := 115) (.out 0x100313 (movR64R64Effect 0x100313 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 116) (.exec 0x100313 (fun s => s.RIP = 0x100313) (movR64R64Effect 0x100313 6 9) (Reg.operands [.gpr 9] [])) #v[73]
    (.letOp (n := 117) (.out 0x100316 (rolR64Effect 0x100316 4 6 44) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[115]
    (.letOp (n := 118) (.exec 0x100316 (fun s => s.RIP = 0x100316) (rolR64Effect 0x100316 4 6 44) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x10031a (andR64R64Effect 0x10031a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[117, 86]
    (.letOp (n := 120) (.exec 0x10031a (fun s => s.RIP = 0x10031a) (andR64R64Effect 0x10031a 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[117, 86]
    (.letOp (n := 121) (.out 0x10031d (movR64R64Effect 0x10031d 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 122) (.exec 0x10031d (fun s => s.RIP = 0x10031d) (movR64R64Effect 0x10031d 0 9) (Reg.operands [.gpr 9] [])) #v[73]
    (.letOp (n := 123) (.out 0x100320 (rolR64Effect 0x100320 4 0 60) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[121]
    (.letOp (n := 124) (.exec 0x100320 (fun s => s.RIP = 0x100320) (rolR64Effect 0x100320 4 0 60) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 125) (.out 0x100324 (andR64R64Effect 0x100324 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[123, 94]
    (.letOp (n := 126) (.exec 0x100324 (fun s => s.RIP = 0x100324) (andR64R64Effect 0x100324 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[123, 94]
    (.letOp (n := 127) (.out 0x100327 (movR64R64Effect 0x100327 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[75]
    (.letOp (n := 128) (.exec 0x100327 (fun s => s.RIP = 0x100327) (movR64R64Effect 0x100327 10 7) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 129) (.out 0x10032a (rolR64Effect 0x10032a 4 10 44) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[127]
    (.letOp (n := 130) (.exec 0x10032a (fun s => s.RIP = 0x10032a) (rolR64Effect 0x10032a 4 10 44) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (b_l1002a0_2)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0_1 : List UInt8 :=
  [0x4C, 0x21, 0xFE, 0x48, 0xBD, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x49, 0x21, 0xEC,
    0x49, 0x09, 0xF4, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xC6, 0x2C, 0x4C, 0x21, 0xFE, 0x4C, 0x89, 0xC0,
    0x48, 0xC1, 0xC0, 0x3C, 0x48, 0x21, 0xE8, 0x48, 0x09, 0xF0, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x89,
    0xCE, 0x48, 0xC1, 0xC6, 0x2C, 0x4C, 0x21, 0xFE, 0x4C, 0x89, 0xC8, 0x48, 0xC1, 0xC0, 0x3C, 0x48,
    0x21, 0xE8, 0x49, 0x89, 0xFA, 0x49, 0xC1, 0xC2, 0x2C] ++ bytes_l1002a0_2

theorem code_l1002a0_1 : ∀ x ∈ codeRange 0x1002e5 bytes_l1002a0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2e5 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_2

@[cfg_block] def b_l1002a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1002a0 (pushR64Effect 0x1002a0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1002a0 (PushPre 0x1002a0 1) (pushR64Effect 0x1002a0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1002a1 (pushR64Effect 0x1002a1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1002a1 (PushPre 0x1002a1 2) (pushR64Effect 0x1002a1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1002a3 (pushR64Effect 0x1002a3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1002a3 (PushPre 0x1002a3 2) (pushR64Effect 0x1002a3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1002a5 (pushR64Effect 0x1002a5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1002a5 (PushPre 0x1002a5 2) (pushR64Effect 0x1002a5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1002a7 (pushR64Effect 0x1002a7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1002a7 (PushPre 0x1002a7 2) (pushR64Effect 0x1002a7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1002a9 (pushR64Effect 0x1002a9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1002a9 (PushPre 0x1002a9 1) (pushR64Effect 0x1002a9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1002aa (subR64Imm8Effect 0x1002aa 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1002aa (fun s => s.RIP = 0x1002aa) (subR64Imm8Effect 0x1002aa 4 0x30) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1002ae (movR64R64Effect 0x1002ae 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 68) (.exec 0x1002ae (fun s => s.RIP = 0x1002ae) (movR64R64Effect 0x1002ae 1 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x1002b1 (movR64M64Effect 0x1002b1 2 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 70) (.exec 0x1002b1 (LoadPre 0x1002b1 (fun s => AddrMode.addr (.base 7 .none) s (0x1002b1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1002b1 2 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x1002b4 (movR64M64Effect 0x1002b4 8 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 72) (.exec 0x1002b4 (LoadPre 0x1002b4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1002b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002b4 8 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x1002b8 (movR64M64Effect 0x1002b8 9 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 74) (.exec 0x1002b8 (LoadPre 0x1002b8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1002b8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002b8 9 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x1002bc (movR64M64Effect 0x1002bc 7 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 76) (.exec 0x1002bc (LoadPre 0x1002bc (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1002bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002bc 7 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.out 0x1002c0 (movR64M64Effect 0x1002c0 11 (.base 1 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 78) (.exec 0x1002c0 (LoadPre 0x1002c0 (fun s => AddrMode.addr (.base 1 (.d8 0x20)) s (0x1002c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002c0 11 (.base 1 (.d8 0x20))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 79) (.out 0x1002c4 (movR64M64Effect 0x1002c4 14 (.base 1 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 80) (.exec 0x1002c4 (LoadPre 0x1002c4 (fun s => AddrMode.addr (.base 1 (.d8 0x28)) s (0x1002c4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002c4 14 (.base 1 (.d8 0x28))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 81) (.exec 0x1002c8 (StorePre 0x1002c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1002c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002c8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 65]
    (.letOp (n := 82) (.out 0x1002cd (movR64R64Effect 0x1002cd 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 83) (.exec 0x1002cd (fun s => s.RIP = 0x1002cd) (movR64R64Effect 0x1002cd 6 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 84) (.out 0x1002d0 (rolR64Effect 0x1002d0 4 6 44) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[82]
    (.letOp (n := 85) (.exec 0x1002d0 (fun s => s.RIP = 0x1002d0) (rolR64Effect 0x1002d0 4 6 44) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (.letOp (n := 86) (.out 0x1002d4 (movR64Imm64Effect 0x1002d4 15 0xfff0fff0fff0fff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 87) (.exec 0x1002d4 (fun s => s.RIP = 0x1002d4) (movR64Imm64Effect 0x1002d4 15 0xfff0fff0fff0fff) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x1002de (movR64R64Effect 0x1002de 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[69]
    (.letOp (n := 89) (.exec 0x1002de (fun s => s.RIP = 0x1002de) (movR64R64Effect 0x1002de 12 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 90) (.out 0x1002e1 (rolR64Effect 0x1002e1 4 12 60) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[88]
    (.letOp (n := 91) (.exec 0x1002e1 (fun s => s.RIP = 0x1002e1) (rolR64Effect 0x1002e1 4 12 60) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (b_l1002a0_1)))))))))))))))))))))))))))))))))))))))

def bytes_l1002a0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89,
    0xF9, 0x48, 0x8B, 0x17, 0x4C, 0x8B, 0x47, 0x08, 0x4C, 0x8B, 0x4F, 0x10, 0x48, 0x8B, 0x7F, 0x18,
    0x4C, 0x8B, 0x59, 0x20, 0x4C, 0x8B, 0x71, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0xD6,
    0x48, 0xC1, 0xC6, 0x2C, 0x49, 0xBF, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0x49, 0x89,
    0xD4, 0x49, 0xC1, 0xC4, 0x3C] ++ bytes_l1002a0_1

theorem code_l1002a0 : ∀ x ∈ codeRange 0x1002a0 bytes_l1002a0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2a0 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1002a0_1

@[cfg_block] def b_l100580_8 : Block Op Label signature Reg.count 363 :=
  .letOp (n := 363) (.exec 0x1007e9 (StorePre 0x1007e9 4 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x1007e9 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1007e9 4 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[361, 7]
    (.letOp (n := 364) (.out 0x1007ed (movR32R32Effect 0x1007ed 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[209]
    (.letOp (n := 365) (.exec 0x1007ed (fun s => s.RIP = 0x1007ed) (movR32R32Effect 0x1007ed 3 0 11) (Reg.operands [.gpr 11] [])) #v[209]
    (.letOp (n := 366) (.out 0x1007f0 (rolR16Effect 0x1007f0 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 367) (.exec 0x1007f0 (fun s => s.RIP = 0x1007f0) (rolR16Effect 0x1007f0 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[364]
    (.letOp (n := 368) (.out 0x1007f4 (andEaxImm32Effect 0x1007f4 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[366]
    (.letOp (n := 369) (.exec 0x1007f4 (fun s => s.RIP = 0x1007f4) (andEaxImm32Effect 0x1007f4 0x3333) (Reg.operands [.gpr 0] [])) #v[366]
    (.letOp (n := 370) (.out 0x1007f9 (rolR16Effect 0x1007f9 5 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[209]
    (.letOp (n := 371) (.exec 0x1007f9 (fun s => s.RIP = 0x1007f9) (rolR16Effect 0x1007f9 5 11 10) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[209]
    (.letOp (n := 372) (.out 0x1007fe (andR32Imm32Effect 0x1007fe 7 11 0xffffcccc) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[370]
    (.letOp (n := 373) (.exec 0x1007fe (fun s => s.RIP = 0x1007fe) (andR32Imm32Effect 0x1007fe 7 11 0xffffcccc) (Reg.operands [.gpr 11] [])) #v[370]
    (.letOp (n := 374) (.out 0x100805 (orR32R32Effect 0x100805 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[372, 368]
    (.letOp (n := 375) (.exec 0x100805 (fun s => s.RIP = 0x100805) (orR32R32Effect 0x100805 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[372, 368]
    (.letOp (n := 376) (.out 0x100808 (movR32R32Effect 0x100808 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[338]
    (.letOp (n := 377) (.exec 0x100808 (fun s => s.RIP = 0x100808) (movR32R32Effect 0x100808 2 0 2) (Reg.operands [.gpr 2] [])) #v[338]
    (.letOp (n := 378) (.out 0x10080a (xorR32R32Effect 0x10080a 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[376, 191]
    (.letOp (n := 379) (.exec 0x10080a (fun s => s.RIP = 0x10080a) (xorR32R32Effect 0x10080a 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[376, 191]
    (.letOp (n := 380) (.out 0x10080c (xorR32R32Effect 0x10080c 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[378, 374]
    (.letOp (n := 381) (.exec 0x10080c (fun s => s.RIP = 0x10080c) (xorR32R32Effect 0x10080c 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[378, 374]
    (.letOp (n := 382) (.exec 0x10080f (StorePre 0x10080f 4 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10080f + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10080f 4 0 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[380, 7]
    (.letOp (n := 383) (.out 0x100813 (addR64Imm8Effect 0x100813 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 384) (.exec 0x100813 (fun s => s.RIP = 0x100813) (addR64Imm8Effect 0x100813 4 0x10) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 385) (.out 0x100817 (popR64Effect 0x100817 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[383]
    (.letOp (n := 386) (.out 0x100817 (popR64Effect 0x100817 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[383]
    (.letOp (n := 387) (.exec 0x100817 (PopPre 0x100817) (popR64Effect 0x100817 1 3) (Reg.operands [.gpr 4] [])) #v[383]
    (.letOp (n := 388) (.out 0x100818 (popR64Effect 0x100818 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[386]
    (.letOp (n := 389) (.out 0x100818 (popR64Effect 0x100818 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[386]
    (.letOp (n := 390) (.exec 0x100818 (PopPre 0x100818) (popR64Effect 0x100818 2 12) (Reg.operands [.gpr 4] [])) #v[386]
    (.letOp (n := 391) (.out 0x10081a (popR64Effect 0x10081a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[389]
    (.letOp (n := 392) (.out 0x10081a (popR64Effect 0x10081a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[389]
    (.letOp (n := 393) (.exec 0x10081a (PopPre 0x10081a) (popR64Effect 0x10081a 2 13) (Reg.operands [.gpr 4] [])) #v[389]
    (.letOp (n := 394) (.out 0x10081c (popR64Effect 0x10081c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[392]
    (.letOp (n := 395) (.out 0x10081c (popR64Effect 0x10081c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[392]
    (.letOp (n := 396) (.exec 0x10081c (PopPre 0x10081c) (popR64Effect 0x10081c 2 14) (Reg.operands [.gpr 4] [])) #v[392]
    (.letOp (n := 397) (.out 0x10081e (popR64Effect 0x10081e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[395]
    (.letOp (n := 398) (.out 0x10081e (popR64Effect 0x10081e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[395]
    (.letOp (n := 399) (.exec 0x10081e (PopPre 0x10081e) (popR64Effect 0x10081e 2 15) (Reg.operands [.gpr 4] [])) #v[395]
    (.letOp (n := 400) (.out 0x100820 (popR64Effect 0x100820 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[398]
    (.letOp (n := 401) (.out 0x100820 (popR64Effect 0x100820 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[398]
    (.letOp (n := 402) (.exec 0x100820 (PopPre 0x100820) (popR64Effect 0x100820 1 5) (Reg.operands [.gpr 4] [])) #v[398]
    (.letOp (n := 403) (.out 0x100821 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[401]
    (.letOp (n := 404) (.out 0x100821 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[401]
    (.letOp (n := 405) (.exec 0x100821 (RetPre 0x100821) (retEffect) (Reg.operands [.gpr 4] [])) #v[401]
    (.terminate (.ret (RegMap.args [(0, 380), (1, 355), (2, 338), (3, 385), (4, 404), (5, 400), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 394), (15, 397), (22, 22), (39, 39), (50, 50), (51, 51)] 406) (some ⟨403, by decide⟩)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l100580_8 : List UInt8 :=
  [0x66, 0x89, 0x47, 0x0C, 0x44, 0x89, 0xD8, 0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00,
    0x66, 0x41, 0xC1, 0xC3, 0x0A, 0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x09, 0xC3, 0x89,
    0xD0, 0x31, 0xE8, 0x44, 0x31, 0xD8, 0x66, 0x89, 0x47, 0x0E, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41,
    0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l100580_8 : ∀ x ∈ codeRange 0x1007e9 bytes_l100580_8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7e9 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100580_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x1007a5 (rolR16Effect 0x1007a5 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[320]
    (.letOp (n := 325) (.exec 0x1007a5 (fun s => s.RIP = 0x1007a5) (rolR16Effect 0x1007a5 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[320]
    (.letOp (n := 326) (.out 0x1007a9 (andR32Imm32Effect 0x1007a9 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[324]
    (.letOp (n := 327) (.exec 0x1007a9 (fun s => s.RIP = 0x1007a9) (andR32Imm32Effect 0x1007a9 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[324]
    (.letOp (n := 328) (.out 0x1007af (orR32R32Effect 0x1007af 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[326, 318]
    (.letOp (n := 329) (.exec 0x1007af (fun s => s.RIP = 0x1007af) (orR32R32Effect 0x1007af 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[326, 318]
    (.letOp (n := 330) (.out 0x1007b1 (movR32R32Effect 0x1007b1 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 331) (.exec 0x1007b1 (fun s => s.RIP = 0x1007b1) (movR32R32Effect 0x1007b1 3 0 8) (Reg.operands [.gpr 8] [])) #v[293]
    (.letOp (n := 332) (.out 0x1007b4 (xorR32R32Effect 0x1007b4 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[330, 161]
    (.letOp (n := 333) (.exec 0x1007b4 (fun s => s.RIP = 0x1007b4) (xorR32R32Effect 0x1007b4 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[330, 161]
    (.letOp (n := 334) (.out 0x1007b7 (movR32M32LowEffect 0x1007b7 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 335) (.exec 0x1007b7 (LoadPre 0x1007b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1007b7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1007b7 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 336) (.out 0x1007bb (movR32M32Effect 0x1007bb 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 337) (.exec 0x1007bb (LoadPre 0x1007bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1007bb + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1007bb 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 338) (.out 0x1007c0 (xorR32R32Effect 0x1007c0 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[334, 336]
    (.letOp (n := 339) (.exec 0x1007c0 (fun s => s.RIP = 0x1007c0) (xorR32R32Effect 0x1007c0 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[334, 336]
    (.letOp (n := 340) (.out 0x1007c3 (xorR32R32Effect 0x1007c3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[332, 328]
    (.letOp (n := 341) (.exec 0x1007c3 (fun s => s.RIP = 0x1007c3) (xorR32R32Effect 0x1007c3 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[332, 328]
    (.letOp (n := 342) (.exec 0x1007c5 (StorePre 0x1007c5 4 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x1007c5 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1007c5 4 0 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[340, 7]
    (.letOp (n := 343) (.out 0x1007c9 (movR32R32Effect 0x1007c9 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[338]
    (.letOp (n := 344) (.exec 0x1007c9 (fun s => s.RIP = 0x1007c9) (movR32R32Effect 0x1007c9 2 0 2) (Reg.operands [.gpr 2] [])) #v[338]
    (.letOp (n := 345) (.out 0x1007cb (rolR16Effect 0x1007cb 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[343]
    (.letOp (n := 346) (.exec 0x1007cb (fun s => s.RIP = 0x1007cb) (rolR16Effect 0x1007cb 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[343]
    (.letOp (n := 347) (.out 0x1007cf (andEaxImm32Effect 0x1007cf 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[345]
    (.letOp (n := 348) (.exec 0x1007cf (fun s => s.RIP = 0x1007cf) (andEaxImm32Effect 0x1007cf 0x3333) (Reg.operands [.gpr 0] [])) #v[345]
    (.letOp (n := 349) (.out 0x1007d4 (movR32R32Effect 0x1007d4 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[338]
    (.letOp (n := 350) (.exec 0x1007d4 (fun s => s.RIP = 0x1007d4) (movR32R32Effect 0x1007d4 2 1 2) (Reg.operands [.gpr 2] [])) #v[338]
    (.letOp (n := 351) (.out 0x1007d6 (rolR16Effect 0x1007d6 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[349]
    (.letOp (n := 352) (.exec 0x1007d6 (fun s => s.RIP = 0x1007d6) (rolR16Effect 0x1007d6 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[349]
    (.letOp (n := 353) (.out 0x1007da (andR32Imm32Effect 0x1007da 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[351]
    (.letOp (n := 354) (.exec 0x1007da (fun s => s.RIP = 0x1007da) (andR32Imm32Effect 0x1007da 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[351]
    (.letOp (n := 355) (.out 0x1007e0 (orR32R32Effect 0x1007e0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[353, 347]
    (.letOp (n := 356) (.exec 0x1007e0 (fun s => s.RIP = 0x1007e0) (orR32R32Effect 0x1007e0 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[353, 347]
    (.letOp (n := 357) (.out 0x1007e2 (movR32R32Effect 0x1007e2 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[322]
    (.letOp (n := 358) (.exec 0x1007e2 (fun s => s.RIP = 0x1007e2) (movR32R32Effect 0x1007e2 2 0 6) (Reg.operands [.gpr 6] [])) #v[322]
    (.letOp (n := 359) (.out 0x1007e4 (xorR32R32Effect 0x1007e4 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[357, 336]
    (.letOp (n := 360) (.exec 0x1007e4 (fun s => s.RIP = 0x1007e4) (xorR32R32Effect 0x1007e4 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[357, 336]
    (.letOp (n := 361) (.out 0x1007e7 (xorR32R32Effect 0x1007e7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[359, 355]
    (.letOp (n := 362) (.exec 0x1007e7 (fun s => s.RIP = 0x1007e7) (xorR32R32Effect 0x1007e7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[359, 355]
    (b_l100580_8)))))))))))))))))))))))))))))))))))))))

def bytes_l100580_7 : List UInt8 :=
  [0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC1, 0x44, 0x89, 0xC0, 0x44,
    0x31, 0xF0, 0x8B, 0x54, 0x24, 0x0C, 0x44, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x31, 0xC2, 0x31, 0xC8,
    0x66, 0x89, 0x47, 0x0A, 0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x89,
    0xD1, 0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC1, 0x89, 0xF0, 0x44,
    0x31, 0xC0, 0x31, 0xC8] ++ bytes_l100580_8

theorem code_l100580_7 : ∀ x ∈ codeRange 0x1007a5 bytes_l100580_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7a5 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_8

@[cfg_block] def b_l100580_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x100762 (movR32R32Effect 0x100762 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[280]
    (.letOp (n := 287) (.exec 0x100762 (fun s => s.RIP = 0x100762) (movR32R32Effect 0x100762 2 0 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 288) (.out 0x100764 (rolR16Effect 0x100764 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[286]
    (.letOp (n := 289) (.exec 0x100764 (fun s => s.RIP = 0x100764) (rolR16Effect 0x100764 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[286]
    (.letOp (n := 290) (.exec 0x100768 (StorePre 0x100768 5 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x100768 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100768 5 8 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[284, 7]
    (.letOp (n := 291) (.out 0x10076d (movR32R32Effect 0x10076d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[280]
    (.letOp (n := 292) (.exec 0x10076d (fun s => s.RIP = 0x10076d) (movR32R32Effect 0x10076d 2 1 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 293) (.out 0x10076f (movR32R32Effect 0x10076f 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[280]
    (.letOp (n := 294) (.exec 0x10076f (fun s => s.RIP = 0x10076f) (movR32R32Effect 0x10076f 3 8 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 295) (.out 0x100772 (rolR16Effect 0x100772 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[291]
    (.letOp (n := 296) (.exec 0x100772 (fun s => s.RIP = 0x100772) (rolR16Effect 0x100772 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[291]
    (.letOp (n := 297) (.out 0x100776 (andEaxImm32Effect 0x100776 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[288]
    (.letOp (n := 298) (.exec 0x100776 (fun s => s.RIP = 0x100776) (andEaxImm32Effect 0x100776 0x3333) (Reg.operands [.gpr 0] [])) #v[288]
    (.letOp (n := 299) (.out 0x10077b (andR32Imm32Effect 0x10077b 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[295]
    (.letOp (n := 300) (.exec 0x10077b (fun s => s.RIP = 0x10077b) (andR32Imm32Effect 0x10077b 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[295]
    (.letOp (n := 301) (.out 0x100781 (orR32R32Effect 0x100781 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[299, 297]
    (.letOp (n := 302) (.exec 0x100781 (fun s => s.RIP = 0x100781) (orR32R32Effect 0x100781 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[299, 297]
    (.letOp (n := 303) (.out 0x100783 (xorR32R32Effect 0x100783 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[257, 153]
    (.letOp (n := 304) (.exec 0x100783 (fun s => s.RIP = 0x100783) (xorR32R32Effect 0x100783 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[257, 153]
    (.letOp (n := 305) (.out 0x100786 (movR32M32LowEffect 0x100786 2 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 306) (.exec 0x100786 (LoadPre 0x100786 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100786 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100786 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 307) (.out 0x10078a (xorR32R32Effect 0x10078a 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[305, 161]
    (.letOp (n := 308) (.exec 0x10078a (fun s => s.RIP = 0x10078a) (xorR32R32Effect 0x10078a 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[305, 161]
    (.letOp (n := 309) (.out 0x10078d (xorR32R32Effect 0x10078d 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[303, 209]
    (.letOp (n := 310) (.exec 0x10078d (fun s => s.RIP = 0x10078d) (xorR32R32Effect 0x10078d 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[303, 209]
    (.letOp (n := 311) (.out 0x100790 (xorR32R32Effect 0x100790 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[309, 301]
    (.letOp (n := 312) (.exec 0x100790 (fun s => s.RIP = 0x100790) (xorR32R32Effect 0x100790 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[309, 301]
    (.letOp (n := 313) (.exec 0x100792 (StorePre 0x100792 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100792 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100792 4 6 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[311, 7]
    (.letOp (n := 314) (.out 0x100796 (movR32R32Effect 0x100796 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[307]
    (.letOp (n := 315) (.exec 0x100796 (fun s => s.RIP = 0x100796) (movR32R32Effect 0x100796 2 0 2) (Reg.operands [.gpr 2] [])) #v[307]
    (.letOp (n := 316) (.out 0x100798 (rolR16Effect 0x100798 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[314]
    (.letOp (n := 317) (.exec 0x100798 (fun s => s.RIP = 0x100798) (rolR16Effect 0x100798 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[314]
    (.letOp (n := 318) (.out 0x10079c (andEaxImm32Effect 0x10079c 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[316]
    (.letOp (n := 319) (.exec 0x10079c (fun s => s.RIP = 0x10079c) (andEaxImm32Effect 0x10079c 0x3333) (Reg.operands [.gpr 0] [])) #v[316]
    (.letOp (n := 320) (.out 0x1007a1 (movR32R32Effect 0x1007a1 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[307]
    (.letOp (n := 321) (.exec 0x1007a1 (fun s => s.RIP = 0x1007a1) (movR32R32Effect 0x1007a1 2 1 2) (Reg.operands [.gpr 2] [])) #v[307]
    (.letOp (n := 322) (.out 0x1007a3 (movR32R32Effect 0x1007a3 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[307]
    (.letOp (n := 323) (.exec 0x1007a3 (fun s => s.RIP = 0x1007a3) (movR32R32Effect 0x1007a3 2 6 2) (Reg.operands [.gpr 2] [])) #v[307]
    (b_l100580_7))))))))))))))))))))))))))))))))))))))

def bytes_l100580_6 : List UInt8 :=
  [0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x06, 0x66, 0x44, 0x89, 0x47, 0x06, 0x89, 0xD1, 0x41, 0x89, 0xD0,
    0x66, 0xC1, 0xC1, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09,
    0xC1, 0x44, 0x31, 0xFE, 0x8B, 0x54, 0x24, 0x04, 0x44, 0x31, 0xF2, 0x44, 0x31, 0xDE, 0x31, 0xCE,
    0x66, 0x89, 0x77, 0x08, 0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x89,
    0xD1, 0x89, 0xD6] ++ bytes_l100580_7

theorem code_l100580_6 : ∀ x ∈ codeRange 0x100762 bytes_l100580_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x762 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_7

@[cfg_block] def b_l100580_5 : Block Op Label signature Reg.count 247 :=
  .letOp (n := 247) (.out 0x10071f (movR32R32Effect 0x10071f 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[238]
    (.letOp (n := 248) (.exec 0x10071f (fun s => s.RIP = 0x10071f) (movR32R32Effect 0x10071f 3 1 8) (Reg.operands [.gpr 8] [])) #v[238]
    (.letOp (n := 249) (.out 0x100722 (rolR16Effect 0x100722 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[247]
    (.letOp (n := 250) (.exec 0x100722 (fun s => s.RIP = 0x100722) (rolR16Effect 0x100722 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 251) (.out 0x100726 (andR32Imm32Effect 0x100726 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[249]
    (.letOp (n := 252) (.exec 0x100726 (fun s => s.RIP = 0x100726) (andR32Imm32Effect 0x100726 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[249]
    (.letOp (n := 253) (.out 0x10072c (orR32R32Effect 0x10072c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[251, 245]
    (.letOp (n := 254) (.exec 0x10072c (fun s => s.RIP = 0x10072c) (orR32R32Effect 0x10072c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[251, 245]
    (.letOp (n := 255) (.out 0x10072e (xorR32R32Effect 0x10072e 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[216, 121]
    (.letOp (n := 256) (.exec 0x10072e (fun s => s.RIP = 0x10072e) (xorR32R32Effect 0x10072e 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[216, 121]
    (.letOp (n := 257) (.out 0x100731 (xorR32R32Effect 0x100731 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[73, 135]
    (.letOp (n := 258) (.exec 0x100731 (fun s => s.RIP = 0x100731) (xorR32R32Effect 0x100731 3 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[73, 135]
    (.letOp (n := 259) (.out 0x100734 (xorR32R32Effect 0x100734 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[255, 253]
    (.letOp (n := 260) (.exec 0x100734 (fun s => s.RIP = 0x100734) (xorR32R32Effect 0x100734 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[255, 253]
    (.letOp (n := 261) (.exec 0x100736 (StorePre 0x100736 4 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x100736 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100736 4 2 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[259, 7]
    (.letOp (n := 262) (.out 0x10073a (movR32R32Effect 0x10073a 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[257]
    (.letOp (n := 263) (.exec 0x10073a (fun s => s.RIP = 0x10073a) (movR32R32Effect 0x10073a 2 0 6) (Reg.operands [.gpr 6] [])) #v[257]
    (.letOp (n := 264) (.out 0x10073c (rolR16Effect 0x10073c 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[262]
    (.letOp (n := 265) (.exec 0x10073c (fun s => s.RIP = 0x10073c) (rolR16Effect 0x10073c 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[262]
    (.letOp (n := 266) (.out 0x100740 (andEaxImm32Effect 0x100740 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[264]
    (.letOp (n := 267) (.exec 0x100740 (fun s => s.RIP = 0x100740) (andEaxImm32Effect 0x100740 0x3333) (Reg.operands [.gpr 0] [])) #v[264]
    (.letOp (n := 268) (.out 0x100745 (movR32R32Effect 0x100745 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[257]
    (.letOp (n := 269) (.exec 0x100745 (fun s => s.RIP = 0x100745) (movR32R32Effect 0x100745 2 1 6) (Reg.operands [.gpr 6] [])) #v[257]
    (.letOp (n := 270) (.out 0x100747 (rolR16Effect 0x100747 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[268]
    (.letOp (n := 271) (.exec 0x100747 (fun s => s.RIP = 0x100747) (rolR16Effect 0x100747 4 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[268]
    (.letOp (n := 272) (.out 0x10074b (andR32Imm32Effect 0x10074b 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[270]
    (.letOp (n := 273) (.exec 0x10074b (fun s => s.RIP = 0x10074b) (andR32Imm32Effect 0x10074b 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[270]
    (.letOp (n := 274) (.out 0x100751 (orR32R32Effect 0x100751 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[272, 266]
    (.letOp (n := 275) (.exec 0x100751 (fun s => s.RIP = 0x100751) (orR32R32Effect 0x100751 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[272, 266]
    (.letOp (n := 276) (.out 0x100753 (xorR32R32Effect 0x100753 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[238, 135]
    (.letOp (n := 277) (.exec 0x100753 (fun s => s.RIP = 0x100753) (xorR32R32Effect 0x100753 3 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[238, 135]
    (.letOp (n := 278) (.out 0x100756 (movR32M32LowEffect 0x100756 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 279) (.exec 0x100756 (LoadPre 0x100756 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100756 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100756 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 280) (.out 0x100759 (xorR32R32Effect 0x100759 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[278, 153]
    (.letOp (n := 281) (.exec 0x100759 (fun s => s.RIP = 0x100759) (xorR32R32Effect 0x100759 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[278, 153]
    (.letOp (n := 282) (.out 0x10075c (xorR32R32Effect 0x10075c 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[276, 209]
    (.letOp (n := 283) (.exec 0x10075c (fun s => s.RIP = 0x10075c) (xorR32R32Effect 0x10075c 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[276, 209]
    (.letOp (n := 284) (.out 0x10075f (xorR32R32Effect 0x10075f 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[282, 274]
    (.letOp (n := 285) (.exec 0x10075f (fun s => s.RIP = 0x10075f) (xorR32R32Effect 0x10075f 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[282, 274]
    (b_l100580_6)))))))))))))))))))))))))))))))))))))))

def bytes_l100580_5 : List UInt8 :=
  [0x44, 0x89, 0xC1, 0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC1, 0x44,
    0x31, 0xEA, 0x44, 0x31, 0xE6, 0x31, 0xCA, 0x66, 0x89, 0x57, 0x04, 0x89, 0xF0, 0x66, 0xC1, 0xC0,
    0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x89, 0xF1, 0x66, 0xC1, 0xC1, 0x0A, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x09, 0xC1, 0x45, 0x31, 0xE0, 0x8B, 0x14, 0x24, 0x44, 0x31, 0xFA, 0x45, 0x31, 0xD8,
    0x41, 0x31, 0xC8] ++ bytes_l100580_6

theorem code_l100580_5 : ∀ x ∈ codeRange 0x10071f bytes_l100580_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x71f 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_6

@[cfg_block] def b_l100580_4 : Block Op Label signature Reg.count 209 :=
  .letOp (n := 209) (.out 0x1006d8 (xorR32R32Effect 0x1006d8 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[177, 191]
    (.letOp (n := 210) (.exec 0x1006d8 (fun s => s.RIP = 0x1006d8) (xorR32R32Effect 0x1006d8 3 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[177, 191]
    (.letOp (n := 211) (.out 0x1006db (xorR32R32Effect 0x1006db 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[97, 209]
    (.letOp (n := 212) (.exec 0x1006db (fun s => s.RIP = 0x1006db) (xorR32R32Effect 0x1006db 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[97, 209]
    (.letOp (n := 213) (.out 0x1006de (xorR32R32Effect 0x1006de 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[211, 207]
    (.letOp (n := 214) (.exec 0x1006de (fun s => s.RIP = 0x1006de) (xorR32R32Effect 0x1006de 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[211, 207]
    (.letOp (n := 215) (.exec 0x1006e0 (StorePre 0x1006e0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1006e0 + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x1006e0 3 3 (.base 7 .none)) (Reg.operands [.gpr 3, .gpr 7] [])) #v[213, 7]
    (.letOp (n := 216) (.out 0x1006e3 (xorR32R32Effect 0x1006e3 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[69, 107]
    (.letOp (n := 217) (.exec 0x1006e3 (fun s => s.RIP = 0x1006e3) (xorR32R32Effect 0x1006e3 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[69, 107]
    (.letOp (n := 218) (.out 0x1006e6 (movR32R32Effect 0x1006e6 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[216]
    (.letOp (n := 219) (.exec 0x1006e6 (fun s => s.RIP = 0x1006e6) (movR32R32Effect 0x1006e6 2 0 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 220) (.out 0x1006e8 (rolR16Effect 0x1006e8 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[218]
    (.letOp (n := 221) (.exec 0x1006e8 (fun s => s.RIP = 0x1006e8) (rolR16Effect 0x1006e8 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[218]
    (.letOp (n := 222) (.out 0x1006ec (andEaxImm32Effect 0x1006ec 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[220]
    (.letOp (n := 223) (.exec 0x1006ec (fun s => s.RIP = 0x1006ec) (andEaxImm32Effect 0x1006ec 0x3333) (Reg.operands [.gpr 0] [])) #v[220]
    (.letOp (n := 224) (.out 0x1006f1 (movR32R32Effect 0x1006f1 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[216]
    (.letOp (n := 225) (.exec 0x1006f1 (fun s => s.RIP = 0x1006f1) (movR32R32Effect 0x1006f1 3 10 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 226) (.out 0x1006f4 (rolR16Effect 0x1006f4 5 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[224]
    (.letOp (n := 227) (.exec 0x1006f4 (fun s => s.RIP = 0x1006f4) (rolR16Effect 0x1006f4 5 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[224]
    (.letOp (n := 228) (.out 0x1006f9 (andR32Imm32Effect 0x1006f9 7 10 0xffffcccc) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[226]
    (.letOp (n := 229) (.exec 0x1006f9 (fun s => s.RIP = 0x1006f9) (andR32Imm32Effect 0x1006f9 7 10 0xffffcccc) (Reg.operands [.gpr 10] [])) #v[226]
    (.letOp (n := 230) (.out 0x100700 (orR32R32Effect 0x100700 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[228, 222]
    (.letOp (n := 231) (.exec 0x100700 (fun s => s.RIP = 0x100700) (orR32R32Effect 0x100700 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[228, 222]
    (.letOp (n := 232) (.out 0x100703 (xorR32R32Effect 0x100703 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[193, 107]
    (.letOp (n := 233) (.exec 0x100703 (fun s => s.RIP = 0x100703) (xorR32R32Effect 0x100703 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[193, 107]
    (.letOp (n := 234) (.out 0x100706 (xorR32R32Effect 0x100706 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[232, 209]
    (.letOp (n := 235) (.exec 0x100706 (fun s => s.RIP = 0x100706) (xorR32R32Effect 0x100706 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[232, 209]
    (.letOp (n := 236) (.out 0x100709 (xorR32R32Effect 0x100709 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[234, 230]
    (.letOp (n := 237) (.exec 0x100709 (fun s => s.RIP = 0x100709) (xorR32R32Effect 0x100709 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[234, 230]
    (.letOp (n := 238) (.out 0x10070c (xorR32R32Effect 0x10070c 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[71, 121]
    (.letOp (n := 239) (.exec 0x10070c (fun s => s.RIP = 0x10070c) (xorR32R32Effect 0x10070c 3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[71, 121]
    (.letOp (n := 240) (.exec 0x10070f (StorePre 0x10070f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x10070f + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10070f 4 1 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[236, 7]
    (.letOp (n := 241) (.out 0x100713 (movR32R32Effect 0x100713 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[238]
    (.letOp (n := 242) (.exec 0x100713 (fun s => s.RIP = 0x100713) (movR32R32Effect 0x100713 3 0 8) (Reg.operands [.gpr 8] [])) #v[238]
    (.letOp (n := 243) (.out 0x100716 (rolR16Effect 0x100716 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[241]
    (.letOp (n := 244) (.exec 0x100716 (fun s => s.RIP = 0x100716) (rolR16Effect 0x100716 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[241]
    (.letOp (n := 245) (.out 0x10071a (andEaxImm32Effect 0x10071a 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[243]
    (.letOp (n := 246) (.exec 0x10071a (fun s => s.RIP = 0x10071a) (andEaxImm32Effect 0x10071a 0x3333) (Reg.operands [.gpr 0] [])) #v[243]
    (b_l100580_5))))))))))))))))))))))))))))))))))))))

def bytes_l100580_4 : List UInt8 :=
  [0x41, 0x31, 0xEB, 0x44, 0x31, 0xDB, 0x31, 0xC3, 0x66, 0x89, 0x1F, 0x44, 0x31, 0xCA, 0x89, 0xD0,
    0x66, 0xC1, 0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00, 0x41, 0x89, 0xD2, 0x66, 0x41, 0xC1, 0xC2,
    0x0A, 0x41, 0x81, 0xE2, 0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x09, 0xC2, 0x44, 0x31, 0xC9, 0x44, 0x31,
    0xD9, 0x44, 0x31, 0xD1, 0x45, 0x31, 0xE8, 0x66, 0x89, 0x4F, 0x02, 0x44, 0x89, 0xC0, 0x66, 0xC1,
    0xC0, 0x06, 0x25, 0x33, 0x33, 0x00, 0x00] ++ bytes_l100580_5

theorem code_l100580_4 : ∀ x ∈ codeRange 0x1006d8 bytes_l100580_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6d8 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_5

@[cfg_block] def b_l100580_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x100685 (rolR16Effect 0x100685 4 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 171) (.exec 0x100685 (fun s => s.RIP = 0x100685) (rolR16Effect 0x100685 4 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 172) (.out 0x100689 (andEaxImm32Effect 0x100689 0xffffeeee) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[170]
    (.letOp (n := 173) (.exec 0x100689 (fun s => s.RIP = 0x100689) (andEaxImm32Effect 0x100689 0xffffeeee) (Reg.operands [.gpr 0] [])) #v[170]
    (.letOp (n := 174) (.out 0x10068e (orR32R32Effect 0x10068e 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[172, 168]
    (.letOp (n := 175) (.exec 0x10068e (fun s => s.RIP = 0x10068e) (orR32R32Effect 0x10068e 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[172, 168]
    (.letOp (n := 176) (.exec 0x100691 (StorePre 0x100691 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100691 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100691 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[174, 65]
    (.letOp (n := 177) (.out 0x100695 (movzxR32M16Effect 0x100695 5 11 (.base 7 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7]
    (.letOp (n := 178) (.exec 0x100695 (LoadPre 0x100695 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x100695 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100695 5 11 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 179) (.out 0x10069a (movR32R32Effect 0x10069a 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[177]
    (.letOp (n := 180) (.exec 0x10069a (fun s => s.RIP = 0x10069a) (movR32R32Effect 0x10069a 3 10 11) (Reg.operands [.gpr 11] [])) #v[177]
    (.letOp (n := 181) (.out 0x10069d (rolR16Effect 0x10069d 5 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[179]
    (.letOp (n := 182) (.exec 0x10069d (fun s => s.RIP = 0x10069d) (rolR16Effect 0x10069d 5 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x1006a2 (andR32Imm32Effect 0x1006a2 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[181]
    (.letOp (n := 184) (.exec 0x1006a2 (fun s => s.RIP = 0x1006a2) (andR32Imm32Effect 0x1006a2 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[181]
    (.letOp (n := 185) (.out 0x1006a9 (movR32R32Effect 0x1006a9 3 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 11] []) (.reg (.gpr 5))) #v[177]
    (.letOp (n := 186) (.exec 0x1006a9 (fun s => s.RIP = 0x1006a9) (movR32R32Effect 0x1006a9 3 5 11) (Reg.operands [.gpr 11] [])) #v[177]
    (.letOp (n := 187) (.out 0x1006ac (rolR16Effect 0x1006ac 4 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[185]
    (.letOp (n := 188) (.exec 0x1006ac (fun s => s.RIP = 0x1006ac) (rolR16Effect 0x1006ac 4 5 13) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 189) (.out 0x1006b0 (andR32Imm32Effect 0x1006b0 6 5 0xffffeeee) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[187]
    (.letOp (n := 190) (.exec 0x1006b0 (fun s => s.RIP = 0x1006b0) (andR32Imm32Effect 0x1006b0 6 5 0xffffeeee) (Reg.operands [.gpr 5] [])) #v[187]
    (.letOp (n := 191) (.out 0x1006b6 (orR32R32Effect 0x1006b6 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[189, 183]
    (.letOp (n := 192) (.exec 0x1006b6 (fun s => s.RIP = 0x1006b6) (orR32R32Effect 0x1006b6 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[189, 183]
    (.letOp (n := 193) (.out 0x1006b9 (xorR32R32Effect 0x1006b9 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[67, 97]
    (.letOp (n := 194) (.exec 0x1006b9 (fun s => s.RIP = 0x1006b9) (xorR32R32Effect 0x1006b9 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[67, 97]
    (.letOp (n := 195) (.out 0x1006bb (movR32R32Effect 0x1006bb 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[193]
    (.letOp (n := 196) (.exec 0x1006bb (fun s => s.RIP = 0x1006bb) (movR32R32Effect 0x1006bb 3 10 1) (Reg.operands [.gpr 1] [])) #v[193]
    (.letOp (n := 197) (.out 0x1006be (rolR16Effect 0x1006be 5 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[195]
    (.letOp (n := 198) (.exec 0x1006be (fun s => s.RIP = 0x1006be) (rolR16Effect 0x1006be 5 10 6) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 199) (.out 0x1006c3 (andR32Imm32Effect 0x1006c3 7 10 0x3333) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[197]
    (.letOp (n := 200) (.exec 0x1006c3 (fun s => s.RIP = 0x1006c3) (andR32Imm32Effect 0x1006c3 7 10 0x3333) (Reg.operands [.gpr 10] [])) #v[197]
    (.letOp (n := 201) (.out 0x1006ca (movR32R32Effect 0x1006ca 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[193]
    (.letOp (n := 202) (.exec 0x1006ca (fun s => s.RIP = 0x1006ca) (movR32R32Effect 0x1006ca 2 0 1) (Reg.operands [.gpr 1] [])) #v[193]
    (.letOp (n := 203) (.out 0x1006cc (rolR16Effect 0x1006cc 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[201]
    (.letOp (n := 204) (.exec 0x1006cc (fun s => s.RIP = 0x1006cc) (rolR16Effect 0x1006cc 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[201]
    (.letOp (n := 205) (.out 0x1006d0 (andEaxImm32Effect 0x1006d0 0xffffcccc) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[203]
    (.letOp (n := 206) (.exec 0x1006d0 (fun s => s.RIP = 0x1006d0) (andEaxImm32Effect 0x1006d0 0xffffcccc) (Reg.operands [.gpr 0] [])) #v[203]
    (.letOp (n := 207) (.out 0x1006d5 (orR32R32Effect 0x1006d5 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[205, 199]
    (.letOp (n := 208) (.exec 0x1006d5 (fun s => s.RIP = 0x1006d5) (orR32R32Effect 0x1006d5 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[205, 199]
    (b_l100580_4)))))))))))))))))))))))))))))))))))))))

def bytes_l100580_3 : List UInt8 :=
  [0x66, 0xC1, 0xC0, 0x0D, 0x25, 0xEE, 0xEE, 0xFF, 0xFF, 0x44, 0x09, 0xD0, 0x89, 0x44, 0x24, 0x08,
    0x44, 0x0F, 0xB7, 0x5F, 0x0E, 0x45, 0x89, 0xDA, 0x66, 0x41, 0xC1, 0xC2, 0x09, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x44, 0x89, 0xDD, 0x66, 0xC1, 0xC5, 0x0D, 0x81, 0xE5, 0xEE, 0xEE, 0xFF,
    0xFF, 0x44, 0x09, 0xD5, 0x31, 0xD9, 0x41, 0x89, 0xCA, 0x66, 0x41, 0xC1, 0xC2, 0x06, 0x41, 0x81,
    0xE2, 0x33, 0x33, 0x00, 0x00, 0x89, 0xC8, 0x66, 0xC1, 0xC0, 0x0A, 0x25, 0xCC, 0xCC, 0xFF, 0xFF,
    0x44, 0x09, 0xD0] ++ bytes_l100580_4

theorem code_l100580_3 : ∀ x ∈ codeRange 0x100685 bytes_l100580_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x685 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_4

@[cfg_block] def b_l100580_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x100623 (andR32Imm32Effect 0x100623 7 12 0xffffeeee) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[131]
    (.letOp (n := 134) (.exec 0x100623 (fun s => s.RIP = 0x100623) (andR32Imm32Effect 0x100623 7 12 0xffffeeee) (Reg.operands [.gpr 12] [])) #v[131]
    (.letOp (n := 135) (.out 0x10062a (orR32R32Effect 0x10062a 3 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[133, 127]
    (.letOp (n := 136) (.exec 0x10062a (fun s => s.RIP = 0x10062a) (orR32R32Effect 0x10062a 3 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[133, 127]
    (.letOp (n := 137) (.exec 0x10062d (StorePre 0x10062d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10062d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10062d 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 138) (.out 0x100631 (movR32R32Effect 0x100631 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[75]
    (.letOp (n := 139) (.exec 0x100631 (fun s => s.RIP = 0x100631) (movR32R32Effect 0x100631 3 10 15) (Reg.operands [.gpr 15] [])) #v[75]
    (.letOp (n := 140) (.out 0x100634 (rolR16Effect 0x100634 5 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[138]
    (.letOp (n := 141) (.exec 0x100634 (fun s => s.RIP = 0x100634) (rolR16Effect 0x100634 5 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138]
    (.letOp (n := 142) (.out 0x100639 (andR32Imm32Effect 0x100639 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[140]
    (.letOp (n := 143) (.exec 0x100639 (fun s => s.RIP = 0x100639) (andR32Imm32Effect 0x100639 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[140]
    (.letOp (n := 144) (.out 0x100640 (rolR16Effect 0x100640 5 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[75]
    (.letOp (n := 145) (.exec 0x100640 (fun s => s.RIP = 0x100640) (rolR16Effect 0x100640 5 15 13) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 146) (.out 0x100645 (andR32Imm32Effect 0x100645 7 15 0xffffeeee) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[144]
    (.letOp (n := 147) (.exec 0x100645 (fun s => s.RIP = 0x100645) (andR32Imm32Effect 0x100645 7 15 0xffffeeee) (Reg.operands [.gpr 15] [])) #v[144]
    (.letOp (n := 148) (.exec 0x10064c (StorePre 0x10064c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10064c + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10064c 14 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 149) (.out 0x100651 (movR32R32Effect 0x100651 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[77]
    (.letOp (n := 150) (.exec 0x100651 (fun s => s.RIP = 0x100651) (movR32R32Effect 0x100651 3 11 14) (Reg.operands [.gpr 14] [])) #v[77]
    (.letOp (n := 151) (.out 0x100654 (rolR16Effect 0x100654 5 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[149]
    (.letOp (n := 152) (.exec 0x100654 (fun s => s.RIP = 0x100654) (rolR16Effect 0x100654 5 11 9) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 153) (.out 0x100659 (orR32R32Effect 0x100659 3 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[146, 142]
    (.letOp (n := 154) (.exec 0x100659 (fun s => s.RIP = 0x100659) (orR32R32Effect 0x100659 3 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[146, 142]
    (.letOp (n := 155) (.out 0x10065c (rolR16Effect 0x10065c 5 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[77]
    (.letOp (n := 156) (.exec 0x10065c (fun s => s.RIP = 0x10065c) (rolR16Effect 0x10065c 5 14 13) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 157) (.out 0x100661 (andR32Imm32Effect 0x100661 7 11 0x1111) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[151]
    (.letOp (n := 158) (.exec 0x100661 (fun s => s.RIP = 0x100661) (andR32Imm32Effect 0x100661 7 11 0x1111) (Reg.operands [.gpr 11] [])) #v[151]
    (.letOp (n := 159) (.out 0x100668 (andR32Imm32Effect 0x100668 7 14 0xffffeeee) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[155]
    (.letOp (n := 160) (.exec 0x100668 (fun s => s.RIP = 0x100668) (andR32Imm32Effect 0x100668 7 14 0xffffeeee) (Reg.operands [.gpr 14] [])) #v[155]
    (.letOp (n := 161) (.out 0x10066f (orR32R32Effect 0x10066f 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x10066f (fun s => s.RIP = 0x10066f) (orR32R32Effect 0x10066f 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[159, 157]
    (.letOp (n := 163) (.exec 0x100672 (StorePre 0x100672 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100672 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100672 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 164) (.out 0x100676 (movR32R32Effect 0x100676 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[79]
    (.letOp (n := 165) (.exec 0x100676 (fun s => s.RIP = 0x100676) (movR32R32Effect 0x100676 3 10 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 166) (.out 0x100679 (rolR16Effect 0x100679 5 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[164]
    (.letOp (n := 167) (.exec 0x100679 (fun s => s.RIP = 0x100679) (rolR16Effect 0x100679 5 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164]
    (.letOp (n := 168) (.out 0x10067e (andR32Imm32Effect 0x10067e 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[166]
    (.letOp (n := 169) (.exec 0x10067e (fun s => s.RIP = 0x10067e) (andR32Imm32Effect 0x10067e 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[166]
    (b_l100580_3)))))))))))))))))))))))))))))))))))))

def bytes_l100580_2 : List UInt8 :=
  [0x41, 0x81, 0xE4, 0xEE, 0xEE, 0xFF, 0xFF, 0x45, 0x09, 0xD4, 0x44, 0x89, 0x3C, 0x24, 0x45, 0x89,
    0xFA, 0x66, 0x41, 0xC1, 0xC2, 0x09, 0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00, 0x66, 0x41, 0xC1,
    0xC7, 0x0D, 0x41, 0x81, 0xE7, 0xEE, 0xEE, 0xFF, 0xFF, 0x44, 0x89, 0x74, 0x24, 0x04, 0x45, 0x89,
    0xF3, 0x66, 0x41, 0xC1, 0xC3, 0x09, 0x45, 0x09, 0xD7, 0x66, 0x41, 0xC1, 0xC6, 0x0D, 0x41, 0x81,
    0xE3, 0x11, 0x11, 0x00, 0x00, 0x41, 0x81, 0xE6, 0xEE, 0xEE, 0xFF, 0xFF, 0x45, 0x09, 0xDE, 0x89,
    0x44, 0x24, 0x0C, 0x41, 0x89, 0xC2, 0x66, 0x41, 0xC1, 0xC2, 0x09, 0x41, 0x81, 0xE2, 0x11, 0x11,
    0x00, 0x00] ++ bytes_l100580_3

theorem code_l100580_2 : ∀ x ∈ codeRange 0x100623 bytes_l100580_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x623 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_3

@[cfg_block] def b_l100580_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1005c7 (movR32R32Effect 0x1005c7 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[69]
    (.letOp (n := 94) (.exec 0x1005c7 (fun s => s.RIP = 0x1005c7) (movR32R32Effect 0x1005c7 3 10 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 95) (.out 0x1005ca (rolR16Effect 0x1005ca 5 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[93]
    (.letOp (n := 96) (.exec 0x1005ca (fun s => s.RIP = 0x1005ca) (rolR16Effect 0x1005ca 5 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x1005cf (orR32R32Effect 0x1005cf 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[91, 85]
    (.letOp (n := 98) (.exec 0x1005cf (fun s => s.RIP = 0x1005cf) (orR32R32Effect 0x1005cf 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[91, 85]
    (.letOp (n := 99) (.out 0x1005d2 (movR32R32Effect 0x1005d2 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 100) (.exec 0x1005d2 (fun s => s.RIP = 0x1005d2) (movR32R32Effect 0x1005d2 3 9 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 101) (.out 0x1005d5 (rolR16Effect 0x1005d5 5 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[99]
    (.letOp (n := 102) (.exec 0x1005d5 (fun s => s.RIP = 0x1005d5) (rolR16Effect 0x1005d5 5 9 13) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[99]
    (.letOp (n := 103) (.out 0x1005da (andR32Imm32Effect 0x1005da 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[95]
    (.letOp (n := 104) (.exec 0x1005da (fun s => s.RIP = 0x1005da) (andR32Imm32Effect 0x1005da 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[95]
    (.letOp (n := 105) (.out 0x1005e1 (andR32Imm32Effect 0x1005e1 7 9 0xffffeeee) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[101]
    (.letOp (n := 106) (.exec 0x1005e1 (fun s => s.RIP = 0x1005e1) (andR32Imm32Effect 0x1005e1 7 9 0xffffeeee) (Reg.operands [.gpr 9] [])) #v[101]
    (.letOp (n := 107) (.out 0x1005e8 (orR32R32Effect 0x1005e8 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x1005e8 (fun s => s.RIP = 0x1005e8) (orR32R32Effect 0x1005e8 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x1005eb (movR32R32Effect 0x1005eb 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[71]
    (.letOp (n := 110) (.exec 0x1005eb (fun s => s.RIP = 0x1005eb) (movR32R32Effect 0x1005eb 3 10 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 111) (.out 0x1005ee (rolR16Effect 0x1005ee 5 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[109]
    (.letOp (n := 112) (.exec 0x1005ee (fun s => s.RIP = 0x1005ee) (rolR16Effect 0x1005ee 5 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x1005f3 (andR32Imm32Effect 0x1005f3 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[111]
    (.letOp (n := 114) (.exec 0x1005f3 (fun s => s.RIP = 0x1005f3) (andR32Imm32Effect 0x1005f3 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[111]
    (.letOp (n := 115) (.out 0x1005fa (movR32R32Effect 0x1005fa 3 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 116) (.exec 0x1005fa (fun s => s.RIP = 0x1005fa) (movR32R32Effect 0x1005fa 3 13 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 117) (.out 0x1005fd (rolR16Effect 0x1005fd 5 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[115]
    (.letOp (n := 118) (.exec 0x1005fd (fun s => s.RIP = 0x1005fd) (rolR16Effect 0x1005fd 5 13 13) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x100602 (andR32Imm32Effect 0x100602 7 13 0xffffeeee) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[117]
    (.letOp (n := 120) (.exec 0x100602 (fun s => s.RIP = 0x100602) (andR32Imm32Effect 0x100602 7 13 0xffffeeee) (Reg.operands [.gpr 13] [])) #v[117]
    (.letOp (n := 121) (.out 0x100609 (orR32R32Effect 0x100609 3 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[119, 113]
    (.letOp (n := 122) (.exec 0x100609 (fun s => s.RIP = 0x100609) (orR32R32Effect 0x100609 3 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[119, 113]
    (.letOp (n := 123) (.out 0x10060c (movR32R32Effect 0x10060c 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[73]
    (.letOp (n := 124) (.exec 0x10060c (fun s => s.RIP = 0x10060c) (movR32R32Effect 0x10060c 3 10 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 125) (.out 0x10060f (rolR16Effect 0x10060f 5 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[123]
    (.letOp (n := 126) (.exec 0x10060f (fun s => s.RIP = 0x10060f) (rolR16Effect 0x10060f 5 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 127) (.out 0x100614 (andR32Imm32Effect 0x100614 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[125]
    (.letOp (n := 128) (.exec 0x100614 (fun s => s.RIP = 0x100614) (andR32Imm32Effect 0x100614 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[125]
    (.letOp (n := 129) (.out 0x10061b (movR32R32Effect 0x10061b 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[73]
    (.letOp (n := 130) (.exec 0x10061b (fun s => s.RIP = 0x10061b) (movR32R32Effect 0x10061b 3 12 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 131) (.out 0x10061e (rolR16Effect 0x10061e 5 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[129]
    (.letOp (n := 132) (.exec 0x10061e (fun s => s.RIP = 0x10061e) (rolR16Effect 0x10061e 5 12 13) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (b_l100580_2))))))))))))))))))))))))))))))))))))))))

def bytes_l100580_1 : List UInt8 :=
  [0x41, 0x89, 0xD2, 0x66, 0x41, 0xC1, 0xC2, 0x09, 0x44, 0x09, 0xCB, 0x41, 0x89, 0xD1, 0x66, 0x41,
    0xC1, 0xC1, 0x0D, 0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xEE, 0xEE, 0xFF,
    0xFF, 0x45, 0x09, 0xD1, 0x45, 0x89, 0xC2, 0x66, 0x41, 0xC1, 0xC2, 0x09, 0x41, 0x81, 0xE2, 0x11,
    0x11, 0x00, 0x00, 0x45, 0x89, 0xC5, 0x66, 0x41, 0xC1, 0xC5, 0x0D, 0x41, 0x81, 0xE5, 0xEE, 0xEE,
    0xFF, 0xFF, 0x45, 0x09, 0xD5, 0x41, 0x89, 0xF2, 0x66, 0x41, 0xC1, 0xC2, 0x09, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x41, 0x89, 0xF4, 0x66, 0x41, 0xC1, 0xC4, 0x0D] ++ bytes_l100580_2

theorem code_l100580_1 : ∀ x ∈ codeRange 0x1005c7 bytes_l100580_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5c7 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_2

@[cfg_block] def b_l100580 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100580 (pushR64Effect 0x100580 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100580 (PushPre 0x100580 1) (pushR64Effect 0x100580 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100581 (pushR64Effect 0x100581 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100581 (PushPre 0x100581 2) (pushR64Effect 0x100581 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100583 (pushR64Effect 0x100583 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100583 (PushPre 0x100583 2) (pushR64Effect 0x100583 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100585 (pushR64Effect 0x100585 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100585 (PushPre 0x100585 2) (pushR64Effect 0x100585 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100587 (pushR64Effect 0x100587 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100587 (PushPre 0x100587 2) (pushR64Effect 0x100587 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100589 (pushR64Effect 0x100589 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100589 (PushPre 0x100589 1) (pushR64Effect 0x100589 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10058a (subR64Imm8Effect 0x10058a 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10058a (fun s => s.RIP = 0x10058a) (subR64Imm8Effect 0x10058a 4 0x10) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10058e (movzxR32M16Effect 0x10058e 3 1 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 68) (.exec 0x10058e (LoadPre 0x10058e (fun s => AddrMode.addr (.base 7 .none) s (0x10058e + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x10058e 3 1 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x100591 (movzxR32M16Effect 0x100591 4 2 (.base 7 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 70) (.exec 0x100591 (LoadPre 0x100591 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100591 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100591 4 2 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x100595 (movzxR32M16Effect 0x100595 5 8 (.base 7 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 72) (.exec 0x100595 (LoadPre 0x100595 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x100595 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100595 5 8 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x10059a (movzxR32M16Effect 0x10059a 4 6 (.base 7 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 74) (.exec 0x10059a (LoadPre 0x10059a (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10059a + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10059a 4 6 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x10059e (movzxR32M16Effect 0x10059e 5 15 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 76) (.exec 0x10059e (LoadPre 0x10059e (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10059e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10059e 5 15 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.out 0x1005a3 (movzxR32M16Effect 0x1005a3 5 14 (.base 7 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 78) (.exec 0x1005a3 (LoadPre 0x1005a3 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x1005a3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1005a3 5 14 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x1005a8 (movzxR32M16Effect 0x1005a8 4 0 (.base 7 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 80) (.exec 0x1005a8 (LoadPre 0x1005a8 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x1005a8 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1005a8 4 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 81) (.out 0x1005ac (movR32R32Effect 0x1005ac 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 82) (.exec 0x1005ac (fun s => s.RIP = 0x1005ac) (movR32R32Effect 0x1005ac 3 9 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 83) (.out 0x1005af (rolR16Effect 0x1005af 5 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[81]
    (.letOp (n := 84) (.exec 0x1005af (fun s => s.RIP = 0x1005af) (rolR16Effect 0x1005af 5 9 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x1005b4 (andR32Imm32Effect 0x1005b4 7 9 0x1111) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[83]
    (.letOp (n := 86) (.exec 0x1005b4 (fun s => s.RIP = 0x1005b4) (andR32Imm32Effect 0x1005b4 7 9 0x1111) (Reg.operands [.gpr 9] [])) #v[83]
    (.letOp (n := 87) (.out 0x1005bb (movR32R32Effect 0x1005bb 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[67]
    (.letOp (n := 88) (.exec 0x1005bb (fun s => s.RIP = 0x1005bb) (movR32R32Effect 0x1005bb 2 3 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 89) (.out 0x1005bd (rolR16Effect 0x1005bd 4 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[87]
    (.letOp (n := 90) (.exec 0x1005bd (fun s => s.RIP = 0x1005bd) (rolR16Effect 0x1005bd 4 3 13) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x1005c1 (andR32Imm32Effect 0x1005c1 6 3 0xffffeeee) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[89]
    (.letOp (n := 92) (.exec 0x1005c1 (fun s => s.RIP = 0x1005c1) (andR32Imm32Effect 0x1005c1 6 3 0xffffeeee) (Reg.operands [.gpr 3] [])) #v[89]
    (b_l100580_1))))))))))))))))))))))))))))))))))))))))

def bytes_l100580 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x0F, 0xB7,
    0x0F, 0x0F, 0xB7, 0x57, 0x02, 0x44, 0x0F, 0xB7, 0x47, 0x04, 0x0F, 0xB7, 0x77, 0x06, 0x44, 0x0F,
    0xB7, 0x7F, 0x08, 0x44, 0x0F, 0xB7, 0x77, 0x0A, 0x0F, 0xB7, 0x47, 0x0C, 0x41, 0x89, 0xC9, 0x66,
    0x41, 0xC1, 0xC1, 0x09, 0x41, 0x81, 0xE1, 0x11, 0x11, 0x00, 0x00, 0x89, 0xCB, 0x66, 0xC1, 0xC3,
    0x0D, 0x81, 0xE3, 0xEE, 0xEE, 0xFF, 0xFF] ++ bytes_l100580_1

theorem code_l100580 : ∀ x ∈ codeRange 0x100580 bytes_l100580, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x580 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100580_1

@[cfg_block] def b_l100830_9 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x100ad9 (rolR64Effect 0x100ad9 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[399]
    (.letOp (n := 402) (.exec 0x100ad9 (fun s => s.RIP = 0x100ad9) (rolR64Effect 0x100ad9 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[399]
    (.letOp (n := 403) (.exec 0x100add (StorePre 0x100add 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x100add + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100add 5 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[397, 359]
    (.letOp (n := 404) (.out 0x100ae1 (andR64R64Effect 0x100ae1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[401, 289]
    (.letOp (n := 405) (.exec 0x100ae1 (fun s => s.RIP = 0x100ae1) (andR64R64Effect 0x100ae1 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[401, 289]
    (.letOp (n := 406) (.out 0x100ae4 (rolR64Effect 0x100ae4 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[239]
    (.letOp (n := 407) (.exec 0x100ae4 (fun s => s.RIP = 0x100ae4) (rolR64Effect 0x100ae4 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239]
    (.letOp (n := 408) (.out 0x100ae8 (andR64R64Effect 0x100ae8 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[406, 322]
    (.letOp (n := 409) (.exec 0x100ae8 (fun s => s.RIP = 0x100ae8) (andR64R64Effect 0x100ae8 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[406, 322]
    (.letOp (n := 410) (.out 0x100aeb (orR64R64Effect 0x100aeb 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[408, 404]
    (.letOp (n := 411) (.exec 0x100aeb (fun s => s.RIP = 0x100aeb) (orR64R64Effect 0x100aeb 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[408, 404]
    (.letOp (n := 412) (.out 0x100aee (xorR64R64Effect 0x100aee 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[410, 389]
    (.letOp (n := 413) (.exec 0x100aee (fun s => s.RIP = 0x100aee) (xorR64R64Effect 0x100aee 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[410, 389]
    (.letOp (n := 414) (.exec 0x100af1 (StorePre 0x100af1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100af1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100af1 10 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[412, 359]
    (.letOp (n := 415) (.out 0x100af5 (addR64Imm8Effect 0x100af5 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 416) (.exec 0x100af5 (fun s => s.RIP = 0x100af5) (addR64Imm8Effect 0x100af5 4 0x30) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 417) (.out 0x100af9 (popR64Effect 0x100af9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[415]
    (.letOp (n := 418) (.out 0x100af9 (popR64Effect 0x100af9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[415]
    (.letOp (n := 419) (.exec 0x100af9 (PopPre 0x100af9) (popR64Effect 0x100af9 1 3) (Reg.operands [.gpr 4] [])) #v[415]
    (.letOp (n := 420) (.out 0x100afa (popR64Effect 0x100afa 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[418]
    (.letOp (n := 421) (.out 0x100afa (popR64Effect 0x100afa 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[418]
    (.letOp (n := 422) (.exec 0x100afa (PopPre 0x100afa) (popR64Effect 0x100afa 2 12) (Reg.operands [.gpr 4] [])) #v[418]
    (.letOp (n := 423) (.out 0x100afc (popR64Effect 0x100afc 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[421]
    (.letOp (n := 424) (.out 0x100afc (popR64Effect 0x100afc 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[421]
    (.letOp (n := 425) (.exec 0x100afc (PopPre 0x100afc) (popR64Effect 0x100afc 2 13) (Reg.operands [.gpr 4] [])) #v[421]
    (.letOp (n := 426) (.out 0x100afe (popR64Effect 0x100afe 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[424]
    (.letOp (n := 427) (.out 0x100afe (popR64Effect 0x100afe 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[424]
    (.letOp (n := 428) (.exec 0x100afe (PopPre 0x100afe) (popR64Effect 0x100afe 2 14) (Reg.operands [.gpr 4] [])) #v[424]
    (.letOp (n := 429) (.out 0x100b00 (popR64Effect 0x100b00 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[427]
    (.letOp (n := 430) (.out 0x100b00 (popR64Effect 0x100b00 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[427]
    (.letOp (n := 431) (.exec 0x100b00 (PopPre 0x100b00) (popR64Effect 0x100b00 2 15) (Reg.operands [.gpr 4] [])) #v[427]
    (.letOp (n := 432) (.out 0x100b02 (popR64Effect 0x100b02 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[430]
    (.letOp (n := 433) (.out 0x100b02 (popR64Effect 0x100b02 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[430]
    (.letOp (n := 434) (.exec 0x100b02 (PopPre 0x100b02) (popR64Effect 0x100b02 1 5) (Reg.operands [.gpr 4] [])) #v[430]
    (.letOp (n := 435) (.out 0x100b03 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[433]
    (.letOp (n := 436) (.out 0x100b03 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[433]
    (.letOp (n := 437) (.exec 0x100b03 (RetPre 0x100b03) (retEffect) (Reg.operands [.gpr 4] [])) #v[433]
    (.terminate (.ret (RegMap.args [(0, 404), (1, 389), (2, 370), (3, 417), (4, 436), (5, 432), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 426), (15, 429), (22, 22), (39, 39), (50, 50), (51, 51)] 438) (some ⟨435, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l100830_9 : List UInt8 :=
  [0x48, 0xC1, 0xC0, 0x18, 0x48, 0x89, 0x6F, 0x30, 0x48, 0x21, 0xD8, 0x49, 0xC1, 0xC2, 0x28, 0x4D,
    0x21, 0xC2, 0x49, 0x09, 0xC2, 0x49, 0x31, 0xCA, 0x4C, 0x89, 0x57, 0x38, 0x48, 0x83, 0xC4, 0x30,
    0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l100830_9 : ∀ x ∈ codeRange 0x100ad9 bytes_l100830_9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xad9 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100830_8 : Block Op Label signature Reg.count 362 :=
  .letOp (n := 362) (.out 0x100a96 (movR64R64Effect 0x100a96 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[332]
    (.letOp (n := 363) (.exec 0x100a96 (fun s => s.RIP = 0x100a96) (movR64R64Effect 0x100a96 0 14) (Reg.operands [.gpr 14] [])) #v[332]
    (.letOp (n := 364) (.out 0x100a99 (rolR64Effect 0x100a99 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[362]
    (.letOp (n := 365) (.exec 0x100a99 (fun s => s.RIP = 0x100a99) (rolR64Effect 0x100a99 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[362]
    (.letOp (n := 366) (.out 0x100a9d (andR64R64Effect 0x100a9d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[364, 289]
    (.letOp (n := 367) (.exec 0x100a9d (fun s => s.RIP = 0x100a9d) (andR64R64Effect 0x100a9d 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[364, 289]
    (.letOp (n := 368) (.out 0x100aa0 (xorR64R64Effect 0x100aa0 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[355, 332]
    (.letOp (n := 369) (.exec 0x100aa0 (fun s => s.RIP = 0x100aa0) (xorR64R64Effect 0x100aa0 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[355, 332]
    (.letOp (n := 370) (.out 0x100aa3 (movR64R64Effect 0x100aa3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[368]
    (.letOp (n := 371) (.exec 0x100aa3 (fun s => s.RIP = 0x100aa3) (movR64R64Effect 0x100aa3 2 1) (Reg.operands [.gpr 1] [])) #v[368]
    (.letOp (n := 372) (.out 0x100aa6 (rolR64Effect 0x100aa6 4 14 40) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[332]
    (.letOp (n := 373) (.exec 0x100aa6 (fun s => s.RIP = 0x100aa6) (rolR64Effect 0x100aa6 4 14 40) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[332]
    (.letOp (n := 374) (.out 0x100aaa (andR64R64Effect 0x100aaa 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[372, 322]
    (.letOp (n := 375) (.exec 0x100aaa (fun s => s.RIP = 0x100aaa) (andR64R64Effect 0x100aaa 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[372, 322]
    (.letOp (n := 376) (.out 0x100aad (orR64R64Effect 0x100aad 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[374, 366]
    (.letOp (n := 377) (.exec 0x100aad (fun s => s.RIP = 0x100aad) (orR64R64Effect 0x100aad 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[374, 366]
    (.letOp (n := 378) (.out 0x100ab0 (xorR64R64Effect 0x100ab0 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[376, 343]
    (.letOp (n := 379) (.exec 0x100ab0 (fun s => s.RIP = 0x100ab0) (xorR64R64Effect 0x100ab0 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[376, 343]
    (.letOp (n := 380) (.exec 0x100ab3 (StorePre 0x100ab3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100ab3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100ab3 14 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[378, 359]
    (.letOp (n := 381) (.out 0x100ab7 (movR64R64Effect 0x100ab7 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[357]
    (.letOp (n := 382) (.exec 0x100ab7 (fun s => s.RIP = 0x100ab7) (movR64R64Effect 0x100ab7 0 5) (Reg.operands [.gpr 5] [])) #v[357]
    (.letOp (n := 383) (.out 0x100aba (rolR64Effect 0x100aba 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[381]
    (.letOp (n := 384) (.exec 0x100aba (fun s => s.RIP = 0x100aba) (rolR64Effect 0x100aba 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[381]
    (.letOp (n := 385) (.out 0x100abe (andR64R64Effect 0x100abe 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[383, 289]
    (.letOp (n := 386) (.exec 0x100abe (fun s => s.RIP = 0x100abe) (andR64R64Effect 0x100abe 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[383, 289]
    (.letOp (n := 387) (.out 0x100ac1 (movR64M64Effect 0x100ac1 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 388) (.exec 0x100ac1 (LoadPre 0x100ac1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100ac1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ac1 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 389) (.out 0x100ac6 (xorR64R64Effect 0x100ac6 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[387, 357]
    (.letOp (n := 390) (.exec 0x100ac6 (fun s => s.RIP = 0x100ac6) (xorR64R64Effect 0x100ac6 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[387, 357]
    (.letOp (n := 391) (.out 0x100ac9 (rolR64Effect 0x100ac9 4 5 40) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[357]
    (.letOp (n := 392) (.exec 0x100ac9 (fun s => s.RIP = 0x100ac9) (rolR64Effect 0x100ac9 4 5 40) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[357]
    (.letOp (n := 393) (.out 0x100acd (andR64R64Effect 0x100acd 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[391, 322]
    (.letOp (n := 394) (.exec 0x100acd (fun s => s.RIP = 0x100acd) (andR64R64Effect 0x100acd 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[391, 322]
    (.letOp (n := 395) (.out 0x100ad0 (orR64R64Effect 0x100ad0 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[393, 385]
    (.letOp (n := 396) (.exec 0x100ad0 (fun s => s.RIP = 0x100ad0) (orR64R64Effect 0x100ad0 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[393, 385]
    (.letOp (n := 397) (.out 0x100ad3 (xorR64R64Effect 0x100ad3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[395, 370]
    (.letOp (n := 398) (.exec 0x100ad3 (fun s => s.RIP = 0x100ad3) (xorR64R64Effect 0x100ad3 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[395, 370]
    (.letOp (n := 399) (.out 0x100ad6 (movR64R64Effect 0x100ad6 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[239]
    (.letOp (n := 400) (.exec 0x100ad6 (fun s => s.RIP = 0x100ad6) (movR64R64Effect 0x100ad6 0 10) (Reg.operands [.gpr 10] [])) #v[239]
    (b_l100830_9)))))))))))))))))))))))))))))))))))))))

def bytes_l100830_8 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x21, 0xD8, 0x4C, 0x31, 0xF1, 0x48, 0x89, 0xCA,
    0x49, 0xC1, 0xC6, 0x28, 0x4D, 0x21, 0xC6, 0x49, 0x09, 0xC6, 0x49, 0x31, 0xF6, 0x4C, 0x89, 0x77,
    0x28, 0x48, 0x89, 0xE8, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x21, 0xD8, 0x48, 0x8B, 0x4C, 0x24, 0x10,
    0x48, 0x31, 0xE9, 0x48, 0xC1, 0xC5, 0x28, 0x4C, 0x21, 0xC5, 0x48, 0x09, 0xC5, 0x48, 0x31, 0xD5,
    0x4C, 0x89, 0xD0] ++ bytes_l100830_9

theorem code_l100830_8 : ∀ x ∈ codeRange 0x100a96 bytes_l100830_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa96 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_9

@[cfg_block] def b_l100830_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x100a52 (orR64R64Effect 0x100a52 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[320, 318]
    (.letOp (n := 325) (.exec 0x100a52 (fun s => s.RIP = 0x100a52) (orR64R64Effect 0x100a52 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[320, 318]
    (.letOp (n := 326) (.out 0x100a55 (xorR64R64Effect 0x100a55 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[293, 239]
    (.letOp (n := 327) (.exec 0x100a55 (fun s => s.RIP = 0x100a55) (xorR64R64Effect 0x100a55 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[293, 239]
    (.letOp (n := 328) (.out 0x100a58 (xorR64R64Effect 0x100a58 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[326, 324]
    (.letOp (n := 329) (.exec 0x100a58 (fun s => s.RIP = 0x100a58) (xorR64R64Effect 0x100a58 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[326, 324]
    (.letOp (n := 330) (.out 0x100a5b (movR64M64Effect 0x100a5b 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 331) (.exec 0x100a5b (LoadPre 0x100a5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100a5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100a5b 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 332) (.out 0x100a60 (xorR64R64Effect 0x100a60 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[79, 330]
    (.letOp (n := 333) (.exec 0x100a60 (fun s => s.RIP = 0x100a60) (xorR64R64Effect 0x100a60 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[79, 330]
    (.letOp (n := 334) (.exec 0x100a63 (StorePre 0x100a63 4 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x100a63 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100a63 13 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[328, 277]
    (.letOp (n := 335) (.out 0x100a67 (movR64R64Effect 0x100a67 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[312]
    (.letOp (n := 336) (.exec 0x100a67 (fun s => s.RIP = 0x100a67) (movR64R64Effect 0x100a67 0 11) (Reg.operands [.gpr 11] [])) #v[312]
    (.letOp (n := 337) (.out 0x100a6a (rolR64Effect 0x100a6a 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[335]
    (.letOp (n := 338) (.exec 0x100a6a (fun s => s.RIP = 0x100a6a) (rolR64Effect 0x100a6a 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335]
    (.letOp (n := 339) (.out 0x100a6e (andR64R64Effect 0x100a6e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[337, 289]
    (.letOp (n := 340) (.exec 0x100a6e (fun s => s.RIP = 0x100a6e) (andR64R64Effect 0x100a6e 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[337, 289]
    (.letOp (n := 341) (.out 0x100a71 (xorR64R64Effect 0x100a71 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[330, 312]
    (.letOp (n := 342) (.exec 0x100a71 (fun s => s.RIP = 0x100a71) (xorR64R64Effect 0x100a71 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[330, 312]
    (.letOp (n := 343) (.out 0x100a74 (movR64R64Effect 0x100a74 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[341]
    (.letOp (n := 344) (.exec 0x100a74 (fun s => s.RIP = 0x100a74) (movR64R64Effect 0x100a74 6 1) (Reg.operands [.gpr 1] [])) #v[341]
    (.letOp (n := 345) (.out 0x100a77 (rolR64Effect 0x100a77 4 11 40) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[312]
    (.letOp (n := 346) (.exec 0x100a77 (fun s => s.RIP = 0x100a77) (rolR64Effect 0x100a77 4 11 40) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 347) (.out 0x100a7b (andR64R64Effect 0x100a7b 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[345, 322]
    (.letOp (n := 348) (.exec 0x100a7b (fun s => s.RIP = 0x100a7b) (andR64R64Effect 0x100a7b 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[345, 322]
    (.letOp (n := 349) (.out 0x100a7e (orR64R64Effect 0x100a7e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[347, 339]
    (.letOp (n := 350) (.exec 0x100a7e (fun s => s.RIP = 0x100a7e) (orR64R64Effect 0x100a7e 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[347, 339]
    (.letOp (n := 351) (.out 0x100a81 (xorR64R64Effect 0x100a81 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[314, 239]
    (.letOp (n := 352) (.exec 0x100a81 (fun s => s.RIP = 0x100a81) (xorR64R64Effect 0x100a81 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[314, 239]
    (.letOp (n := 353) (.out 0x100a84 (xorR64R64Effect 0x100a84 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[351, 349]
    (.letOp (n := 354) (.exec 0x100a84 (fun s => s.RIP = 0x100a84) (xorR64R64Effect 0x100a84 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[351, 349]
    (.letOp (n := 355) (.out 0x100a87 (movR64M64Effect 0x100a87 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 356) (.exec 0x100a87 (LoadPre 0x100a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100a87 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100a87 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 357) (.out 0x100a8c (xorR64R64Effect 0x100a8c 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[172, 355]
    (.letOp (n := 358) (.exec 0x100a8c (fun s => s.RIP = 0x100a8c) (xorR64R64Effect 0x100a8c 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[172, 355]
    (.letOp (n := 359) (.out 0x100a8f (movR64R64Effect 0x100a8f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[277]
    (.letOp (n := 360) (.exec 0x100a8f (fun s => s.RIP = 0x100a8f) (movR64R64Effect 0x100a8f 7 2) (Reg.operands [.gpr 2] [])) #v[277]
    (.letOp (n := 361) (.exec 0x100a92 (StorePre 0x100a92 4 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x100a92 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100a92 15 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[353, 277]
    (b_l100830_8))))))))))))))))))))))))))))))))))))))

def bytes_l100830_7 : List UInt8 :=
  [0x48, 0x09, 0xC7, 0x4D, 0x31, 0xD5, 0x49, 0x31, 0xFD, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x49, 0x31,
    0xCE, 0x4C, 0x89, 0x6A, 0x18, 0x4C, 0x89, 0xD8, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x21, 0xD8, 0x4C,
    0x31, 0xD9, 0x48, 0x89, 0xCE, 0x49, 0xC1, 0xC3, 0x28, 0x4D, 0x21, 0xC3, 0x49, 0x09, 0xC3, 0x4D,
    0x31, 0xD7, 0x4D, 0x31, 0xDF, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0x31, 0xCD, 0x48, 0x89, 0xD7,
    0x4C, 0x89, 0x7A, 0x20] ++ bytes_l100830_8

theorem code_l100830_7 : ∀ x ∈ codeRange 0x100a52 bytes_l100830_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa52 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_8

@[cfg_block] def b_l100830_6 : Block Op Label signature Reg.count 285 :=
  .letOp (n := 285) (.out 0x100a03 (movR64R64Effect 0x100a03 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[281]
    (.letOp (n := 286) (.exec 0x100a03 (fun s => s.RIP = 0x100a03) (movR64R64Effect 0x100a03 0 9) (Reg.operands [.gpr 9] [])) #v[281]
    (.letOp (n := 287) (.out 0x100a06 (rolR64Effect 0x100a06 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 288) (.exec 0x100a06 (fun s => s.RIP = 0x100a06) (rolR64Effect 0x100a06 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[285]
    (.letOp (n := 289) (.out 0x100a0a (movR64Imm64Effect 0x100a0a 3 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 290) (.exec 0x100a0a (fun s => s.RIP = 0x100a0a) (movR64Imm64Effect 0x100a0a 3 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 291) (.out 0x100a14 (andR64R64Effect 0x100a14 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[287, 289]
    (.letOp (n := 292) (.exec 0x100a14 (fun s => s.RIP = 0x100a14) (andR64R64Effect 0x100a14 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[287, 289]
    (.letOp (n := 293) (.out 0x100a17 (xorR64R64Effect 0x100a17 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[142, 281]
    (.letOp (n := 294) (.exec 0x100a17 (fun s => s.RIP = 0x100a17) (xorR64R64Effect 0x100a17 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[142, 281]
    (.letOp (n := 295) (.out 0x100a1a (rolR64Effect 0x100a1a 4 9 40) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[281]
    (.letOp (n := 296) (.exec 0x100a1a (fun s => s.RIP = 0x100a1a) (rolR64Effect 0x100a1a 4 9 40) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[281]
    (.letOp (n := 297) (.out 0x100a1e (movR64Imm64Effect 0x100a1e 6 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 298) (.exec 0x100a1e (fun s => s.RIP = 0x100a1e) (movR64Imm64Effect 0x100a1e 6 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 299) (.out 0x100a28 (andR64R64Effect 0x100a28 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[295, 297]
    (.letOp (n := 300) (.exec 0x100a28 (fun s => s.RIP = 0x100a28) (andR64R64Effect 0x100a28 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[295, 297]
    (.letOp (n := 301) (.out 0x100a2b (orR64R64Effect 0x100a2b 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[299, 291]
    (.letOp (n := 302) (.exec 0x100a2b (fun s => s.RIP = 0x100a2b) (orR64R64Effect 0x100a2b 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[299, 291]
    (.letOp (n := 303) (.out 0x100a2e (xorR64R64Effect 0x100a2e 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[247, 279]
    (.letOp (n := 304) (.exec 0x100a2e (fun s => s.RIP = 0x100a2e) (xorR64R64Effect 0x100a2e 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[247, 279]
    (.letOp (n := 305) (.out 0x100a31 (xorR64R64Effect 0x100a31 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[303, 301]
    (.letOp (n := 306) (.exec 0x100a31 (fun s => s.RIP = 0x100a31) (xorR64R64Effect 0x100a31 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[303, 301]
    (.letOp (n := 307) (.exec 0x100a34 (StorePre 0x100a34 4 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x100a34 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100a34 8 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 2] [])) #v[305, 277]
    (.letOp (n := 308) (.out 0x100a38 (movR64R64Effect 0x100a38 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[283]
    (.letOp (n := 309) (.exec 0x100a38 (fun s => s.RIP = 0x100a38) (movR64R64Effect 0x100a38 0 7) (Reg.operands [.gpr 7] [])) #v[283]
    (.letOp (n := 310) (.out 0x100a3b (rolR64Effect 0x100a3b 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[308]
    (.letOp (n := 311) (.exec 0x100a3b (fun s => s.RIP = 0x100a3b) (rolR64Effect 0x100a3b 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[308]
    (.letOp (n := 312) (.out 0x100a3f (xorR64R64Effect 0x100a3f 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[77, 158]
    (.letOp (n := 313) (.exec 0x100a3f (fun s => s.RIP = 0x100a3f) (xorR64R64Effect 0x100a3f 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[77, 158]
    (.letOp (n := 314) (.out 0x100a42 (xorR64R64Effect 0x100a42 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[158, 283]
    (.letOp (n := 315) (.exec 0x100a42 (fun s => s.RIP = 0x100a42) (xorR64R64Effect 0x100a42 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[158, 283]
    (.letOp (n := 316) (.out 0x100a45 (rolR64Effect 0x100a45 4 7 40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[283]
    (.letOp (n := 317) (.exec 0x100a45 (fun s => s.RIP = 0x100a45) (rolR64Effect 0x100a45 4 7 40) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[283]
    (.letOp (n := 318) (.out 0x100a49 (andR64R64Effect 0x100a49 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[310, 289]
    (.letOp (n := 319) (.exec 0x100a49 (fun s => s.RIP = 0x100a49) (andR64R64Effect 0x100a49 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[310, 289]
    (.letOp (n := 320) (.out 0x100a4c (andR64R64Effect 0x100a4c 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[316, 297]
    (.letOp (n := 321) (.exec 0x100a4c (fun s => s.RIP = 0x100a4c) (andR64R64Effect 0x100a4c 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[316, 297]
    (.letOp (n := 322) (.out 0x100a4f (movR64R64Effect 0x100a4f 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[297]
    (.letOp (n := 323) (.exec 0x100a4f (fun s => s.RIP = 0x100a4f) (movR64R64Effect 0x100a4f 8 6) (Reg.operands [.gpr 6] [])) #v[297]
    (b_l100830_7)))))))))))))))))))))))))))))))))))))))

def bytes_l100830_6 : List UInt8 :=
  [0x4C, 0x89, 0xC8, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0xBB, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0x00, 0x48, 0x21, 0xD8, 0x4D, 0x31, 0xCD, 0x49, 0xC1, 0xC1, 0x28, 0x48, 0xBE, 0x00, 0xFF, 0x00,
    0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x49, 0x21, 0xF1, 0x49, 0x09, 0xC1, 0x49, 0x31, 0xC8, 0x4D, 0x31,
    0xC8, 0x4C, 0x89, 0x42, 0x10, 0x48, 0x89, 0xF8, 0x48, 0xC1, 0xC0, 0x18, 0x4D, 0x31, 0xFB, 0x49,
    0x31, 0xFF, 0x48, 0xC1, 0xC7, 0x28, 0x48, 0x21, 0xD8, 0x48, 0x21, 0xF7, 0x49, 0x89, 0xF0] ++ bytes_l100830_7

theorem code_l100830_6 : ∀ x ∈ codeRange 0x100a03 bytes_l100830_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa03 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_7

@[cfg_block] def b_l100830_5 : Block Op Label signature Reg.count 247 :=
  .letOp (n := 247) (.out 0x1009b2 (xorR64R64Effect 0x1009b2 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[71, 245]
    (.letOp (n := 248) (.exec 0x1009b2 (fun s => s.RIP = 0x1009b2) (xorR64R64Effect 0x1009b2 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[71, 245]
    (.letOp (n := 249) (.out 0x1009b5 (movR64R64Effect 0x1009b5 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[247]
    (.letOp (n := 250) (.exec 0x1009b5 (fun s => s.RIP = 0x1009b5) (movR64R64Effect 0x1009b5 0 8) (Reg.operands [.gpr 8] [])) #v[247]
    (.letOp (n := 251) (.out 0x1009b8 (rolR64Effect 0x1009b8 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[249]
    (.letOp (n := 252) (.exec 0x1009b8 (fun s => s.RIP = 0x1009b8) (rolR64Effect 0x1009b8 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[249]
    (.letOp (n := 253) (.out 0x1009bc (movR64M64Effect 0x1009bc 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 254) (.exec 0x1009bc (LoadPre 0x1009bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1009bc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009bc 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 255) (.exec 0x1009c1 (StorePre 0x1009c1 3 (fun s => AddrMode.addr (.base 1 .none) s (0x1009c1 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1009c1 12 (.base 1 .none)) (Reg.operands [.gpr 12, .gpr 1] [])) #v[243, 253]
    (.letOp (n := 256) (.out 0x1009c4 (movR64R64Effect 0x1009c4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[247]
    (.letOp (n := 257) (.exec 0x1009c4 (fun s => s.RIP = 0x1009c4) (movR64R64Effect 0x1009c4 6 8) (Reg.operands [.gpr 8] [])) #v[247]
    (.letOp (n := 258) (.out 0x1009c7 (rolR64Effect 0x1009c7 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[256]
    (.letOp (n := 259) (.exec 0x1009c7 (fun s => s.RIP = 0x1009c7) (rolR64Effect 0x1009c7 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[256]
    (.letOp (n := 260) (.out 0x1009cb (movR64Imm64Effect 0x1009cb 12 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 261) (.exec 0x1009cb (fun s => s.RIP = 0x1009cb) (movR64Imm64Effect 0x1009cb 12 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 262) (.out 0x1009d5 (andR64R64Effect 0x1009d5 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[251, 260]
    (.letOp (n := 263) (.exec 0x1009d5 (fun s => s.RIP = 0x1009d5) (andR64R64Effect 0x1009d5 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[251, 260]
    (.letOp (n := 264) (.out 0x1009d8 (movR64Imm64Effect 0x1009d8 12 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 265) (.exec 0x1009d8 (fun s => s.RIP = 0x1009d8) (movR64Imm64Effect 0x1009d8 12 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 266) (.out 0x1009e2 (andR64R64Effect 0x1009e2 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[258, 264]
    (.letOp (n := 267) (.exec 0x1009e2 (fun s => s.RIP = 0x1009e2) (andR64R64Effect 0x1009e2 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[258, 264]
    (.letOp (n := 268) (.out 0x1009e5 (orR64R64Effect 0x1009e5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[266, 262]
    (.letOp (n := 269) (.exec 0x1009e5 (fun s => s.RIP = 0x1009e5) (orR64R64Effect 0x1009e5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[266, 262]
    (.letOp (n := 270) (.out 0x1009e8 (xorR64R64Effect 0x1009e8 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[216, 245]
    (.letOp (n := 271) (.exec 0x1009e8 (fun s => s.RIP = 0x1009e8) (xorR64R64Effect 0x1009e8 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[216, 245]
    (.letOp (n := 272) (.out 0x1009eb (xorR64R64Effect 0x1009eb 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[270, 239]
    (.letOp (n := 273) (.exec 0x1009eb (fun s => s.RIP = 0x1009eb) (xorR64R64Effect 0x1009eb 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[270, 239]
    (.letOp (n := 274) (.out 0x1009ee (xorR64R64Effect 0x1009ee 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[272, 268]
    (.letOp (n := 275) (.exec 0x1009ee (fun s => s.RIP = 0x1009ee) (xorR64R64Effect 0x1009ee 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[272, 268]
    (.letOp (n := 276) (.exec 0x1009f1 (StorePre 0x1009f1 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x1009f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009f1 2 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 1] [])) #v[274, 253]
    (.letOp (n := 277) (.out 0x1009f5 (movR64R64Effect 0x1009f5 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[253]
    (.letOp (n := 278) (.exec 0x1009f5 (fun s => s.RIP = 0x1009f5) (movR64R64Effect 0x1009f5 2 1) (Reg.operands [.gpr 1] [])) #v[253]
    (.letOp (n := 279) (.out 0x1009f8 (movR64M64Effect 0x1009f8 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 280) (.exec 0x1009f8 (LoadPre 0x1009f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1009f8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009f8 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 281) (.out 0x1009fd (xorR64R64Effect 0x1009fd 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[73, 279]
    (.letOp (n := 282) (.exec 0x1009fd (fun s => s.RIP = 0x1009fd) (xorR64R64Effect 0x1009fd 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[73, 279]
    (.letOp (n := 283) (.out 0x100a00 (xorR64R64Effect 0x100a00 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[75, 142]
    (.letOp (n := 284) (.exec 0x100a00 (fun s => s.RIP = 0x100a00) (xorR64R64Effect 0x100a00 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[75, 142]
    (b_l100830_6))))))))))))))))))))))))))))))))))))))

def bytes_l100830_5 : List UInt8 :=
  [0x49, 0x31, 0xD8, 0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x4C,
    0x89, 0x21, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xC6, 0x28, 0x49, 0xBC, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0x00, 0xFF, 0x00, 0x4C, 0x21, 0xE0, 0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0x4C, 0x21, 0xE6, 0x48, 0x09, 0xC6, 0x48, 0x31, 0xDA, 0x4C, 0x31, 0xD2, 0x48, 0x31, 0xF2, 0x48,
    0x89, 0x51, 0x08, 0x48, 0x89, 0xCA, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x31, 0xC9, 0x4C, 0x31,
    0xEF] ++ bytes_l100830_6

theorem code_l100830_5 : ∀ x ∈ codeRange 0x1009b2 bytes_l100830_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b2 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_6

@[cfg_block] def b_l100830_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x10095b (rolR64Effect 0x10095b 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[206]
    (.letOp (n := 209) (.exec 0x10095b (fun s => s.RIP = 0x10095b) (rolR64Effect 0x10095b 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[206]
    (.letOp (n := 210) (.out 0x10095f (movR64Imm64Effect 0x10095f 1 0xfff0fff0fff0fff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 211) (.exec 0x10095f (fun s => s.RIP = 0x10095f) (movR64Imm64Effect 0x10095f 1 0xfff0fff0fff0fff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 212) (.out 0x100969 (andR64R64Effect 0x100969 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[208, 210]
    (.letOp (n := 213) (.exec 0x100969 (fun s => s.RIP = 0x100969) (andR64R64Effect 0x100969 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[208, 210]
    (.letOp (n := 214) (.out 0x10096c (movR64R64Effect 0x10096c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[212]
    (.letOp (n := 215) (.exec 0x10096c (fun s => s.RIP = 0x10096c) (movR64R64Effect 0x10096c 1 0) (Reg.operands [.gpr 0] [])) #v[212]
    (.letOp (n := 216) (.out 0x10096f (xorR64R64Effect 0x10096f 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[69, 98]
    (.letOp (n := 217) (.exec 0x10096f (fun s => s.RIP = 0x10096f) (xorR64R64Effect 0x10096f 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[69, 98]
    (.letOp (n := 218) (.out 0x100972 (movR64R64Effect 0x100972 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[216]
    (.letOp (n := 219) (.exec 0x100972 (fun s => s.RIP = 0x100972) (movR64R64Effect 0x100972 0 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 220) (.out 0x100975 (rolR64Effect 0x100975 4 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[218]
    (.letOp (n := 221) (.exec 0x100975 (fun s => s.RIP = 0x100975) (rolR64Effect 0x100975 4 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[218]
    (.letOp (n := 222) (.out 0x100979 (orR64R64Effect 0x100979 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[214, 204]
    (.letOp (n := 223) (.exec 0x100979 (fun s => s.RIP = 0x100979) (orR64R64Effect 0x100979 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[214, 204]
    (.letOp (n := 224) (.exec 0x10097c (StorePre 0x10097c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10097c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10097c 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[222, 65]
    (.letOp (n := 225) (.out 0x100981 (movR64Imm64Effect 0x100981 6 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 226) (.exec 0x100981 (fun s => s.RIP = 0x100981) (movR64Imm64Effect 0x100981 6 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 227) (.out 0x10098b (andR64R64Effect 0x10098b 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[220, 225]
    (.letOp (n := 228) (.exec 0x10098b (fun s => s.RIP = 0x10098b) (andR64R64Effect 0x10098b 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[220, 225]
    (.letOp (n := 229) (.out 0x10098e (movR64R64Effect 0x10098e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[216]
    (.letOp (n := 230) (.exec 0x10098e (fun s => s.RIP = 0x10098e) (movR64R64Effect 0x10098e 6 2) (Reg.operands [.gpr 2] [])) #v[216]
    (.letOp (n := 231) (.out 0x100991 (rolR64Effect 0x100991 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[229]
    (.letOp (n := 232) (.exec 0x100991 (fun s => s.RIP = 0x100991) (rolR64Effect 0x100991 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[229]
    (.letOp (n := 233) (.out 0x100995 (movR64Imm64Effect 0x100995 3 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 234) (.exec 0x100995 (fun s => s.RIP = 0x100995) (movR64Imm64Effect 0x100995 3 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 235) (.out 0x10099f (andR64R64Effect 0x10099f 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[231, 233]
    (.letOp (n := 236) (.exec 0x10099f (fun s => s.RIP = 0x10099f) (andR64R64Effect 0x10099f 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[231, 233]
    (.letOp (n := 237) (.out 0x1009a2 (orR64R64Effect 0x1009a2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[235, 227]
    (.letOp (n := 238) (.exec 0x1009a2 (fun s => s.RIP = 0x1009a2) (orR64R64Effect 0x1009a2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[235, 227]
    (.letOp (n := 239) (.out 0x1009a5 (xorR64R64Effect 0x1009a5 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[196, 222]
    (.letOp (n := 240) (.exec 0x1009a5 (fun s => s.RIP = 0x1009a5) (xorR64R64Effect 0x1009a5 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[196, 222]
    (.letOp (n := 241) (.out 0x1009a8 (xorR64R64Effect 0x1009a8 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[98, 239]
    (.letOp (n := 242) (.exec 0x1009a8 (fun s => s.RIP = 0x1009a8) (xorR64R64Effect 0x1009a8 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[98, 239]
    (.letOp (n := 243) (.out 0x1009ab (xorR64R64Effect 0x1009ab 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[241, 237]
    (.letOp (n := 244) (.exec 0x1009ab (fun s => s.RIP = 0x1009ab) (xorR64R64Effect 0x1009ab 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[241, 237]
    (.letOp (n := 245) (.out 0x1009ae (movR64M64Effect 0x1009ae 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 246) (.exec 0x1009ae (LoadPre 0x1009ae (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1009ae + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1009ae 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l100830_5)))))))))))))))))))))))))))))))))))))))

def bytes_l100830_4 : List UInt8 :=
  [0x48, 0xC1, 0xC0, 0x34, 0x48, 0xB9, 0xF0, 0xFF, 0xF0, 0xFF, 0xF0, 0xFF, 0xF0, 0xFF, 0x48, 0x21,
    0xC8, 0x48, 0x89, 0xC1, 0x4C, 0x31, 0xE2, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xC0, 0x18, 0x48, 0x09,
    0xF1, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0xBE, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00,
    0x48, 0x21, 0xF0, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xC6, 0x28, 0x48, 0xBB, 0x00, 0xFF, 0x00, 0xFF,
    0x00, 0xFF, 0x00, 0xFF, 0x48, 0x21, 0xDE, 0x48, 0x09, 0xC6, 0x49, 0x31, 0xCA, 0x4D, 0x31, 0xD4,
    0x49, 0x31, 0xF4, 0x48, 0x8B, 0x1C, 0x24] ++ bytes_l100830_5

theorem code_l100830_4 : ∀ x ∈ codeRange 0x10095b bytes_l100830_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x95b 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_5

@[cfg_block] def b_l100830_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x100901 (andR64R64Effect 0x100901 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[168, 94]
    (.letOp (n := 171) (.exec 0x100901 (fun s => s.RIP = 0x100901) (andR64R64Effect 0x100901 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[168, 94]
    (.letOp (n := 172) (.out 0x100904 (movR64M64Effect 0x100904 5 (.base 1 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[67]
    (.letOp (n := 173) (.exec 0x100904 (LoadPre 0x100904 (fun s => AddrMode.addr (.base 1 (.d8 0x30)) s (0x100904 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100904 5 (.base 1 (.d8 0x30))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 174) (.out 0x100908 (movR64R64Effect 0x100908 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[172]
    (.letOp (n := 175) (.exec 0x100908 (fun s => s.RIP = 0x100908) (movR64R64Effect 0x100908 6 5) (Reg.operands [.gpr 5] [])) #v[172]
    (.letOp (n := 176) (.out 0x10090b (rolR64Effect 0x10090b 4 6 36) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[174]
    (.letOp (n := 177) (.exec 0x10090b (fun s => s.RIP = 0x10090b) (rolR64Effect 0x10090b 4 6 36) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[174]
    (.letOp (n := 178) (.out 0x10090f (orR64R64Effect 0x10090f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[170, 164]
    (.letOp (n := 179) (.exec 0x10090f (fun s => s.RIP = 0x10090f) (orR64R64Effect 0x10090f 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[170, 164]
    (.letOp (n := 180) (.exec 0x100912 (StorePre 0x100912 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100912 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100912 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[178, 65]
    (.letOp (n := 181) (.out 0x100917 (movR64R64Effect 0x100917 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[172]
    (.letOp (n := 182) (.exec 0x100917 (fun s => s.RIP = 0x100917) (movR64R64Effect 0x100917 0 5) (Reg.operands [.gpr 5] [])) #v[172]
    (.letOp (n := 183) (.out 0x10091a (rolR64Effect 0x10091a 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[181]
    (.letOp (n := 184) (.exec 0x10091a (fun s => s.RIP = 0x10091a) (rolR64Effect 0x10091a 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[181]
    (.letOp (n := 185) (.out 0x10091e (movR64Imm64Effect 0x10091e 10 0xf000f000f000f) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 186) (.exec 0x10091e (fun s => s.RIP = 0x10091e) (movR64Imm64Effect 0x10091e 10 0xf000f000f000f) (Reg.operands [] [])) #v[]
    (.letOp (n := 187) (.out 0x100928 (andR64R64Effect 0x100928 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[176, 185]
    (.letOp (n := 188) (.exec 0x100928 (fun s => s.RIP = 0x100928) (andR64R64Effect 0x100928 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[176, 185]
    (.letOp (n := 189) (.out 0x10092b (movR64Imm64Effect 0x10092b 10 0xfff0fff0fff0fff0) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 190) (.exec 0x10092b (fun s => s.RIP = 0x10092b) (movR64Imm64Effect 0x10092b 10 0xfff0fff0fff0fff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 191) (.out 0x100935 (andR64R64Effect 0x100935 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[183, 189]
    (.letOp (n := 192) (.exec 0x100935 (fun s => s.RIP = 0x100935) (andR64R64Effect 0x100935 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[183, 189]
    (.letOp (n := 193) (.out 0x100938 (orR64R64Effect 0x100938 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[191, 187]
    (.letOp (n := 194) (.exec 0x100938 (fun s => s.RIP = 0x100938) (orR64R64Effect 0x100938 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[191, 187]
    (.letOp (n := 195) (.exec 0x10093b (StorePre 0x10093b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10093b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10093b 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[193, 65]
    (.letOp (n := 196) (.out 0x100940 (movR64M64Effect 0x100940 10 (.base 1 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[67]
    (.letOp (n := 197) (.exec 0x100940 (LoadPre 0x100940 (fun s => AddrMode.addr (.base 1 (.d8 0x38)) s (0x100940 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100940 10 (.base 1 (.d8 0x38))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 198) (.out 0x100944 (movR64R64Effect 0x100944 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[196]
    (.letOp (n := 199) (.exec 0x100944 (fun s => s.RIP = 0x100944) (movR64R64Effect 0x100944 6 10) (Reg.operands [.gpr 10] [])) #v[196]
    (.letOp (n := 200) (.out 0x100947 (rolR64Effect 0x100947 4 6 36) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[198]
    (.letOp (n := 201) (.exec 0x100947 (fun s => s.RIP = 0x100947) (rolR64Effect 0x100947 4 6 36) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[198]
    (.letOp (n := 202) (.out 0x10094b (movR64Imm64Effect 0x10094b 0 0xf000f000f000f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 203) (.exec 0x10094b (fun s => s.RIP = 0x10094b) (movR64Imm64Effect 0x10094b 0 0xf000f000f000f) (Reg.operands [] [])) #v[]
    (.letOp (n := 204) (.out 0x100955 (andR64R64Effect 0x100955 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[200, 202]
    (.letOp (n := 205) (.exec 0x100955 (fun s => s.RIP = 0x100955) (andR64R64Effect 0x100955 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[200, 202]
    (.letOp (n := 206) (.out 0x100958 (movR64R64Effect 0x100958 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[196]
    (.letOp (n := 207) (.exec 0x100958 (fun s => s.RIP = 0x100958) (movR64R64Effect 0x100958 0 10) (Reg.operands [.gpr 10] [])) #v[196]
    (b_l100830_4))))))))))))))))))))))))))))))))))))))

def bytes_l100830_3 : List UInt8 :=
  [0x48, 0x21, 0xE8, 0x48, 0x8B, 0x69, 0x30, 0x48, 0x89, 0xEE, 0x48, 0xC1, 0xC6, 0x24, 0x4C, 0x09,
    0xD0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xE8, 0x48, 0xC1, 0xC0, 0x34, 0x49, 0xBA, 0x0F,
    0x00, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x4C, 0x21, 0xD6, 0x49, 0xBA, 0xF0, 0xFF, 0xF0, 0xFF,
    0xF0, 0xFF, 0xF0, 0xFF, 0x4C, 0x21, 0xD0, 0x48, 0x09, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C,
    0x8B, 0x51, 0x38, 0x4C, 0x89, 0xD6, 0x48, 0xC1, 0xC6, 0x24, 0x48, 0xB8, 0x0F, 0x00, 0x0F, 0x00,
    0x0F, 0x00, 0x0F, 0x00, 0x48, 0x21, 0xC6, 0x4C, 0x89, 0xD0] ++ bytes_l100830_4

theorem code_l100830_3 : ∀ x ∈ codeRange 0x100901 bytes_l100830_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x901 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_4

@[cfg_block] def b_l100830_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x1008be (orR64R64Effect 0x1008be 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[125, 119]
    (.letOp (n := 132) (.exec 0x1008be (fun s => s.RIP = 0x1008be) (orR64R64Effect 0x1008be 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[125, 119]
    (.letOp (n := 133) (.exec 0x1008c1 (StorePre 0x1008c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1008c1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1008c1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[131, 65]
    (.letOp (n := 134) (.out 0x1008c6 (movR64R64Effect 0x1008c6 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[75]
    (.letOp (n := 135) (.exec 0x1008c6 (fun s => s.RIP = 0x1008c6) (movR64R64Effect 0x1008c6 13 7) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 136) (.out 0x1008c9 (rolR64Effect 0x1008c9 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[134]
    (.letOp (n := 137) (.exec 0x1008c9 (fun s => s.RIP = 0x1008c9) (rolR64Effect 0x1008c9 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 138) (.out 0x1008cd (andR64R64Effect 0x1008cd 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[129, 86]
    (.letOp (n := 139) (.exec 0x1008cd (fun s => s.RIP = 0x1008cd) (andR64R64Effect 0x1008cd 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[129, 86]
    (.letOp (n := 140) (.out 0x1008d0 (andR64R64Effect 0x1008d0 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[136, 94]
    (.letOp (n := 141) (.exec 0x1008d0 (fun s => s.RIP = 0x1008d0) (andR64R64Effect 0x1008d0 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[136, 94]
    (.letOp (n := 142) (.out 0x1008d3 (orR64R64Effect 0x1008d3 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[140, 138]
    (.letOp (n := 143) (.exec 0x1008d3 (fun s => s.RIP = 0x1008d3) (orR64R64Effect 0x1008d3 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[140, 138]
    (.letOp (n := 144) (.out 0x1008d6 (movR64R64Effect 0x1008d6 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[77]
    (.letOp (n := 145) (.exec 0x1008d6 (fun s => s.RIP = 0x1008d6) (movR64R64Effect 0x1008d6 6 11) (Reg.operands [.gpr 11] [])) #v[77]
    (.letOp (n := 146) (.out 0x1008d9 (rolR64Effect 0x1008d9 4 6 36) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[144]
    (.letOp (n := 147) (.exec 0x1008d9 (fun s => s.RIP = 0x1008d9) (rolR64Effect 0x1008d9 4 6 36) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[144]
    (.letOp (n := 148) (.out 0x1008dd (andR64R64Effect 0x1008dd 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[146, 86]
    (.letOp (n := 149) (.exec 0x1008dd (fun s => s.RIP = 0x1008dd) (andR64R64Effect 0x1008dd 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[146, 86]
    (.letOp (n := 150) (.out 0x1008e0 (movR64R64Effect 0x1008e0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[86]
    (.letOp (n := 151) (.exec 0x1008e0 (fun s => s.RIP = 0x1008e0) (movR64R64Effect 0x1008e0 0 15) (Reg.operands [.gpr 15] [])) #v[86]
    (.letOp (n := 152) (.out 0x1008e3 (movR64R64Effect 0x1008e3 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 153) (.exec 0x1008e3 (fun s => s.RIP = 0x1008e3) (movR64R64Effect 0x1008e3 15 11) (Reg.operands [.gpr 11] [])) #v[77]
    (.letOp (n := 154) (.out 0x1008e6 (rolR64Effect 0x1008e6 4 15 52) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[152]
    (.letOp (n := 155) (.exec 0x1008e6 (fun s => s.RIP = 0x1008e6) (rolR64Effect 0x1008e6 4 15 52) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[152]
    (.letOp (n := 156) (.out 0x1008ea (andR64R64Effect 0x1008ea 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[154, 94]
    (.letOp (n := 157) (.exec 0x1008ea (fun s => s.RIP = 0x1008ea) (andR64R64Effect 0x1008ea 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[154, 94]
    (.letOp (n := 158) (.out 0x1008ed (orR64R64Effect 0x1008ed 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[156, 148]
    (.letOp (n := 159) (.exec 0x1008ed (fun s => s.RIP = 0x1008ed) (orR64R64Effect 0x1008ed 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[156, 148]
    (.letOp (n := 160) (.out 0x1008f0 (movR64R64Effect 0x1008f0 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[79]
    (.letOp (n := 161) (.exec 0x1008f0 (fun s => s.RIP = 0x1008f0) (movR64R64Effect 0x1008f0 10 14) (Reg.operands [.gpr 14] [])) #v[79]
    (.letOp (n := 162) (.out 0x1008f3 (rolR64Effect 0x1008f3 4 10 36) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[160]
    (.letOp (n := 163) (.exec 0x1008f3 (fun s => s.RIP = 0x1008f3) (rolR64Effect 0x1008f3 4 10 36) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[160]
    (.letOp (n := 164) (.out 0x1008f7 (andR64R64Effect 0x1008f7 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[162, 150]
    (.letOp (n := 165) (.exec 0x1008f7 (fun s => s.RIP = 0x1008f7) (andR64R64Effect 0x1008f7 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[162, 150]
    (.letOp (n := 166) (.out 0x1008fa (movR64R64Effect 0x1008fa 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 167) (.exec 0x1008fa (fun s => s.RIP = 0x1008fa) (movR64R64Effect 0x1008fa 0 14) (Reg.operands [.gpr 14] [])) #v[79]
    (.letOp (n := 168) (.out 0x1008fd (rolR64Effect 0x1008fd 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[166]
    (.letOp (n := 169) (.exec 0x1008fd (fun s => s.RIP = 0x1008fd) (rolR64Effect 0x1008fd 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[166]
    (b_l100830_3)))))))))))))))))))))))))))))))))))))))

def bytes_l100830_2 : List UInt8 :=
  [0x48, 0x09, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x49, 0x89, 0xFD, 0x49, 0xC1, 0xC5, 0x34, 0x4D,
    0x21, 0xFA, 0x49, 0x21, 0xED, 0x4D, 0x09, 0xD5, 0x4C, 0x89, 0xDE, 0x48, 0xC1, 0xC6, 0x24, 0x4C,
    0x21, 0xFE, 0x4C, 0x89, 0xF8, 0x4D, 0x89, 0xDF, 0x49, 0xC1, 0xC7, 0x34, 0x49, 0x21, 0xEF, 0x49,
    0x09, 0xF7, 0x4D, 0x89, 0xF2, 0x49, 0xC1, 0xC2, 0x24, 0x49, 0x21, 0xC2, 0x4C, 0x89, 0xF0, 0x48,
    0xC1, 0xC0, 0x34] ++ bytes_l100830_3

theorem code_l100830_2 : ∀ x ∈ codeRange 0x1008be bytes_l100830_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8be 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_3

@[cfg_block] def b_l100830_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x100875 (andR64R64Effect 0x100875 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[84, 86]
    (.letOp (n := 93) (.exec 0x100875 (fun s => s.RIP = 0x100875) (andR64R64Effect 0x100875 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[84, 86]
    (.letOp (n := 94) (.out 0x100878 (movR64Imm64Effect 0x100878 5 0xfff0fff0fff0fff0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 95) (.exec 0x100878 (fun s => s.RIP = 0x100878) (movR64Imm64Effect 0x100878 5 0xfff0fff0fff0fff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.out 0x100882 (andR64R64Effect 0x100882 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[90, 94]
    (.letOp (n := 97) (.exec 0x100882 (fun s => s.RIP = 0x100882) (andR64R64Effect 0x100882 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[90, 94]
    (.letOp (n := 98) (.out 0x100885 (orR64R64Effect 0x100885 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[96, 92]
    (.letOp (n := 99) (.exec 0x100885 (fun s => s.RIP = 0x100885) (orR64R64Effect 0x100885 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[96, 92]
    (.letOp (n := 100) (.out 0x100888 (movR64R64Effect 0x100888 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 101) (.exec 0x100888 (fun s => s.RIP = 0x100888) (movR64R64Effect 0x100888 6 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 102) (.out 0x10088b (rolR64Effect 0x10088b 4 6 36) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[100]
    (.letOp (n := 103) (.exec 0x10088b (fun s => s.RIP = 0x10088b) (rolR64Effect 0x10088b 4 6 36) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100]
    (.letOp (n := 104) (.out 0x10088f (andR64R64Effect 0x10088f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[102, 86]
    (.letOp (n := 105) (.exec 0x10088f (fun s => s.RIP = 0x10088f) (andR64R64Effect 0x10088f 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[102, 86]
    (.letOp (n := 106) (.out 0x100892 (movR64R64Effect 0x100892 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 107) (.exec 0x100892 (fun s => s.RIP = 0x100892) (movR64R64Effect 0x100892 0 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 108) (.out 0x100895 (rolR64Effect 0x100895 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[106]
    (.letOp (n := 109) (.exec 0x100895 (fun s => s.RIP = 0x100895) (rolR64Effect 0x100895 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[106]
    (.letOp (n := 110) (.out 0x100899 (andR64R64Effect 0x100899 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[108, 94]
    (.letOp (n := 111) (.exec 0x100899 (fun s => s.RIP = 0x100899) (andR64R64Effect 0x100899 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[108, 94]
    (.letOp (n := 112) (.out 0x10089c (orR64R64Effect 0x10089c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[110, 104]
    (.letOp (n := 113) (.exec 0x10089c (fun s => s.RIP = 0x10089c) (orR64R64Effect 0x10089c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[110, 104]
    (.letOp (n := 114) (.exec 0x10089f (StorePre 0x10089f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10089f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10089f 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[112, 65]
    (.letOp (n := 115) (.out 0x1008a3 (movR64R64Effect 0x1008a3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 116) (.exec 0x1008a3 (fun s => s.RIP = 0x1008a3) (movR64R64Effect 0x1008a3 6 9) (Reg.operands [.gpr 9] [])) #v[73]
    (.letOp (n := 117) (.out 0x1008a6 (rolR64Effect 0x1008a6 4 6 36) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[115]
    (.letOp (n := 118) (.exec 0x1008a6 (fun s => s.RIP = 0x1008a6) (rolR64Effect 0x1008a6 4 6 36) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x1008aa (andR64R64Effect 0x1008aa 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[117, 86]
    (.letOp (n := 120) (.exec 0x1008aa (fun s => s.RIP = 0x1008aa) (andR64R64Effect 0x1008aa 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[117, 86]
    (.letOp (n := 121) (.out 0x1008ad (movR64R64Effect 0x1008ad 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 122) (.exec 0x1008ad (fun s => s.RIP = 0x1008ad) (movR64R64Effect 0x1008ad 0 9) (Reg.operands [.gpr 9] [])) #v[73]
    (.letOp (n := 123) (.out 0x1008b0 (rolR64Effect 0x1008b0 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[121]
    (.letOp (n := 124) (.exec 0x1008b0 (fun s => s.RIP = 0x1008b0) (rolR64Effect 0x1008b0 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 125) (.out 0x1008b4 (andR64R64Effect 0x1008b4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[123, 94]
    (.letOp (n := 126) (.exec 0x1008b4 (fun s => s.RIP = 0x1008b4) (andR64R64Effect 0x1008b4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[123, 94]
    (.letOp (n := 127) (.out 0x1008b7 (movR64R64Effect 0x1008b7 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[75]
    (.letOp (n := 128) (.exec 0x1008b7 (fun s => s.RIP = 0x1008b7) (movR64R64Effect 0x1008b7 10 7) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 129) (.out 0x1008ba (rolR64Effect 0x1008ba 4 10 36) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[127]
    (.letOp (n := 130) (.exec 0x1008ba (fun s => s.RIP = 0x1008ba) (rolR64Effect 0x1008ba 4 10 36) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (b_l100830_2)))))))))))))))))))))))))))))))))))))))

def bytes_l100830_1 : List UInt8 :=
  [0x4C, 0x21, 0xFE, 0x48, 0xBD, 0xF0, 0xFF, 0xF0, 0xFF, 0xF0, 0xFF, 0xF0, 0xFF, 0x49, 0x21, 0xEC,
    0x49, 0x09, 0xF4, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xC6, 0x24, 0x4C, 0x21, 0xFE, 0x4C, 0x89, 0xC0,
    0x48, 0xC1, 0xC0, 0x34, 0x48, 0x21, 0xE8, 0x48, 0x09, 0xF0, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x89,
    0xCE, 0x48, 0xC1, 0xC6, 0x24, 0x4C, 0x21, 0xFE, 0x4C, 0x89, 0xC8, 0x48, 0xC1, 0xC0, 0x34, 0x48,
    0x21, 0xE8, 0x49, 0x89, 0xFA, 0x49, 0xC1, 0xC2, 0x24] ++ bytes_l100830_2

theorem code_l100830_1 : ∀ x ∈ codeRange 0x100875 bytes_l100830_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x875 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_2

@[cfg_block] def b_l100830 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100830 (pushR64Effect 0x100830 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100830 (PushPre 0x100830 1) (pushR64Effect 0x100830 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100831 (pushR64Effect 0x100831 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100831 (PushPre 0x100831 2) (pushR64Effect 0x100831 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100833 (pushR64Effect 0x100833 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100833 (PushPre 0x100833 2) (pushR64Effect 0x100833 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100835 (pushR64Effect 0x100835 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100835 (PushPre 0x100835 2) (pushR64Effect 0x100835 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100837 (pushR64Effect 0x100837 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100837 (PushPre 0x100837 2) (pushR64Effect 0x100837 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100839 (pushR64Effect 0x100839 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100839 (PushPre 0x100839 1) (pushR64Effect 0x100839 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10083a (subR64Imm8Effect 0x10083a 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10083a (fun s => s.RIP = 0x10083a) (subR64Imm8Effect 0x10083a 4 0x30) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10083e (movR64R64Effect 0x10083e 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 68) (.exec 0x10083e (fun s => s.RIP = 0x10083e) (movR64R64Effect 0x10083e 1 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x100841 (movR64M64Effect 0x100841 2 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 70) (.exec 0x100841 (LoadPre 0x100841 (fun s => AddrMode.addr (.base 7 .none) s (0x100841 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100841 2 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x100844 (movR64M64Effect 0x100844 8 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 72) (.exec 0x100844 (LoadPre 0x100844 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100844 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100844 8 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x100848 (movR64M64Effect 0x100848 9 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 74) (.exec 0x100848 (LoadPre 0x100848 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100848 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100848 9 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x10084c (movR64M64Effect 0x10084c 7 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 76) (.exec 0x10084c (LoadPre 0x10084c (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10084c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10084c 7 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.out 0x100850 (movR64M64Effect 0x100850 11 (.base 1 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 78) (.exec 0x100850 (LoadPre 0x100850 (fun s => AddrMode.addr (.base 1 (.d8 0x20)) s (0x100850 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100850 11 (.base 1 (.d8 0x20))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 79) (.out 0x100854 (movR64M64Effect 0x100854 14 (.base 1 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 80) (.exec 0x100854 (LoadPre 0x100854 (fun s => AddrMode.addr (.base 1 (.d8 0x28)) s (0x100854 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100854 14 (.base 1 (.d8 0x28))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 81) (.exec 0x100858 (StorePre 0x100858 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100858 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100858 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 65]
    (.letOp (n := 82) (.out 0x10085d (movR64R64Effect 0x10085d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 83) (.exec 0x10085d (fun s => s.RIP = 0x10085d) (movR64R64Effect 0x10085d 6 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 84) (.out 0x100860 (rolR64Effect 0x100860 4 6 36) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[82]
    (.letOp (n := 85) (.exec 0x100860 (fun s => s.RIP = 0x100860) (rolR64Effect 0x100860 4 6 36) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (.letOp (n := 86) (.out 0x100864 (movR64Imm64Effect 0x100864 15 0xf000f000f000f) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 87) (.exec 0x100864 (fun s => s.RIP = 0x100864) (movR64Imm64Effect 0x100864 15 0xf000f000f000f) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x10086e (movR64R64Effect 0x10086e 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[69]
    (.letOp (n := 89) (.exec 0x10086e (fun s => s.RIP = 0x10086e) (movR64R64Effect 0x10086e 12 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 90) (.out 0x100871 (rolR64Effect 0x100871 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[88]
    (.letOp (n := 91) (.exec 0x100871 (fun s => s.RIP = 0x100871) (rolR64Effect 0x100871 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (b_l100830_1)))))))))))))))))))))))))))))))))))))))

def bytes_l100830 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89,
    0xF9, 0x48, 0x8B, 0x17, 0x4C, 0x8B, 0x47, 0x08, 0x4C, 0x8B, 0x4F, 0x10, 0x48, 0x8B, 0x7F, 0x18,
    0x4C, 0x8B, 0x59, 0x20, 0x4C, 0x8B, 0x71, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0xD6,
    0x48, 0xC1, 0xC6, 0x24, 0x49, 0xBF, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x49, 0x89,
    0xD4, 0x49, 0xC1, 0xC4, 0x34] ++ bytes_l100830_1

theorem code_l100830 : ∀ x ∈ codeRange 0x100830 bytes_l100830, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x830 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100830_1

@[cfg_block] def b_l100b10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b10 (pushR64Effect 0x100b10 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100b10 (PushPre 0x100b10 1) (pushR64Effect 0x100b10 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100b11 (pushR64Effect 0x100b11 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100b11 (PushPre 0x100b11 2) (pushR64Effect 0x100b11 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100b13 (pushR64Effect 0x100b13 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100b13 (PushPre 0x100b13 2) (pushR64Effect 0x100b13 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100b15 (pushR64Effect 0x100b15 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100b15 (PushPre 0x100b15 2) (pushR64Effect 0x100b15 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100b17 (pushR64Effect 0x100b17 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100b17 (PushPre 0x100b17 2) (pushR64Effect 0x100b17 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100b19 (pushR64Effect 0x100b19 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100b19 (PushPre 0x100b19 1) (pushR64Effect 0x100b19 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x100b1a (subR64Imm8Effect 0x100b1a 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x100b1a (fun s => s.RIP = 0x100b1a) (subR64Imm8Effect 0x100b1a 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100b1e (testR64R64Effect 0x100b1e 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 68) (.exec 0x100b1e (fun s => s.RIP = 0x100b1e) (testR64R64Effect 0x100b1e 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.pure (condOp 4)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l100de6, RegMap.args [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l100b27, RegMap.args [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l100b10 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x48, 0x85,
    0xF6, 0x0F, 0x84, 0xBF, 0x02, 0x00, 0x00]

theorem code_l100b10 : ∀ x ∈ codeRange 0x100b10 bytes_l100b10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb10 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b27 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b27 (cmpR64Imm8Effect 0x100b27 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100b27 (fun s => s.RIP = 0x100b27) (cmpR64Imm8Effect 0x100b27 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100df6, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100b31, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100b27 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x01, 0x0F, 0x84, 0xC5, 0x02, 0x00, 0x00]

theorem code_l100b27 : ∀ x ∈ codeRange 0x100b27 bytes_l100b27, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb27 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b31 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b31 (cmpR64Imm8Effect 0x100b31 6 0x2) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 54) (.out 0x100b31 (cmpR64Imm8Effect 0x100b31 6 0x2) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 55) (.exec 0x100b31 (fun s => s.RIP = 0x100b31) (cmpR64Imm8Effect 0x100b31 6 0x2) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l100e0c, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100b3b, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100b31 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x02, 0x0F, 0x86, 0xD1, 0x02, 0x00, 0x00]

theorem code_l100b31 : ∀ x ∈ codeRange 0x100b31 bytes_l100b31, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb31 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b3b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b3b (cmpR64Imm8Effect 0x100b3b 6 0x3) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100b3b (fun s => s.RIP = 0x100b3b) (cmpR64Imm8Effect 0x100b3b 6 0x3) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100e22, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100b45, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100b3b : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x03, 0x0F, 0x84, 0xDD, 0x02, 0x00, 0x00]

theorem code_l100b3b : ∀ x ∈ codeRange 0x100b3b bytes_l100b3b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb3b 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b45 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b45 (cmpR64Imm8Effect 0x100b45 6 0x4) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 54) (.out 0x100b45 (cmpR64Imm8Effect 0x100b45 6 0x4) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 55) (.exec 0x100b45 (fun s => s.RIP = 0x100b45) (cmpR64Imm8Effect 0x100b45 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l100e38, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100b4f, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100b45 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x04, 0x0F, 0x86, 0xE9, 0x02, 0x00, 0x00]

theorem code_l100b45 : ∀ x ∈ codeRange 0x100b45 bytes_l100b45, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb45 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b4f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b4f (cmpR64Imm8Effect 0x100b4f 6 0x5) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100b4f (fun s => s.RIP = 0x100b4f) (cmpR64Imm8Effect 0x100b4f 6 0x5) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100e4e, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100b59, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100b4f : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x05, 0x0F, 0x84, 0xF5, 0x02, 0x00, 0x00]

theorem code_l100b4f : ∀ x ∈ codeRange 0x100b4f bytes_l100b4f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb4f 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b59 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b59 (cmpR64Imm8Effect 0x100b59 6 0x6) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 54) (.out 0x100b59 (cmpR64Imm8Effect 0x100b59 6 0x6) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 55) (.exec 0x100b59 (fun s => s.RIP = 0x100b59) (cmpR64Imm8Effect 0x100b59 6 0x6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l100e64, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100b63, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100b59 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x06, 0x0F, 0x86, 0x01, 0x03, 0x00, 0x00]

theorem code_l100b59 : ∀ x ∈ codeRange 0x100b59 bytes_l100b59, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb59 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b63 (cmpR64Imm8Effect 0x100b63 6 0x7) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100b63 (fun s => s.RIP = 0x100b63) (cmpR64Imm8Effect 0x100b63 6 0x7) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100e7a, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100b6d, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100b63 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x07, 0x0F, 0x84, 0x0D, 0x03, 0x00, 0x00]

theorem code_l100b63 : ∀ x ∈ codeRange 0x100b63 bytes_l100b63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb63 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b6d_9 : Block Op Label signature Reg.count 393 :=
  .letOp (n := 393) (.exec 0x100da9 (StorePre 0x100da9 5 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x100da9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100da9 5 10 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[391, 53]
    (.letOp (n := 394) (.out 0x100dae (xorR32R32Effect 0x100dae 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[325, 357]
    (.letOp (n := 395) (.exec 0x100dae (fun s => s.RIP = 0x100dae) (xorR32R32Effect 0x100dae 3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[325, 357]
    (.letOp (n := 396) (.out 0x100db1 (xorR32R32Effect 0x100db1 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[375, 394]
    (.letOp (n := 397) (.exec 0x100db1 (fun s => s.RIP = 0x100db1) (xorR32R32Effect 0x100db1 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[375, 394]
    (.letOp (n := 398) (.exec 0x100db4 (StorePre 0x100db4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x100db4 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100db4 4 1 (.base 3 (.d8 0x6))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[396, 53]
    (.letOp (n := 399) (.out 0x100db8 (xorR32R32Effect 0x100db8 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[357, 363]
    (.letOp (n := 400) (.exec 0x100db8 (fun s => s.RIP = 0x100db8) (xorR32R32Effect 0x100db8 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[357, 363]
    (.letOp (n := 401) (.exec 0x100dbb (StorePre 0x100dbb 5 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100dbb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100dbb 5 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[394, 53]
    (.letOp (n := 402) (.out 0x100dc0 (xorR32R32Effect 0x100dc0 3 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[394, 363]
    (.letOp (n := 403) (.exec 0x100dc0 (fun s => s.RIP = 0x100dc0) (xorR32R32Effect 0x100dc0 3 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[394, 363]
    (.letOp (n := 404) (.out 0x100dc3 (xorR32R32Effect 0x100dc3 3 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[371, 363]
    (.letOp (n := 405) (.exec 0x100dc3 (fun s => s.RIP = 0x100dc3) (xorR32R32Effect 0x100dc3 3 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[371, 363]
    (.letOp (n := 406) (.out 0x100dc6 (xorR32R32Effect 0x100dc6 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[404, 383]
    (.letOp (n := 407) (.exec 0x100dc6 (fun s => s.RIP = 0x100dc6) (xorR32R32Effect 0x100dc6 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[404, 383]
    (.letOp (n := 408) (.exec 0x100dc9 (StorePre 0x100dc9 5 (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x100dc9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100dc9 5 13 (.base 3 (.d8 0xa))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[406, 53]
    (.letOp (n := 409) (.exec 0x100dce (StorePre 0x100dce 5 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x100dce + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100dce 5 12 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[402, 53]
    (.letOp (n := 410) (.exec 0x100dd3 (StorePre 0x100dd3 4 (fun s => AddrMode.addr (.base 3 (.d8 0xe)) s (0x100dd3 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100dd3 4 2 (.base 3 (.d8 0xe))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[399, 53]
    (.letOp (n := 411) (.out 0x100dd7 (addR64Imm8Effect 0x100dd7 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 412) (.exec 0x100dd7 (fun s => s.RIP = 0x100dd7) (addR64Imm8Effect 0x100dd7 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 413) (.out 0x100ddb (popR64Effect 0x100ddb 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[411]
    (.letOp (n := 414) (.out 0x100ddb (popR64Effect 0x100ddb 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[411]
    (.letOp (n := 415) (.exec 0x100ddb (PopPre 0x100ddb) (popR64Effect 0x100ddb 1 3) (Reg.operands [.gpr 4] [])) #v[411]
    (.letOp (n := 416) (.out 0x100ddc (popR64Effect 0x100ddc 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[414]
    (.letOp (n := 417) (.out 0x100ddc (popR64Effect 0x100ddc 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[414]
    (.letOp (n := 418) (.exec 0x100ddc (PopPre 0x100ddc) (popR64Effect 0x100ddc 2 12) (Reg.operands [.gpr 4] [])) #v[414]
    (.letOp (n := 419) (.out 0x100dde (popR64Effect 0x100dde 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[417]
    (.letOp (n := 420) (.out 0x100dde (popR64Effect 0x100dde 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[417]
    (.letOp (n := 421) (.exec 0x100dde (PopPre 0x100dde) (popR64Effect 0x100dde 2 13) (Reg.operands [.gpr 4] [])) #v[417]
    (.letOp (n := 422) (.out 0x100de0 (popR64Effect 0x100de0 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[420]
    (.letOp (n := 423) (.out 0x100de0 (popR64Effect 0x100de0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[420]
    (.letOp (n := 424) (.exec 0x100de0 (PopPre 0x100de0) (popR64Effect 0x100de0 2 14) (Reg.operands [.gpr 4] [])) #v[420]
    (.letOp (n := 425) (.out 0x100de2 (popR64Effect 0x100de2 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[423]
    (.letOp (n := 426) (.out 0x100de2 (popR64Effect 0x100de2 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[423]
    (.letOp (n := 427) (.exec 0x100de2 (PopPre 0x100de2) (popR64Effect 0x100de2 2 15) (Reg.operands [.gpr 4] [])) #v[423]
    (.letOp (n := 428) (.out 0x100de4 (popR64Effect 0x100de4 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[426]
    (.letOp (n := 429) (.out 0x100de4 (popR64Effect 0x100de4 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[426]
    (.letOp (n := 430) (.exec 0x100de4 (PopPre 0x100de4) (popR64Effect 0x100de4 1 5) (Reg.operands [.gpr 4] [])) #v[426]
    (.letOp (n := 431) (.out 0x100de5 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[429]
    (.letOp (n := 432) (.out 0x100de5 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[429]
    (.letOp (n := 433) (.exec 0x100de5 (RetPre 0x100de5) (retEffect) (Reg.operands [.gpr 4] [])) #v[429]
    (.terminate (.ret (RegMap.args [(0, 383), (1, 396), (2, 399), (3, 413), (4, 432), (5, 428), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 419), (14, 422), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)] 434) (some ⟨431, by decide⟩)))))))))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_9 : List UInt8 :=
  [0x66, 0x44, 0x89, 0x53, 0x04, 0x41, 0x31, 0xD4, 0x44, 0x31, 0xE1, 0x66, 0x89, 0x4B, 0x06, 0x44,
    0x31, 0xF2, 0x66, 0x44, 0x89, 0x63, 0x08, 0x45, 0x31, 0xF4, 0x45, 0x31, 0xF5, 0x41, 0x31, 0xC5,
    0x66, 0x44, 0x89, 0x6B, 0x0A, 0x66, 0x44, 0x89, 0x63, 0x0C, 0x66, 0x89, 0x53, 0x0E, 0x48, 0x83,
    0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l100b6d_9 : ∀ x ∈ codeRange 0x100da9 bytes_l100b6d_9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xda9 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b6d_8 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x100d6a (xorR32R32Effect 0x100d6a 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[349, 353]
    (.letOp (n := 356) (.exec 0x100d6a (fun s => s.RIP = 0x100d6a) (xorR32R32Effect 0x100d6a 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[349, 353]
    (.letOp (n := 357) (.out 0x100d6d (xorR32R32Effect 0x100d6d 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[353, 300]
    (.letOp (n := 358) (.exec 0x100d6d (fun s => s.RIP = 0x100d6d) (xorR32R32Effect 0x100d6d 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[353, 300]
    (.letOp (n := 359) (.out 0x100d6f (andR32M32Effect 0x100d6f 4 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[274, 4]
    (.letOp (n := 360) (.exec 0x100d6f (LoadPre 0x100d6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100d6f + BitVec.ofNat 64 4)) 4) (andR32M32Effect 0x100d6f 4 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[274, 4]
    (.letOp (n := 361) (.out 0x100d73 (xorR32R32Effect 0x100d73 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[359, 296]
    (.letOp (n := 362) (.exec 0x100d73 (fun s => s.RIP = 0x100d73) (xorR32R32Effect 0x100d73 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[359, 296]
    (.letOp (n := 363) (.out 0x100d76 (xorR32R32Effect 0x100d76 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[343, 337]
    (.letOp (n := 364) (.exec 0x100d76 (fun s => s.RIP = 0x100d76) (xorR32R32Effect 0x100d76 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[343, 337]
    (.letOp (n := 365) (.out 0x100d79 (xorR32R32Effect 0x100d79 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[320, 361]
    (.letOp (n := 366) (.exec 0x100d79 (fun s => s.RIP = 0x100d79) (xorR32R32Effect 0x100d79 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[320, 361]
    (.letOp (n := 367) (.out 0x100d7c (xorR32R32Effect 0x100d7c 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[365, 290]
    (.letOp (n := 368) (.exec 0x100d7c (fun s => s.RIP = 0x100d7c) (xorR32R32Effect 0x100d7c 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[365, 290]
    (.letOp (n := 369) (.out 0x100d7f (xorR32R32Effect 0x100d7f 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[367, 337]
    (.letOp (n := 370) (.exec 0x100d7f (fun s => s.RIP = 0x100d7f) (xorR32R32Effect 0x100d7f 3 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[367, 337]
    (.letOp (n := 371) (.out 0x100d82 (xorR32M32Effect 0x100d82 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[345, 4]
    (.letOp (n := 372) (.exec 0x100d82 (LoadPre 0x100d82 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100d82 + BitVec.ofNat 64 4)) 4) (xorR32M32Effect 0x100d82 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[345, 4]
    (.letOp (n := 373) (.out 0x100d86 (xorR32M32LowEffect 0x100d86 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[361, 4]
    (.letOp (n := 374) (.exec 0x100d86 (LoadPre 0x100d86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100d86 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x100d86 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[361, 4]
    (.letOp (n := 375) (.out 0x100d8a (xorR32R32Effect 0x100d8a 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[373, 318]
    (.letOp (n := 376) (.exec 0x100d8a (fun s => s.RIP = 0x100d8a) (xorR32R32Effect 0x100d8a 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[373, 318]
    (.letOp (n := 377) (.out 0x100d8d (xorR32R32Effect 0x100d8d 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[302, 375]
    (.letOp (n := 378) (.exec 0x100d8d (fun s => s.RIP = 0x100d8d) (xorR32R32Effect 0x100d8d 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[302, 375]
    (.letOp (n := 379) (.out 0x100d8f (xorR32R32Effect 0x100d8f 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[377, 351]
    (.letOp (n := 380) (.exec 0x100d8f (fun s => s.RIP = 0x100d8f) (xorR32R32Effect 0x100d8f 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[377, 351]
    (.letOp (n := 381) (.out 0x100d91 (movR32M32LowEffect 0x100d91 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 382) (.exec 0x100d91 (LoadPre 0x100d91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100d91 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100d91 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 383) (.out 0x100d95 (xorR32R32Effect 0x100d95 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[381, 369]
    (.letOp (n := 384) (.exec 0x100d95 (fun s => s.RIP = 0x100d95) (xorR32R32Effect 0x100d95 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[381, 369]
    (.letOp (n := 385) (.out 0x100d98 (xorR32R32Effect 0x100d98 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[369, 379]
    (.letOp (n := 386) (.exec 0x100d98 (fun s => s.RIP = 0x100d98) (xorR32R32Effect 0x100d98 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[369, 379]
    (.letOp (n := 387) (.out 0x100d9b (xorR32R32Effect 0x100d9b 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[379, 290]
    (.letOp (n := 388) (.exec 0x100d9b (fun s => s.RIP = 0x100d9b) (xorR32R32Effect 0x100d9b 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[379, 290]
    (.letOp (n := 389) (.exec 0x100d9e (StorePre 0x100d9e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x100d9e + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x100d9e 3 7 (.base 3 .none)) (Reg.operands [.gpr 7, .gpr 3] [])) #v[387, 53]
    (.letOp (n := 390) (.exec 0x100da1 (StorePre 0x100da1 5 (fun s => AddrMode.addr (.base 3 (.d8 0x2)) s (0x100da1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100da1 5 8 (.base 3 (.d8 0x2))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[385, 53]
    (.letOp (n := 391) (.out 0x100da6 (xorR32R32Effect 0x100da6 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[355, 383]
    (.letOp (n := 392) (.exec 0x100da6 (fun s => s.RIP = 0x100da6) (xorR32R32Effect 0x100da6 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[355, 383]
    (b_l100b6d_9))))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_8 : List UInt8 :=
  [0x41, 0x31, 0xD2, 0x31, 0xF2, 0x23, 0x4C, 0x24, 0x24, 0x44, 0x31, 0xD9, 0x41, 0x31, 0xEE, 0x41,
    0x31, 0xC8, 0x45, 0x31, 0xC8, 0x41, 0x31, 0xE8, 0x44, 0x33, 0x2C, 0x24, 0x33, 0x4C, 0x24, 0x0C,
    0x44, 0x31, 0xF9, 0x31, 0xCF, 0x31, 0xC7, 0x8B, 0x44, 0x24, 0x10, 0x44, 0x31, 0xC0, 0x41, 0x31,
    0xF8, 0x44, 0x31, 0xCF, 0x66, 0x89, 0x3B, 0x66, 0x44, 0x89, 0x43, 0x02, 0x41, 0x31, 0xC2] ++ bytes_l100b6d_9

theorem code_l100b6d_8 : ∀ x ∈ codeRange 0x100d6a bytes_l100b6d_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd6a 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_9

@[cfg_block] def b_l100b6d_7 : Block Op Label signature Reg.count 316 :=
  .letOp (n := 316) (.out 0x100d26 (xorR32R32Effect 0x100d26 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[304, 288]
    (.letOp (n := 317) (.exec 0x100d26 (fun s => s.RIP = 0x100d26) (xorR32R32Effect 0x100d26 3 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[304, 288]
    (.letOp (n := 318) (.out 0x100d29 (movR32R32Effect 0x100d29 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[288]
    (.letOp (n := 319) (.exec 0x100d29 (fun s => s.RIP = 0x100d29) (movR32R32Effect 0x100d29 3 15 14) (Reg.operands [.gpr 14] [])) #v[288]
    (.letOp (n := 320) (.out 0x100d2c (andR32R32Effect 0x100d2c 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[127, 308]
    (.letOp (n := 321) (.exec 0x100d2c (fun s => s.RIP = 0x100d2c) (andR32R32Effect 0x100d2c 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[127, 308]
    (.letOp (n := 322) (.exec 0x100d2f (StorePre 0x100d2f 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100d2f + BitVec.ofNat 64 3)) 4) (andMREffect 0x100d2f 3 32 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[308, 4]
    (.letOp (n := 323) (.out 0x100d32 (xorR32R32Effect 0x100d32 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[312, 296]
    (.letOp (n := 324) (.exec 0x100d32 (fun s => s.RIP = 0x100d32) (xorR32R32Effect 0x100d32 3 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[312, 296]
    (.letOp (n := 325) (.out 0x100d35 (xorR32R32Effect 0x100d35 3 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[323, 316]
    (.letOp (n := 326) (.exec 0x100d35 (fun s => s.RIP = 0x100d35) (xorR32R32Effect 0x100d35 3 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[323, 316]
    (.letOp (n := 327) (.out 0x100d38 (xorR32R32Effect 0x100d38 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[272, 274]
    (.letOp (n := 328) (.exec 0x100d38 (fun s => s.RIP = 0x100d38) (xorR32R32Effect 0x100d38 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[272, 274]
    (.letOp (n := 329) (.out 0x100d3b (xorR32R32Effect 0x100d3b 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[308, 327]
    (.letOp (n := 330) (.exec 0x100d3b (fun s => s.RIP = 0x100d3b) (xorR32R32Effect 0x100d3b 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[308, 327]
    (.letOp (n := 331) (.out 0x100d3e (movR32M32Effect 0x100d3e 10 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 332) (.exec 0x100d3e (LoadPre 0x100d3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100d3e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100d3e 10 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 333) (.out 0x100d43 (andR32R32Effect 0x100d43 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[331, 329]
    (.letOp (n := 334) (.exec 0x100d43 (fun s => s.RIP = 0x100d43) (andR32R32Effect 0x100d43 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[331, 329]
    (.letOp (n := 335) (.out 0x100d46 (xorR32R32Effect 0x100d46 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[333, 316]
    (.letOp (n := 336) (.exec 0x100d46 (fun s => s.RIP = 0x100d46) (xorR32R32Effect 0x100d46 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[333, 316]
    (.letOp (n := 337) (.out 0x100d49 (movR32R32Effect 0x100d49 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[335]
    (.letOp (n := 338) (.exec 0x100d49 (fun s => s.RIP = 0x100d49) (movR32R32Effect 0x100d49 3 5 10) (Reg.operands [.gpr 10] [])) #v[335]
    (.letOp (n := 339) (.out 0x100d4c (andR32M32Effect 0x100d4c 4 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[329, 4]
    (.letOp (n := 340) (.exec 0x100d4c (LoadPre 0x100d4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100d4c + BitVec.ofNat 64 4)) 4) (andR32M32Effect 0x100d4c 4 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[329, 4]
    (.letOp (n := 341) (.out 0x100d50 (movR32M32Effect 0x100d50 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 342) (.exec 0x100d50 (LoadPre 0x100d50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100d50 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100d50 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 343) (.out 0x100d55 (andR32R32Effect 0x100d55 3 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[341, 327]
    (.letOp (n := 344) (.exec 0x100d55 (fun s => s.RIP = 0x100d55) (andR32R32Effect 0x100d55 3 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[341, 327]
    (.letOp (n := 345) (.out 0x100d58 (andR32M32Effect 0x100d58 5 13 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[327, 4]
    (.letOp (n := 346) (.exec 0x100d58 (LoadPre 0x100d58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100d58 + BitVec.ofNat 64 5)) 4) (andR32M32Effect 0x100d58 5 13 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[327, 4]
    (.letOp (n := 347) (.out 0x100d5d (movR32M32Effect 0x100d5d 10 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 348) (.exec 0x100d5d (LoadPre 0x100d5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100d5d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100d5d 10 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 349) (.out 0x100d62 (andR32R32Effect 0x100d62 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[347, 274]
    (.letOp (n := 350) (.exec 0x100d62 (fun s => s.RIP = 0x100d62) (andR32R32Effect 0x100d62 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[347, 274]
    (.letOp (n := 351) (.out 0x100d65 (xorR32R32Effect 0x100d65 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[339, 345]
    (.letOp (n := 352) (.exec 0x100d65 (fun s => s.RIP = 0x100d65) (xorR32R32Effect 0x100d65 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[339, 345]
    (.letOp (n := 353) (.out 0x100d68 (xorR32R32Effect 0x100d68 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[310, 351]
    (.letOp (n := 354) (.exec 0x100d68 (fun s => s.RIP = 0x100d68) (xorR32R32Effect 0x100d68 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[310, 351]
    (b_l100b6d_8)))))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_7 : List UInt8 :=
  [0x44, 0x31, 0xF5, 0x45, 0x89, 0xF7, 0x41, 0x21, 0xC0, 0x21, 0x04, 0x24, 0x45, 0x31, 0xDC, 0x41,
    0x31, 0xEC, 0x41, 0x31, 0xCD, 0x44, 0x31, 0xE8, 0x44, 0x8B, 0x54, 0x24, 0x2C, 0x41, 0x21, 0xC2,
    0x41, 0x31, 0xEA, 0x44, 0x89, 0xD5, 0x23, 0x44, 0x24, 0x30, 0x44, 0x8B, 0x74, 0x24, 0x28, 0x45,
    0x21, 0xEE, 0x44, 0x23, 0x6C, 0x24, 0x34, 0x44, 0x8B, 0x54, 0x24, 0x04, 0x41, 0x21, 0xCA, 0x44,
    0x31, 0xE8, 0x31, 0xC2] ++ bytes_l100b6d_8

theorem code_l100b6d_7 : ∀ x ∈ codeRange 0x100d26 bytes_l100b6d_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd26 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_8

@[cfg_block] def b_l100b6d_6 : Block Op Label signature Reg.count 278 :=
  .letOp (n := 278) (.out 0x100ce4 (xorR32R32Effect 0x100ce4 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[264, 276]
    (.letOp (n := 279) (.exec 0x100ce4 (fun s => s.RIP = 0x100ce4) (xorR32R32Effect 0x100ce4 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[264, 276]
    (.letOp (n := 280) (.out 0x100ce6 (andR32R32Effect 0x100ce6 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[278, 272]
    (.letOp (n := 281) (.exec 0x100ce6 (fun s => s.RIP = 0x100ce6) (andR32R32Effect 0x100ce6 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[278, 272]
    (.letOp (n := 282) (.out 0x100ce9 (xorR32R32Effect 0x100ce9 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[280, 266]
    (.letOp (n := 283) (.exec 0x100ce9 (fun s => s.RIP = 0x100ce9) (xorR32R32Effect 0x100ce9 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[280, 266]
    (.letOp (n := 284) (.out 0x100cec (movR32R32Effect 0x100cec 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[282]
    (.letOp (n := 285) (.exec 0x100cec (fun s => s.RIP = 0x100cec) (movR32R32Effect 0x100cec 3 9 0) (Reg.operands [.gpr 0] [])) #v[282]
    (.letOp (n := 286) (.out 0x100cef (xorR32R32Effect 0x100cef 3 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[284, 272]
    (.letOp (n := 287) (.exec 0x100cef (fun s => s.RIP = 0x100cef) (xorR32R32Effect 0x100cef 3 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[284, 272]
    (.letOp (n := 288) (.out 0x100cf2 (andR32R32Effect 0x100cf2 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[238, 286]
    (.letOp (n := 289) (.exec 0x100cf2 (fun s => s.RIP = 0x100cf2) (andR32R32Effect 0x100cf2 3 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[238, 286]
    (.letOp (n := 290) (.out 0x100cf5 (andR32M32Effect 0x100cf5 5 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[286, 4]
    (.letOp (n := 291) (.exec 0x100cf5 (LoadPre 0x100cf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100cf5 + BitVec.ofNat 64 5)) 4) (andR32M32Effect 0x100cf5 5 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[286, 4]
    (.letOp (n := 292) (.out 0x100cfa (xorR32R32Effect 0x100cfa 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[276, 240]
    (.letOp (n := 293) (.exec 0x100cfa (fun s => s.RIP = 0x100cfa) (xorR32R32Effect 0x100cfa 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[276, 240]
    (.letOp (n := 294) (.out 0x100cfd (movR32M32Effect 0x100cfd 11 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 295) (.exec 0x100cfd (LoadPre 0x100cfd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100cfd + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cfd 11 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 296) (.out 0x100d02 (andR32R32Effect 0x100d02 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[294, 292]
    (.letOp (n := 297) (.exec 0x100d02 (fun s => s.RIP = 0x100d02) (andR32R32Effect 0x100d02 3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[294, 292]
    (.letOp (n := 298) (.out 0x100d05 (movR32R32Effect 0x100d05 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[292]
    (.letOp (n := 299) (.exec 0x100d05 (fun s => s.RIP = 0x100d05) (movR32R32Effect 0x100d05 3 12 6) (Reg.operands [.gpr 6] [])) #v[292]
    (.letOp (n := 300) (.out 0x100d08 (andR32M32Effect 0x100d08 4 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[292, 4]
    (.letOp (n := 301) (.exec 0x100d08 (LoadPre 0x100d08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100d08 + BitVec.ofNat 64 4)) 4) (andR32M32Effect 0x100d08 4 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[292, 4]
    (.letOp (n := 302) (.out 0x100d0c (andR32R32Effect 0x100d0c 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[206, 282]
    (.letOp (n := 303) (.exec 0x100d0c (fun s => s.RIP = 0x100d0c) (andR32R32Effect 0x100d0c 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[206, 282]
    (.letOp (n := 304) (.out 0x100d0e (andR32R32Effect 0x100d0e 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[156, 282]
    (.letOp (n := 305) (.exec 0x100d0e (fun s => s.RIP = 0x100d0e) (andR32R32Effect 0x100d0e 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[156, 282]
    (.letOp (n := 306) (.out 0x100d10 (xorR32R32Effect 0x100d10 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[298, 274]
    (.letOp (n := 307) (.exec 0x100d10 (fun s => s.RIP = 0x100d10) (xorR32R32Effect 0x100d10 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[298, 274]
    (.letOp (n := 308) (.out 0x100d13 (xorR32R32Effect 0x100d13 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[282, 306]
    (.letOp (n := 309) (.exec 0x100d13 (fun s => s.RIP = 0x100d13) (xorR32R32Effect 0x100d13 3 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[282, 306]
    (.letOp (n := 310) (.out 0x100d16 (andR32R32Effect 0x100d16 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[224, 306]
    (.letOp (n := 311) (.exec 0x100d16 (fun s => s.RIP = 0x100d16) (andR32R32Effect 0x100d16 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[224, 306]
    (.letOp (n := 312) (.out 0x100d19 (andR32R32Effect 0x100d19 3 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[306, 220]
    (.letOp (n := 313) (.exec 0x100d19 (fun s => s.RIP = 0x100d19) (andR32R32Effect 0x100d19 3 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[306, 220]
    (.letOp (n := 314) (.exec 0x100d1c (StorePre 0x100d1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100d1c + BitVec.ofNat 64 5)) 4) (andMREffect 0x100d1c 5 32 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[272, 4]
    (.letOp (n := 315) (.exec 0x100d21 (StorePre 0x100d21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100d21 + BitVec.ofNat 64 5)) 4) (andMREffect 0x100d21 5 32 13 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[272, 4]
    (b_l100b6d_7))))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_6 : List UInt8 :=
  [0x31, 0xF0, 0x44, 0x21, 0xE8, 0x44, 0x31, 0xC8, 0x41, 0x89, 0xC1, 0x45, 0x31, 0xE9, 0x45, 0x21,
    0xCE, 0x44, 0x23, 0x4C, 0x24, 0x08, 0x44, 0x31, 0xDE, 0x44, 0x8B, 0x5C, 0x24, 0x1C, 0x41, 0x21,
    0xF3, 0x41, 0x89, 0xF4, 0x23, 0x74, 0x24, 0x20, 0x21, 0xC7, 0x21, 0xC5, 0x41, 0x31, 0xCC, 0x44,
    0x31, 0xE0, 0x44, 0x21, 0xE2, 0x45, 0x21, 0xD4, 0x44, 0x21, 0x6C, 0x24, 0x10, 0x44, 0x21, 0x6C,
    0x24, 0x0C] ++ bytes_l100b6d_7

theorem code_l100b6d_6 : ∀ x ∈ codeRange 0x100ce4 bytes_l100b6d_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xce4 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_7

@[cfg_block] def b_l100b6d_5 : Block Op Label signature Reg.count 238 :=
  .letOp (n := 238) (.out 0x100ca9 (movR32M32Effect 0x100ca9 14 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 239) (.exec 0x100ca9 (LoadPre 0x100ca9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100ca9 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100ca9 14 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 240) (.out 0x100cae (xorR32R32Effect 0x100cae 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[236, 238]
    (.letOp (n := 241) (.exec 0x100cae (fun s => s.RIP = 0x100cae) (xorR32R32Effect 0x100cae 3 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[236, 238]
    (.letOp (n := 242) (.out 0x100cb1 (movR32R32Effect 0x100cb1 3 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 11] []) (.reg (.gpr 13))) #v[240]
    (.letOp (n := 243) (.exec 0x100cb1 (fun s => s.RIP = 0x100cb1) (movR32R32Effect 0x100cb1 3 13 11) (Reg.operands [.gpr 11] [])) #v[240]
    (.letOp (n := 244) (.out 0x100cb4 (andR32R32Effect 0x100cb4 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[242, 234]
    (.letOp (n := 245) (.exec 0x100cb4 (fun s => s.RIP = 0x100cb4) (andR32R32Effect 0x100cb4 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[242, 234]
    (.letOp (n := 246) (.out 0x100cb7 (movR32R32Effect 0x100cb7 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[244]
    (.letOp (n := 247) (.exec 0x100cb7 (fun s => s.RIP = 0x100cb7) (movR32R32Effect 0x100cb7 3 1 13) (Reg.operands [.gpr 13] [])) #v[244]
    (.letOp (n := 248) (.out 0x100cba (xorR32R32Effect 0x100cba 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[246, 198]
    (.letOp (n := 249) (.exec 0x100cba (fun s => s.RIP = 0x100cba) (xorR32R32Effect 0x100cba 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[246, 198]
    (.letOp (n := 250) (.out 0x100cbd (xorR32R32Effect 0x100cbd 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[232, 202]
    (.letOp (n := 251) (.exec 0x100cbd (fun s => s.RIP = 0x100cbd) (xorR32R32Effect 0x100cbd 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[232, 202]
    (.letOp (n := 252) (.out 0x100cbf (andR32R32Effect 0x100cbf 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[250, 248]
    (.letOp (n := 253) (.exec 0x100cbf (fun s => s.RIP = 0x100cbf) (andR32R32Effect 0x100cbf 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[250, 248]
    (.letOp (n := 254) (.out 0x100cc1 (movR32R32Effect 0x100cc1 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[202]
    (.letOp (n := 255) (.exec 0x100cc1 (fun s => s.RIP = 0x100cc1) (movR32R32Effect 0x100cc1 3 15 0) (Reg.operands [.gpr 0] [])) #v[202]
    (.letOp (n := 256) (.out 0x100cc4 (xorR32R32Effect 0x100cc4 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[254, 238]
    (.letOp (n := 257) (.exec 0x100cc4 (fun s => s.RIP = 0x100cc4) (xorR32R32Effect 0x100cc4 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[254, 238]
    (.letOp (n := 258) (.out 0x100cc7 (movR32R32Effect 0x100cc7 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[252]
    (.letOp (n := 259) (.exec 0x100cc7 (fun s => s.RIP = 0x100cc7) (movR32R32Effect 0x100cc7 2 1 6) (Reg.operands [.gpr 6] [])) #v[252]
    (.letOp (n := 260) (.out 0x100cc9 (xorR32R32Effect 0x100cc9 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[252, 244]
    (.letOp (n := 261) (.exec 0x100cc9 (fun s => s.RIP = 0x100cc9) (xorR32R32Effect 0x100cc9 3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[252, 244]
    (.letOp (n := 262) (.out 0x100ccc (movR32R32Effect 0x100ccc 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[244]
    (.letOp (n := 263) (.exec 0x100ccc (fun s => s.RIP = 0x100ccc) (movR32R32Effect 0x100ccc 3 0 13) (Reg.operands [.gpr 13] [])) #v[244]
    (.letOp (n := 264) (.out 0x100ccf (xorR32R32Effect 0x100ccf 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[262, 256]
    (.letOp (n := 265) (.exec 0x100ccf (fun s => s.RIP = 0x100ccf) (xorR32R32Effect 0x100ccf 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[262, 256]
    (.letOp (n := 266) (.out 0x100cd2 (xorR32R32Effect 0x100cd2 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[234, 198]
    (.letOp (n := 267) (.exec 0x100cd2 (fun s => s.RIP = 0x100cd2) (xorR32R32Effect 0x100cd2 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[234, 198]
    (.letOp (n := 268) (.out 0x100cd5 (movR32R32Effect 0x100cd5 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[264]
    (.letOp (n := 269) (.exec 0x100cd5 (fun s => s.RIP = 0x100cd5) (movR32R32Effect 0x100cd5 3 13 0) (Reg.operands [.gpr 0] [])) #v[264]
    (.letOp (n := 270) (.out 0x100cd8 (andR32R32Effect 0x100cd8 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[268, 266]
    (.letOp (n := 271) (.exec 0x100cd8 (fun s => s.RIP = 0x100cd8) (andR32R32Effect 0x100cd8 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[268, 266]
    (.letOp (n := 272) (.out 0x100cdb (xorR32R32Effect 0x100cdb 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[270, 198]
    (.letOp (n := 273) (.exec 0x100cdb (fun s => s.RIP = 0x100cdb) (xorR32R32Effect 0x100cdb 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[270, 198]
    (.letOp (n := 274) (.out 0x100cde (xorR32R32Effect 0x100cde 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[258, 256]
    (.letOp (n := 275) (.exec 0x100cde (fun s => s.RIP = 0x100cde) (xorR32R32Effect 0x100cde 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[258, 256]
    (.letOp (n := 276) (.out 0x100ce1 (andR32R32Effect 0x100ce1 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[260, 256]
    (.letOp (n := 277) (.exec 0x100ce1 (fun s => s.RIP = 0x100ce1) (andR32R32Effect 0x100ce1 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[260, 256]
    (b_l100b6d_6))))))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_5 : List UInt8 :=
  [0x44, 0x8B, 0x74, 0x24, 0x14, 0x45, 0x31, 0xF3, 0x45, 0x89, 0xDD, 0x45, 0x21, 0xCD, 0x44, 0x89,
    0xE9, 0x44, 0x31, 0xE1, 0x31, 0xC6, 0x21, 0xCE, 0x41, 0x89, 0xC7, 0x45, 0x31, 0xF7, 0x89, 0xF1,
    0x44, 0x31, 0xEE, 0x44, 0x89, 0xE8, 0x44, 0x31, 0xF8, 0x45, 0x31, 0xE1, 0x41, 0x89, 0xC5, 0x45,
    0x21, 0xCD, 0x45, 0x31, 0xE5, 0x44, 0x31, 0xF9, 0x44, 0x21, 0xFE] ++ bytes_l100b6d_6

theorem code_l100b6d_5 : ∀ x ∈ codeRange 0x100ca9 bytes_l100b6d_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xca9 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_6

@[cfg_block] def b_l100b6d_4 : Block Op Label signature Reg.count 198 :=
  .letOp (n := 198) (.out 0x100c72 (xorR32R32Effect 0x100c72 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[196, 142]
    (.letOp (n := 199) (.exec 0x100c72 (fun s => s.RIP = 0x100c72) (xorR32R32Effect 0x100c72 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[196, 142]
    (.letOp (n := 200) (.out 0x100c75 (xorR32R32Effect 0x100c75 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[142, 178]
    (.letOp (n := 201) (.exec 0x100c75 (fun s => s.RIP = 0x100c75) (xorR32R32Effect 0x100c75 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[142, 178]
    (.letOp (n := 202) (.out 0x100c78 (xorR32R32Effect 0x100c78 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[200, 165]
    (.letOp (n := 203) (.exec 0x100c78 (fun s => s.RIP = 0x100c78) (xorR32R32Effect 0x100c78 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[200, 165]
    (.letOp (n := 204) (.out 0x100c7a (movR32M32LowEffect 0x100c7a 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 205) (.exec 0x100c7a (LoadPre 0x100c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100c7a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c7a 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 206) (.out 0x100c7e (xorR32R32Effect 0x100c7e 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[204, 156]
    (.letOp (n := 207) (.exec 0x100c7e (fun s => s.RIP = 0x100c7e) (xorR32R32Effect 0x100c7e 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[204, 156]
    (.letOp (n := 208) (.out 0x100c80 (movR32R32Effect 0x100c80 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[206]
    (.letOp (n := 209) (.exec 0x100c80 (fun s => s.RIP = 0x100c80) (movR32R32Effect 0x100c80 2 6 7) (Reg.operands [.gpr 7] [])) #v[206]
    (.letOp (n := 210) (.out 0x100c82 (andR32R32Effect 0x100c82 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[208, 156]
    (.letOp (n := 211) (.exec 0x100c82 (fun s => s.RIP = 0x100c82) (andR32R32Effect 0x100c82 2 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[208, 156]
    (.letOp (n := 212) (.out 0x100c84 (xorR32R32Effect 0x100c84 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[210, 176]
    (.letOp (n := 213) (.exec 0x100c84 (fun s => s.RIP = 0x100c84) (xorR32R32Effect 0x100c84 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[210, 176]
    (.letOp (n := 214) (.out 0x100c87 (xorR32R32Effect 0x100c87 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[212, 178]
    (.letOp (n := 215) (.exec 0x100c87 (fun s => s.RIP = 0x100c87) (xorR32R32Effect 0x100c87 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[212, 178]
    (.letOp (n := 216) (.out 0x100c8a (xorR32R32Effect 0x100c8a 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[100, 172]
    (.letOp (n := 217) (.exec 0x100c8a (fun s => s.RIP = 0x100c8a) (xorR32R32Effect 0x100c8a 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[100, 172]
    (.letOp (n := 218) (.out 0x100c8d (movR32R32Effect 0x100c8d 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[167]
    (.letOp (n := 219) (.exec 0x100c8d (fun s => s.RIP = 0x100c8d) (movR32R32Effect 0x100c8d 3 10 14) (Reg.operands [.gpr 14] [])) #v[167]
    (.letOp (n := 220) (.out 0x100c90 (xorR32R32Effect 0x100c90 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[218, 185]
    (.letOp (n := 221) (.exec 0x100c90 (fun s => s.RIP = 0x100c90) (xorR32R32Effect 0x100c90 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[218, 185]
    (.letOp (n := 222) (.out 0x100c93 (movR32R32Effect 0x100c93 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[206]
    (.letOp (n := 223) (.exec 0x100c93 (fun s => s.RIP = 0x100c93) (movR32R32Effect 0x100c93 2 2 7) (Reg.operands [.gpr 7] [])) #v[206]
    (.letOp (n := 224) (.out 0x100c95 (xorR32R32Effect 0x100c95 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[222, 190]
    (.letOp (n := 225) (.exec 0x100c95 (fun s => s.RIP = 0x100c95) (xorR32R32Effect 0x100c95 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[222, 190]
    (.letOp (n := 226) (.out 0x100c98 (movR32R32Effect 0x100c98 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[220]
    (.letOp (n := 227) (.exec 0x100c98 (fun s => s.RIP = 0x100c98) (movR32R32Effect 0x100c98 3 11 10) (Reg.operands [.gpr 10] [])) #v[220]
    (.letOp (n := 228) (.out 0x100c9b (andR32R32Effect 0x100c9b 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[226, 224]
    (.letOp (n := 229) (.exec 0x100c9b (fun s => s.RIP = 0x100c9b) (andR32R32Effect 0x100c9b 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[226, 224]
    (.letOp (n := 230) (.out 0x100c9e (xorR32R32Effect 0x100c9e 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[216, 228]
    (.letOp (n := 231) (.exec 0x100c9e (fun s => s.RIP = 0x100c9e) (xorR32R32Effect 0x100c9e 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[216, 228]
    (.letOp (n := 232) (.out 0x100ca1 (xorR32R32Effect 0x100ca1 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[214, 136]
    (.letOp (n := 233) (.exec 0x100ca1 (fun s => s.RIP = 0x100ca1) (xorR32R32Effect 0x100ca1 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[214, 136]
    (.letOp (n := 234) (.out 0x100ca3 (xorR32R32Effect 0x100ca3 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[230, 136]
    (.letOp (n := 235) (.exec 0x100ca3 (fun s => s.RIP = 0x100ca3) (xorR32R32Effect 0x100ca3 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[230, 136]
    (.letOp (n := 236) (.out 0x100ca6 (movR32R32Effect 0x100ca6 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[232]
    (.letOp (n := 237) (.exec 0x100ca6 (fun s => s.RIP = 0x100ca6) (movR32R32Effect 0x100ca6 3 11 6) (Reg.operands [.gpr 6] [])) #v[232]
    (b_l100b6d_5))))))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_4 : List UInt8 :=
  [0x41, 0x31, 0xC4, 0x44, 0x31, 0xD0, 0x31, 0xF0, 0x8B, 0x7C, 0x24, 0x18, 0x31, 0xEF, 0x89, 0xFE,
    0x21, 0xEE, 0x44, 0x31, 0xFE, 0x44, 0x31, 0xD6, 0x41, 0x31, 0xD1, 0x45, 0x89, 0xF2, 0x45, 0x31,
    0xDA, 0x89, 0xFA, 0x44, 0x31, 0xEA, 0x45, 0x89, 0xD3, 0x41, 0x21, 0xD3, 0x45, 0x31, 0xD9, 0x31,
    0xCE, 0x41, 0x31, 0xC9, 0x41, 0x89, 0xF3] ++ bytes_l100b6d_5

theorem code_l100b6d_4 : ∀ x ∈ codeRange 0x100c72 bytes_l100b6d_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc72 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_5

@[cfg_block] def b_l100b6d_3 : Block Op Label signature Reg.count 162 :=
  .letOp (n := 162) (.exec 0x100c2a (StorePre 0x100c2a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100c2a + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c2a 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 163) (.out 0x100c2f (andR32R32Effect 0x100c2f 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[148, 160]
    (.letOp (n := 164) (.exec 0x100c2f (fun s => s.RIP = 0x100c2f) (andR32R32Effect 0x100c2f 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[148, 160]
    (.letOp (n := 165) (.out 0x100c32 (xorR32R32Effect 0x100c32 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[163, 68]
    (.letOp (n := 166) (.exec 0x100c32 (fun s => s.RIP = 0x100c32) (xorR32R32Effect 0x100c32 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[163, 68]
    (.letOp (n := 167) (.out 0x100c34 (movR32R32Effect 0x100c34 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[125]
    (.letOp (n := 168) (.exec 0x100c34 (fun s => s.RIP = 0x100c34) (movR32R32Effect 0x100c34 3 14 11) (Reg.operands [.gpr 11] [])) #v[125]
    (.letOp (n := 169) (.exec 0x100c37 (StorePre 0x100c37 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100c37 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c37 11 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[125, 4]
    (.letOp (n := 170) (.out 0x100c3c (movR32R32Effect 0x100c3c 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[125]
    (.letOp (n := 171) (.exec 0x100c3c (fun s => s.RIP = 0x100c3c) (movR32R32Effect 0x100c3c 3 2 11) (Reg.operands [.gpr 11] [])) #v[125]
    (.letOp (n := 172) (.out 0x100c3f (andR32R32Effect 0x100c3f 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[170, 89]
    (.letOp (n := 173) (.exec 0x100c3f (fun s => s.RIP = 0x100c3f) (andR32R32Effect 0x100c3f 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[170, 89]
    (.letOp (n := 174) (.out 0x100c42 (movR32R32Effect 0x100c42 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[153]
    (.letOp (n := 175) (.exec 0x100c42 (fun s => s.RIP = 0x100c42) (movR32R32Effect 0x100c42 3 10 7) (Reg.operands [.gpr 7] [])) #v[153]
    (.letOp (n := 176) (.out 0x100c45 (movR32M32Effect 0x100c45 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 177) (.exec 0x100c45 (LoadPre 0x100c45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100c45 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100c45 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 178) (.out 0x100c4a (andR32R32Effect 0x100c4a 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[174, 176]
    (.letOp (n := 179) (.exec 0x100c4a (fun s => s.RIP = 0x100c4a) (andR32R32Effect 0x100c4a 3 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[174, 176]
    (.letOp (n := 180) (.out 0x100c4d (movR32M32Effect 0x100c4d 12 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 181) (.exec 0x100c4d (LoadPre 0x100c4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100c4d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100c4d 12 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 182) (.out 0x100c52 (xorR32R32Effect 0x100c52 3 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[180, 156]
    (.letOp (n := 183) (.exec 0x100c52 (fun s => s.RIP = 0x100c52) (xorR32R32Effect 0x100c52 3 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[180, 156]
    (.letOp (n := 184) (.exec 0x100c55 (StorePre 0x100c55 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100c55 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c55 12 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[182, 4]
    (.letOp (n := 185) (.out 0x100c5a (movR32R32Effect 0x100c5a 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 13] []) (.reg (.gpr 11))) #v[144]
    (.letOp (n := 186) (.exec 0x100c5a (fun s => s.RIP = 0x100c5a) (movR32R32Effect 0x100c5a 3 11 13) (Reg.operands [.gpr 13] [])) #v[144]
    (.letOp (n := 187) (.exec 0x100c5d (StorePre 0x100c5d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100c5d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c5d 13 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[144, 4]
    (.letOp (n := 188) (.out 0x100c62 (andR32R32Effect 0x100c62 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[182, 144]
    (.letOp (n := 189) (.exec 0x100c62 (fun s => s.RIP = 0x100c62) (andR32R32Effect 0x100c62 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[182, 144]
    (.letOp (n := 190) (.out 0x100c65 (movR32M32Effect 0x100c65 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 191) (.exec 0x100c65 (LoadPre 0x100c65 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100c65 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c65 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 192) (.out 0x100c69 (xorR32R32Effect 0x100c69 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[188, 190]
    (.letOp (n := 193) (.exec 0x100c69 (fun s => s.RIP = 0x100c69) (xorR32R32Effect 0x100c69 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[188, 190]
    (.letOp (n := 194) (.out 0x100c6c (xorR32R32Effect 0x100c6c 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[192, 172]
    (.letOp (n := 195) (.exec 0x100c6c (fun s => s.RIP = 0x100c6c) (xorR32R32Effect 0x100c6c 3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[192, 172]
    (.letOp (n := 196) (.out 0x100c6f (xorR32R32Effect 0x100c6f 3 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[194, 127]
    (.letOp (n := 197) (.exec 0x100c6f (fun s => s.RIP = 0x100c6f) (xorR32R32Effect 0x100c6f 3 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[194, 127]
    (b_l100b6d_4))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_3 : List UInt8 :=
  [0x44, 0x89, 0x54, 0x24, 0x10, 0x44, 0x21, 0xD6, 0x31, 0xD6, 0x45, 0x89, 0xDE, 0x44, 0x89, 0x5C,
    0x24, 0x1C, 0x44, 0x89, 0xDA, 0x44, 0x21, 0xE2, 0x41, 0x89, 0xFA, 0x44, 0x8B, 0x7C, 0x24, 0x08,
    0x45, 0x21, 0xFA, 0x44, 0x8B, 0x64, 0x24, 0x04, 0x41, 0x31, 0xEC, 0x44, 0x89, 0x64, 0x24, 0x04,
    0x45, 0x89, 0xEB, 0x44, 0x89, 0x6C, 0x24, 0x24, 0x45, 0x21, 0xEC, 0x44, 0x8B, 0x2C, 0x24, 0x45,
    0x31, 0xEC, 0x41, 0x31, 0xD4, 0x45, 0x31, 0xC4] ++ bytes_l100b6d_4

theorem code_l100b6d_3 : ∀ x ∈ codeRange 0x100c2a bytes_l100b6d_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc2a 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_4

@[cfg_block] def b_l100b6d_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.out 0x100bee (movR32R32Effect 0x100bee 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 13] []) (.reg (.gpr 11))) #v[96]
    (.letOp (n := 126) (.exec 0x100bee (fun s => s.RIP = 0x100bee) (movR32R32Effect 0x100bee 3 11 13) (Reg.operands [.gpr 13] [])) #v[96]
    (.letOp (n := 127) (.out 0x100bf1 (xorR32R32Effect 0x100bf1 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[123, 121]
    (.letOp (n := 128) (.exec 0x100bf1 (fun s => s.RIP = 0x100bf1) (xorR32R32Effect 0x100bf1 3 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[123, 121]
    (.letOp (n := 129) (.out 0x100bf4 (movR32R32Effect 0x100bf4 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[113]
    (.letOp (n := 130) (.exec 0x100bf4 (fun s => s.RIP = 0x100bf4) (movR32R32Effect 0x100bf4 3 1 14) (Reg.operands [.gpr 14] [])) #v[113]
    (.letOp (n := 131) (.out 0x100bf7 (xorR32R32Effect 0x100bf7 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[129, 127]
    (.letOp (n := 132) (.exec 0x100bf7 (fun s => s.RIP = 0x100bf7) (xorR32R32Effect 0x100bf7 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[129, 127]
    (.letOp (n := 133) (.exec 0x100bfa (StorePre 0x100bfa 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100bfa + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bfa 1 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[131, 4]
    (.letOp (n := 134) (.out 0x100bfe (andR32R32Effect 0x100bfe 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[131, 84]
    (.letOp (n := 135) (.exec 0x100bfe (fun s => s.RIP = 0x100bfe) (andR32R32Effect 0x100bfe 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[131, 84]
    (.letOp (n := 136) (.out 0x100c01 (xorR32R32Effect 0x100c01 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[134, 116]
    (.letOp (n := 137) (.exec 0x100c01 (fun s => s.RIP = 0x100c01) (xorR32R32Effect 0x100c01 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[134, 116]
    (.letOp (n := 138) (.out 0x100c03 (movR32R32Effect 0x100c03 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[127]
    (.letOp (n := 139) (.exec 0x100c03 (fun s => s.RIP = 0x100c03) (movR32R32Effect 0x100c03 3 0 8) (Reg.operands [.gpr 8] [])) #v[127]
    (.letOp (n := 140) (.out 0x100c06 (andR32R32Effect 0x100c06 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[138, 118]
    (.letOp (n := 141) (.exec 0x100c06 (fun s => s.RIP = 0x100c06) (andR32R32Effect 0x100c06 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[138, 118]
    (.letOp (n := 142) (.out 0x100c08 (xorR32R32Effect 0x100c08 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[140, 116]
    (.letOp (n := 143) (.exec 0x100c08 (fun s => s.RIP = 0x100c08) (xorR32R32Effect 0x100c08 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[140, 116]
    (.letOp (n := 144) (.out 0x100c0a (movzxR32M16Effect 0x100c0a 4 13 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 145) (.exec 0x100c0a (LoadPre 0x100c0a (fun s => AddrMode.addr (.base 3 .none) s (0x100c0a + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100c0a 4 13 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 146) (.out 0x100c0e (movR32R32Effect 0x100c0e 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[113]
    (.letOp (n := 147) (.exec 0x100c0e (fun s => s.RIP = 0x100c0e) (movR32R32Effect 0x100c0e 3 6 14) (Reg.operands [.gpr 14] [])) #v[113]
    (.letOp (n := 148) (.out 0x100c11 (xorR32R32Effect 0x100c11 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[146, 144]
    (.letOp (n := 149) (.exec 0x100c11 (fun s => s.RIP = 0x100c11) (xorR32R32Effect 0x100c11 3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[146, 144]
    (.letOp (n := 150) (.exec 0x100c14 (StorePre 0x100c14 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100c14 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c14 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[148, 4]
    (.letOp (n := 151) (.out 0x100c18 (movR32R32Effect 0x100c18 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[113]
    (.letOp (n := 152) (.exec 0x100c18 (fun s => s.RIP = 0x100c18) (movR32R32Effect 0x100c18 3 7 14) (Reg.operands [.gpr 14] [])) #v[113]
    (.letOp (n := 153) (.out 0x100c1b (xorR32R32Effect 0x100c1b 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[151, 121]
    (.letOp (n := 154) (.exec 0x100c1b (fun s => s.RIP = 0x100c1b) (xorR32R32Effect 0x100c1b 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[151, 121]
    (.letOp (n := 155) (.exec 0x100c1d (StorePre 0x100c1d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100c1d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c1d 7 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[153, 4]
    (.letOp (n := 156) (.out 0x100c21 (xorR32R32Effect 0x100c21 3 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[121, 144]
    (.letOp (n := 157) (.exec 0x100c21 (fun s => s.RIP = 0x100c21) (xorR32R32Effect 0x100c21 3 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[121, 144]
    (.letOp (n := 158) (.out 0x100c24 (movR32R32Effect 0x100c24 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[156]
    (.letOp (n := 159) (.exec 0x100c24 (fun s => s.RIP = 0x100c24) (movR32R32Effect 0x100c24 3 10 5) (Reg.operands [.gpr 5] [])) #v[156]
    (.letOp (n := 160) (.out 0x100c27 (xorR32R32Effect 0x100c27 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[158, 68]
    (.letOp (n := 161) (.exec 0x100c27 (fun s => s.RIP = 0x100c27) (xorR32R32Effect 0x100c27 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[158, 68]
    (b_l100b6d_3)))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_2 : List UInt8 :=
  [0x45, 0x89, 0xEB, 0x41, 0x31, 0xE8, 0x44, 0x89, 0xF1, 0x44, 0x31, 0xC1, 0x89, 0x4C, 0x24, 0x2C,
    0x44, 0x21, 0xF9, 0x31, 0xF1, 0x44, 0x89, 0xC0, 0x21, 0xF8, 0x31, 0xF0, 0x44, 0x0F, 0xB7, 0x2B,
    0x44, 0x89, 0xF6, 0x44, 0x31, 0xEE, 0x89, 0x74, 0x24, 0x0C, 0x44, 0x89, 0xF7, 0x31, 0xEF, 0x89,
    0x7C, 0x24, 0x14, 0x44, 0x31, 0xED, 0x41, 0x89, 0xEA, 0x41, 0x31, 0xD2] ++ bytes_l100b6d_3

theorem code_l100b6d_2 : ∀ x ∈ codeRange 0x100bee bytes_l100b6d_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbee 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_3

@[cfg_block] def b_l100b6d_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x100bb4 (movR32R32Effect 0x100bb4 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[82]
    (.letOp (n := 90) (.exec 0x100bb4 (fun s => s.RIP = 0x100bb4) (movR32R32Effect 0x100bb4 3 12 6) (Reg.operands [.gpr 6] [])) #v[82]
    (.letOp (n := 91) (.exec 0x100bb7 (StorePre 0x100bb7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100bb7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bb7 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 92) (.out 0x100bbb (movR32R32Effect 0x100bbb 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[87]
    (.letOp (n := 93) (.exec 0x100bbb (fun s => s.RIP = 0x100bbb) (movR32R32Effect 0x100bbb 3 6 9) (Reg.operands [.gpr 9] [])) #v[87]
    (.letOp (n := 94) (.out 0x100bbe (xorR32R32Effect 0x100bbe 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[92, 58]
    (.letOp (n := 95) (.exec 0x100bbe (fun s => s.RIP = 0x100bbe) (xorR32R32Effect 0x100bbe 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[92, 58]
    (.letOp (n := 96) (.out 0x100bc0 (movR32R32Effect 0x100bc0 3 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[94]
    (.letOp (n := 97) (.exec 0x100bc0 (fun s => s.RIP = 0x100bc0) (movR32R32Effect 0x100bc0 3 13 6) (Reg.operands [.gpr 6] [])) #v[94]
    (.letOp (n := 98) (.out 0x100bc3 (movR32R32Effect 0x100bc3 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[58]
    (.letOp (n := 99) (.exec 0x100bc3 (fun s => s.RIP = 0x100bc3) (movR32R32Effect 0x100bc3 2 7 1) (Reg.operands [.gpr 1] [])) #v[58]
    (.letOp (n := 100) (.out 0x100bc5 (xorR32R32Effect 0x100bc5 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[87, 66]
    (.letOp (n := 101) (.exec 0x100bc5 (fun s => s.RIP = 0x100bc5) (xorR32R32Effect 0x100bc5 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[87, 66]
    (.letOp (n := 102) (.out 0x100bc8 (movR32R32Effect 0x100bc8 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 103) (.exec 0x100bc8 (fun s => s.RIP = 0x100bc8) (movR32R32Effect 0x100bc8 2 1 2) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 104) (.out 0x100bca (xorR32R32Effect 0x100bca 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[102, 72]
    (.letOp (n := 105) (.exec 0x100bca (fun s => s.RIP = 0x100bca) (xorR32R32Effect 0x100bca 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[102, 72]
    (.letOp (n := 106) (.exec 0x100bcd (StorePre 0x100bcd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100bcd + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bcd 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[104, 4]
    (.letOp (n := 107) (.out 0x100bd1 (movR32R32Effect 0x100bd1 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[100]
    (.letOp (n := 108) (.exec 0x100bd1 (fun s => s.RIP = 0x100bd1) (movR32R32Effect 0x100bd1 3 8 9) (Reg.operands [.gpr 9] [])) #v[100]
    (.letOp (n := 109) (.out 0x100bd4 (xorR32R32Effect 0x100bd4 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[107, 104]
    (.letOp (n := 110) (.exec 0x100bd4 (fun s => s.RIP = 0x100bd4) (xorR32R32Effect 0x100bd4 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[107, 104]
    (.letOp (n := 111) (.out 0x100bd7 (movR32R32Effect 0x100bd7 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[109]
    (.letOp (n := 112) (.exec 0x100bd7 (fun s => s.RIP = 0x100bd7) (movR32R32Effect 0x100bd7 3 6 8) (Reg.operands [.gpr 8] [])) #v[109]
    (.letOp (n := 113) (.out 0x100bda (movR32R32Effect 0x100bda 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[109]
    (.letOp (n := 114) (.exec 0x100bda (fun s => s.RIP = 0x100bda) (movR32R32Effect 0x100bda 3 14 8) (Reg.operands [.gpr 8] [])) #v[109]
    (.letOp (n := 115) (.exec 0x100bdd (StorePre 0x100bdd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100bdd + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100bdd 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[109, 4]
    (.letOp (n := 116) (.out 0x100be2 (andR32R32Effect 0x100be2 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[111, 104]
    (.letOp (n := 117) (.exec 0x100be2 (fun s => s.RIP = 0x100be2) (andR32R32Effect 0x100be2 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[111, 104]
    (.letOp (n := 118) (.out 0x100be4 (xorR32R32Effect 0x100be4 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[98, 68]
    (.letOp (n := 119) (.exec 0x100be4 (fun s => s.RIP = 0x100be4) (xorR32R32Effect 0x100be4 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[98, 68]
    (.letOp (n := 120) (.exec 0x100be6 (StorePre 0x100be6 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100be6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x100be6 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[118, 4]
    (.letOp (n := 121) (.out 0x100be9 (xorR32R32Effect 0x100be9 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[64, 66]
    (.letOp (n := 122) (.exec 0x100be9 (fun s => s.RIP = 0x100be9) (xorR32R32Effect 0x100be9 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[64, 66]
    (.letOp (n := 123) (.out 0x100beb (movR32R32Effect 0x100beb 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[96]
    (.letOp (n := 124) (.exec 0x100beb (fun s => s.RIP = 0x100beb) (movR32R32Effect 0x100beb 3 8 13) (Reg.operands [.gpr 13] [])) #v[96]
    (b_l100b6d_2))))))))))))))))))))))))))))))))))))

def bytes_l100b6d_1 : List UInt8 :=
  [0x41, 0x89, 0xF4, 0x89, 0x74, 0x24, 0x20, 0x44, 0x89, 0xCE, 0x31, 0xCE, 0x41, 0x89, 0xF5, 0x89,
    0xCF, 0x41, 0x31, 0xC1, 0x89, 0xD1, 0x44, 0x31, 0xD9, 0x89, 0x4C, 0x24, 0x34, 0x45, 0x89, 0xC8,
    0x41, 0x31, 0xC8, 0x44, 0x89, 0xC6, 0x45, 0x89, 0xC6, 0x44, 0x89, 0x44, 0x24, 0x28, 0x21, 0xCE,
    0x31, 0xD7, 0x89, 0x3C, 0x24, 0x31, 0xC5, 0x45, 0x89, 0xE8] ++ bytes_l100b6d_2

theorem code_l100b6d_1 : ∀ x ∈ codeRange 0x100bb4 bytes_l100b6d_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbb4 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_2

@[cfg_block] def b_l100b6d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b6d (movR64R64Effect 0x100b6d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 54) (.exec 0x100b6d (fun s => s.RIP = 0x100b6d) (movR64R64Effect 0x100b6d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x100b70 (movzxR32M16Effect 0x100b70 4 7 (.base 7 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x100b70 (LoadPre 0x100b70 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100b70 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b70 4 7 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x100b74 (StorePre 0x100b74 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100b74 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100b74 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x100b78 (movzxR32M16Effect 0x100b78 4 1 (.base 3 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 59) (.exec 0x100b78 (LoadPre 0x100b78 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x100b78 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b78 4 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 60) (.out 0x100b7c (movzxR32M16Effect 0x100b7c 5 9 (.base 3 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 61) (.exec 0x100b7c (LoadPre 0x100b7c (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x100b7c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100b7c 5 9 (.base 3 (.d8 0x6))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 62) (.out 0x100b81 (movzxR32M16Effect 0x100b81 4 6 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 63) (.exec 0x100b81 (LoadPre 0x100b81 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100b81 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b81 4 6 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 64) (.out 0x100b85 (movzxR32M16Effect 0x100b85 4 5 (.base 3 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 65) (.exec 0x100b85 (LoadPre 0x100b85 (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x100b85 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b85 4 5 (.base 3 (.d8 0xa))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 66) (.out 0x100b89 (movzxR32M16Effect 0x100b89 4 0 (.base 3 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 67) (.exec 0x100b89 (LoadPre 0x100b89 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x100b89 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b89 4 0 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 68) (.out 0x100b8d (movzxR32M16Effect 0x100b8d 4 2 (.base 3 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 69) (.exec 0x100b8d (LoadPre 0x100b8d (fun s => AddrMode.addr (.base 3 (.d8 0xe)) s (0x100b8d + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b8d 4 2 (.base 3 (.d8 0xe))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 70) (.out 0x100b91 (movR32R32Effect 0x100b91 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[62]
    (.letOp (n := 71) (.exec 0x100b91 (fun s => s.RIP = 0x100b91) (movR32R32Effect 0x100b91 3 8 6) (Reg.operands [.gpr 6] [])) #v[62]
    (.letOp (n := 72) (.out 0x100b94 (movR32R32Effect 0x100b94 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[62]
    (.letOp (n := 73) (.exec 0x100b94 (fun s => s.RIP = 0x100b94) (movR32R32Effect 0x100b94 3 11 6) (Reg.operands [.gpr 6] [])) #v[62]
    (.letOp (n := 74) (.exec 0x100b97 (StorePre 0x100b97 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100b97 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100b97 6 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 75) (.out 0x100b9b (xorR32R32Effect 0x100b9b 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[70, 58]
    (.letOp (n := 76) (.exec 0x100b9b (fun s => s.RIP = 0x100b9b) (xorR32R32Effect 0x100b9b 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[70, 58]
    (.letOp (n := 77) (.out 0x100b9e (movR32R32Effect 0x100b9e 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[68]
    (.letOp (n := 78) (.exec 0x100b9e (fun s => s.RIP = 0x100b9e) (movR32R32Effect 0x100b9e 2 6 2) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 79) (.out 0x100ba0 (xorR32R32Effect 0x100ba0 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[77, 55]
    (.letOp (n := 80) (.exec 0x100ba0 (fun s => s.RIP = 0x100ba0) (xorR32R32Effect 0x100ba0 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[77, 55]
    (.letOp (n := 81) (.exec 0x100ba2 (StorePre 0x100ba2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100ba2 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100ba2 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x100ba6 (xorR32R32Effect 0x100ba6 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[79, 75]
    (.letOp (n := 83) (.exec 0x100ba6 (fun s => s.RIP = 0x100ba6) (xorR32R32Effect 0x100ba6 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[79, 75]
    (.letOp (n := 84) (.out 0x100ba9 (movR32R32Effect 0x100ba9 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[75]
    (.letOp (n := 85) (.exec 0x100ba9 (fun s => s.RIP = 0x100ba9) (movR32R32Effect 0x100ba9 3 15 8) (Reg.operands [.gpr 8] [])) #v[75]
    (.letOp (n := 86) (.exec 0x100bac (StorePre 0x100bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100bac + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100bac 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 87) (.out 0x100bb1 (xorR32R32Effect 0x100bb1 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[60, 82]
    (.letOp (n := 88) (.exec 0x100bb1 (fun s => s.RIP = 0x100bb1) (xorR32R32Effect 0x100bb1 3 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[60, 82]
    (b_l100b6d_1))))))))))))))))))))))))))))))))))))

def bytes_l100b6d : List UInt8 :=
  [0x48, 0x89, 0xFB, 0x0F, 0xB7, 0x7F, 0x02, 0x89, 0x7C, 0x24, 0x18, 0x0F, 0xB7, 0x4B, 0x04, 0x44,
    0x0F, 0xB7, 0x4B, 0x06, 0x0F, 0xB7, 0x73, 0x08, 0x0F, 0xB7, 0x6B, 0x0A, 0x0F, 0xB7, 0x43, 0x0C,
    0x0F, 0xB7, 0x53, 0x0E, 0x41, 0x89, 0xF0, 0x41, 0x89, 0xF3, 0x89, 0x74, 0x24, 0x04, 0x41, 0x31,
    0xC8, 0x89, 0xD6, 0x31, 0xFE, 0x89, 0x74, 0x24, 0x08, 0x44, 0x31, 0xC6, 0x45, 0x89, 0xC7, 0x44,
    0x89, 0x44, 0x24, 0x30, 0x41, 0x31, 0xF1] ++ bytes_l100b6d_1

theorem code_l100b6d : ∀ x ∈ codeRange 0x100b6d bytes_l100b6d, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb6d 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100b6d_1

@[cfg_block] def b_l100de6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100de6 (xorR32R32Effect 0x100de6 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x100de6 (fun s => s.RIP = 0x100de6) (xorR32R32Effect 0x100de6 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x100de8 (xorR32R32Effect 0x100de8 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x100de8 (fun s => s.RIP = 0x100de8) (xorR32R32Effect 0x100de8 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.out 0x100dea (movR64Imm32Effect 0x100dea 2 0x200e60) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100dea (fun s => s.RIP = 0x100dea) (movR64Imm32Effect 0x100dea 2 0x200e60) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100df1 (callEffect (fun _ => 0x103837) 0x100df6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100df1 (PushPre 0x100df1 5) (callEffect (fun _ => 0x103837) 0x100df6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100df6⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100df6, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100de6 : List UInt8 :=
  [0x31, 0xFF, 0x31, 0xF6, 0x48, 0xC7, 0xC2, 0x60, 0x0E, 0x20, 0x00, 0xE8, 0x41, 0x2A, 0x00, 0x00]

theorem code_l100de6 : ∀ x ∈ codeRange 0x100de6 bytes_l100de6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xde6 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100df6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100df6 (movR32Imm32Effect 0x100df6 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100df6 (fun s => s.RIP = 0x100df6) (movR32Imm32Effect 0x100df6 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100dfb (movR32Imm32Effect 0x100dfb 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100dfb (fun s => s.RIP = 0x100dfb) (movR32Imm32Effect 0x100dfb 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e00 (movR64Imm32Effect 0x100e00 2 0x200e78) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e00 (fun s => s.RIP = 0x100e00) (movR64Imm32Effect 0x100e00 2 0x200e78) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e07 (callEffect (fun _ => 0x103837) 0x100e0c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e07 (PushPre 0x100e07 5) (callEffect (fun _ => 0x103837) 0x100e0c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e0c⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e0c, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100df6 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x78, 0x0E, 0x20,
    0x00, 0xE8, 0x2B, 0x2A, 0x00, 0x00]

theorem code_l100df6 : ∀ x ∈ codeRange 0x100df6 bytes_l100df6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdf6 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e0c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e0c (movR32Imm32Effect 0x100e0c 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100e0c (fun s => s.RIP = 0x100e0c) (movR32Imm32Effect 0x100e0c 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e11 (movR32Imm32Effect 0x100e11 5 6 0x2) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100e11 (fun s => s.RIP = 0x100e11) (movR32Imm32Effect 0x100e11 5 6 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e16 (movR64Imm32Effect 0x100e16 2 0x200e90) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e16 (fun s => s.RIP = 0x100e16) (movR64Imm32Effect 0x100e16 2 0x200e90) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e1d (callEffect (fun _ => 0x103837) 0x100e22) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e1d (PushPre 0x100e1d 5) (callEffect (fun _ => 0x103837) 0x100e22) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e22⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e22, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e0c : List UInt8 :=
  [0xBF, 0x02, 0x00, 0x00, 0x00, 0xBE, 0x02, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x90, 0x0E, 0x20,
    0x00, 0xE8, 0x15, 0x2A, 0x00, 0x00]

theorem code_l100e0c : ∀ x ∈ codeRange 0x100e0c bytes_l100e0c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe0c 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e22 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e22 (movR32Imm32Effect 0x100e22 5 7 0x3) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100e22 (fun s => s.RIP = 0x100e22) (movR32Imm32Effect 0x100e22 5 7 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e27 (movR32Imm32Effect 0x100e27 5 6 0x3) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100e27 (fun s => s.RIP = 0x100e27) (movR32Imm32Effect 0x100e27 5 6 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e2c (movR64Imm32Effect 0x100e2c 2 0x200ea8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e2c (fun s => s.RIP = 0x100e2c) (movR64Imm32Effect 0x100e2c 2 0x200ea8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e33 (callEffect (fun _ => 0x103837) 0x100e38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e33 (PushPre 0x100e33 5) (callEffect (fun _ => 0x103837) 0x100e38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e38⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e38, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e22 : List UInt8 :=
  [0xBF, 0x03, 0x00, 0x00, 0x00, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xA8, 0x0E, 0x20,
    0x00, 0xE8, 0xFF, 0x29, 0x00, 0x00]

theorem code_l100e22 : ∀ x ∈ codeRange 0x100e22 bytes_l100e22, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe22 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e38 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e38 (movR32Imm32Effect 0x100e38 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100e38 (fun s => s.RIP = 0x100e38) (movR32Imm32Effect 0x100e38 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e3d (movR32Imm32Effect 0x100e3d 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100e3d (fun s => s.RIP = 0x100e3d) (movR32Imm32Effect 0x100e3d 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e42 (movR64Imm32Effect 0x100e42 2 0x200ec0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e42 (fun s => s.RIP = 0x100e42) (movR64Imm32Effect 0x100e42 2 0x200ec0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e49 (callEffect (fun _ => 0x103837) 0x100e4e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e49 (PushPre 0x100e49 5) (callEffect (fun _ => 0x103837) 0x100e4e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e4e⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e4e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e38 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xC0, 0x0E, 0x20,
    0x00, 0xE8, 0xE9, 0x29, 0x00, 0x00]

theorem code_l100e38 : ∀ x ∈ codeRange 0x100e38 bytes_l100e38, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe38 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e4e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e4e (movR32Imm32Effect 0x100e4e 5 7 0x5) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100e4e (fun s => s.RIP = 0x100e4e) (movR32Imm32Effect 0x100e4e 5 7 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e53 (movR32Imm32Effect 0x100e53 5 6 0x5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100e53 (fun s => s.RIP = 0x100e53) (movR32Imm32Effect 0x100e53 5 6 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e58 (movR64Imm32Effect 0x100e58 2 0x200ed8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e58 (fun s => s.RIP = 0x100e58) (movR64Imm32Effect 0x100e58 2 0x200ed8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e5f (callEffect (fun _ => 0x103837) 0x100e64) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e5f (PushPre 0x100e5f 5) (callEffect (fun _ => 0x103837) 0x100e64) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e64⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e64, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e4e : List UInt8 :=
  [0xBF, 0x05, 0x00, 0x00, 0x00, 0xBE, 0x05, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xD8, 0x0E, 0x20,
    0x00, 0xE8, 0xD3, 0x29, 0x00, 0x00]

theorem code_l100e4e : ∀ x ∈ codeRange 0x100e4e bytes_l100e4e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe4e 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e64 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e64 (movR32Imm32Effect 0x100e64 5 7 0x6) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100e64 (fun s => s.RIP = 0x100e64) (movR32Imm32Effect 0x100e64 5 7 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e69 (movR32Imm32Effect 0x100e69 5 6 0x6) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100e69 (fun s => s.RIP = 0x100e69) (movR32Imm32Effect 0x100e69 5 6 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e6e (movR64Imm32Effect 0x100e6e 2 0x200ef0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e6e (fun s => s.RIP = 0x100e6e) (movR64Imm32Effect 0x100e6e 2 0x200ef0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e75 (callEffect (fun _ => 0x103837) 0x100e7a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e75 (PushPre 0x100e75 5) (callEffect (fun _ => 0x103837) 0x100e7a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e7a⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e7a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e64 : List UInt8 :=
  [0xBF, 0x06, 0x00, 0x00, 0x00, 0xBE, 0x06, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xF0, 0x0E, 0x20,
    0x00, 0xE8, 0xBD, 0x29, 0x00, 0x00]

theorem code_l100e64 : ∀ x ∈ codeRange 0x100e64 bytes_l100e64, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe64 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e7a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e7a (movR32Imm32Effect 0x100e7a 5 7 0x7) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x100e7a (fun s => s.RIP = 0x100e7a) (movR32Imm32Effect 0x100e7a 5 7 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e7f (movR32Imm32Effect 0x100e7f 5 6 0x7) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x100e7f (fun s => s.RIP = 0x100e7f) (movR32Imm32Effect 0x100e7f 5 6 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e84 (movR64Imm32Effect 0x100e84 2 0x200f08) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e84 (fun s => s.RIP = 0x100e84) (movR64Imm32Effect 0x100e84 2 0x200f08) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e8b (callEffect (fun _ => 0x103837) 0x100e90) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e8b (PushPre 0x100e8b 5) (callEffect (fun _ => 0x103837) 0x100e90) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e90⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l100e90, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e7a : List UInt8 :=
  [0xBF, 0x07, 0x00, 0x00, 0x00, 0xBE, 0x07, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x08, 0x0F, 0x20,
    0x00, 0xE8, 0xA7, 0x29, 0x00, 0x00]

theorem code_l100e7a : ∀ x ∈ codeRange 0x100e7a bytes_l100e7a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe7a 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e90 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e90 (pushR64Effect 0x100e90 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100e90 (PushPre 0x100e90 1) (pushR64Effect 0x100e90 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100e91 (pushR64Effect 0x100e91 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100e91 (PushPre 0x100e91 2) (pushR64Effect 0x100e91 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100e93 (pushR64Effect 0x100e93 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100e93 (PushPre 0x100e93 2) (pushR64Effect 0x100e93 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100e95 (pushR64Effect 0x100e95 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100e95 (PushPre 0x100e95 2) (pushR64Effect 0x100e95 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100e97 (pushR64Effect 0x100e97 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100e97 (PushPre 0x100e97 2) (pushR64Effect 0x100e97 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100e99 (pushR64Effect 0x100e99 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100e99 (PushPre 0x100e99 1) (pushR64Effect 0x100e99 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x100e9a (subR64Imm8Effect 0x100e9a 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x100e9a (fun s => s.RIP = 0x100e9a) (subR64Imm8Effect 0x100e9a 4 0x68) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100e9e (testR64R64Effect 0x100e9e 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 68) (.exec 0x100e9e (fun s => s.RIP = 0x100e9e) (testR64R64Effect 0x100e9e 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.pure (condOp 4)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l101177, RegMap.args [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l100ea7, RegMap.args [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l100e90 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x68, 0x48, 0x85,
    0xF6, 0x0F, 0x84, 0xD0, 0x02, 0x00, 0x00]

theorem code_l100e90 : ∀ x ∈ codeRange 0x100e90 bytes_l100e90, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe90 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ea7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ea7 (cmpR64Imm8Effect 0x100ea7 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100ea7 (fun s => s.RIP = 0x100ea7) (cmpR64Imm8Effect 0x100ea7 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101187, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100eb1, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100ea7 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x01, 0x0F, 0x84, 0xD6, 0x02, 0x00, 0x00]

theorem code_l100ea7 : ∀ x ∈ codeRange 0x100ea7 bytes_l100ea7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xea7 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100eb1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100eb1 (cmpR64Imm8Effect 0x100eb1 6 0x2) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 54) (.out 0x100eb1 (cmpR64Imm8Effect 0x100eb1 6 0x2) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 55) (.exec 0x100eb1 (fun s => s.RIP = 0x100eb1) (cmpR64Imm8Effect 0x100eb1 6 0x2) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10119d, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100ebb, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100eb1 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x02, 0x0F, 0x86, 0xE2, 0x02, 0x00, 0x00]

theorem code_l100eb1 : ∀ x ∈ codeRange 0x100eb1 bytes_l100eb1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xeb1 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ebb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ebb (cmpR64Imm8Effect 0x100ebb 6 0x3) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100ebb (fun s => s.RIP = 0x100ebb) (cmpR64Imm8Effect 0x100ebb 6 0x3) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1011b3, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100ec5, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100ebb : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x03, 0x0F, 0x84, 0xEE, 0x02, 0x00, 0x00]

theorem code_l100ebb : ∀ x ∈ codeRange 0x100ebb bytes_l100ebb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xebb 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ec5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ec5 (cmpR64Imm8Effect 0x100ec5 6 0x4) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 54) (.out 0x100ec5 (cmpR64Imm8Effect 0x100ec5 6 0x4) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 55) (.exec 0x100ec5 (fun s => s.RIP = 0x100ec5) (cmpR64Imm8Effect 0x100ec5 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l1011c9, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100ecf, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100ec5 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x04, 0x0F, 0x86, 0xFA, 0x02, 0x00, 0x00]

theorem code_l100ec5 : ∀ x ∈ codeRange 0x100ec5 bytes_l100ec5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xec5 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ecf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ecf (cmpR64Imm8Effect 0x100ecf 6 0x5) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100ecf (fun s => s.RIP = 0x100ecf) (cmpR64Imm8Effect 0x100ecf 6 0x5) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1011df, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100ed9, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100ecf : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x05, 0x0F, 0x84, 0x06, 0x03, 0x00, 0x00]

theorem code_l100ecf : ∀ x ∈ codeRange 0x100ecf bytes_l100ecf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xecf 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ed9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ed9 (cmpR64Imm8Effect 0x100ed9 6 0x6) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 54) (.out 0x100ed9 (cmpR64Imm8Effect 0x100ed9 6 0x6) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 55) (.exec 0x100ed9 (fun s => s.RIP = 0x100ed9) (cmpR64Imm8Effect 0x100ed9 6 0x6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l1011f5, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100ee3, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100ed9 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x06, 0x0F, 0x86, 0x12, 0x03, 0x00, 0x00]

theorem code_l100ed9 : ∀ x ∈ codeRange 0x100ed9 bytes_l100ed9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xed9 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ee3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ee3 (cmpR64Imm8Effect 0x100ee3 6 0x7) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 54) (.exec 0x100ee3 (fun s => s.RIP = 0x100ee3) (cmpR64Imm8Effect 0x100ee3 6 0x7) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10120b, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100eed, RegMap.args [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100ee3 : List UInt8 :=
  [0x48, 0x83, 0xFE, 0x07, 0x0F, 0x84, 0x1E, 0x03, 0x00, 0x00]

theorem code_l100ee3 : ∀ x ∈ codeRange 0x100ee3 bytes_l100ee3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xee3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100eed_9 : Block Op Label signature Reg.count 391 :=
  .letOp (n := 391) (.out 0x101156 (xorR64R64Effect 0x101156 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[358, 350]
    (.letOp (n := 392) (.exec 0x101156 (fun s => s.RIP = 0x101156) (xorR64R64Effect 0x101156 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[358, 350]
    (.letOp (n := 393) (.out 0x101159 (xorR64R64Effect 0x101159 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[391, 370]
    (.letOp (n := 394) (.exec 0x101159 (fun s => s.RIP = 0x101159) (xorR64R64Effect 0x101159 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[391, 370]
    (.letOp (n := 395) (.exec 0x10115c (StorePre 0x10115c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10115c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10115c 13 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 13, .gpr 7] [])) #v[393, 7]
    (.letOp (n := 396) (.exec 0x101160 (StorePre 0x101160 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x101160 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101160 14 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[389, 7]
    (.letOp (n := 397) (.exec 0x101164 (StorePre 0x101164 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x101164 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101164 6 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[386, 7]
    (.letOp (n := 398) (.out 0x101168 (addR64Imm8Effect 0x101168 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 399) (.exec 0x101168 (fun s => s.RIP = 0x101168) (addR64Imm8Effect 0x101168 4 0x68) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 400) (.out 0x10116c (popR64Effect 0x10116c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[398]
    (.letOp (n := 401) (.out 0x10116c (popR64Effect 0x10116c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[398]
    (.letOp (n := 402) (.exec 0x10116c (PopPre 0x10116c) (popR64Effect 0x10116c 1 3) (Reg.operands [.gpr 4] [])) #v[398]
    (.letOp (n := 403) (.out 0x10116d (popR64Effect 0x10116d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[401]
    (.letOp (n := 404) (.out 0x10116d (popR64Effect 0x10116d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[401]
    (.letOp (n := 405) (.exec 0x10116d (PopPre 0x10116d) (popR64Effect 0x10116d 2 12) (Reg.operands [.gpr 4] [])) #v[401]
    (.letOp (n := 406) (.out 0x10116f (popR64Effect 0x10116f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[404]
    (.letOp (n := 407) (.out 0x10116f (popR64Effect 0x10116f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[404]
    (.letOp (n := 408) (.exec 0x10116f (PopPre 0x10116f) (popR64Effect 0x10116f 2 13) (Reg.operands [.gpr 4] [])) #v[404]
    (.letOp (n := 409) (.out 0x101171 (popR64Effect 0x101171 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[407]
    (.letOp (n := 410) (.out 0x101171 (popR64Effect 0x101171 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[407]
    (.letOp (n := 411) (.exec 0x101171 (PopPre 0x101171) (popR64Effect 0x101171 2 14) (Reg.operands [.gpr 4] [])) #v[407]
    (.letOp (n := 412) (.out 0x101173 (popR64Effect 0x101173 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[410]
    (.letOp (n := 413) (.out 0x101173 (popR64Effect 0x101173 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[410]
    (.letOp (n := 414) (.exec 0x101173 (PopPre 0x101173) (popR64Effect 0x101173 2 15) (Reg.operands [.gpr 4] [])) #v[410]
    (.letOp (n := 415) (.out 0x101175 (popR64Effect 0x101175 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[413]
    (.letOp (n := 416) (.out 0x101175 (popR64Effect 0x101175 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[413]
    (.letOp (n := 417) (.exec 0x101175 (PopPre 0x101175) (popR64Effect 0x101175 1 5) (Reg.operands [.gpr 4] [])) #v[413]
    (.letOp (n := 418) (.out 0x101176 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[416]
    (.letOp (n := 419) (.out 0x101176 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[416]
    (.letOp (n := 420) (.exec 0x101176 (RetPre 0x101176) (retEffect) (Reg.operands [.gpr 4] [])) #v[416]
    (.terminate (.ret (RegMap.args [(0, 370), (1, 338), (2, 383), (3, 400), (4, 419), (5, 415), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 406), (14, 409), (15, 412), (22, 22), (39, 39), (50, 50), (51, 51)] 421) (some ⟨418, by decide⟩))))))))))))))))))))))))))))))))

def bytes_l100eed_9 : List UInt8 :=
  [0x49, 0x31, 0xDD, 0x49, 0x31, 0xC5, 0x4C, 0x89, 0x6F, 0x28, 0x4C, 0x89, 0x77, 0x30, 0x48, 0x89,
    0x77, 0x38, 0x48, 0x83, 0xC4, 0x68, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D,
    0xC3]

theorem code_l100eed_9 : ∀ x ∈ codeRange 0x101156 bytes_l100eed_9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1156 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100eed_8 : Block Op Label signature Reg.count 356 :=
  .letOp (n := 356) (.out 0x101111 (xorR64R64Effect 0x101111 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[354, 324]
    (.letOp (n := 357) (.exec 0x101111 (fun s => s.RIP = 0x101111) (xorR64R64Effect 0x101111 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[354, 324]
    (.letOp (n := 358) (.out 0x101114 (xorR64R64Effect 0x101114 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[332, 310]
    (.letOp (n := 359) (.exec 0x101114 (fun s => s.RIP = 0x101114) (xorR64R64Effect 0x101114 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[332, 310]
    (.letOp (n := 360) (.out 0x101117 (xorR64M64Effect 0x101117 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[348, 4]
    (.letOp (n := 361) (.exec 0x101117 (LoadPre 0x101117 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101117 + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x101117 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 362) (.out 0x10111c (xorR64M64Effect 0x10111c 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[360, 4]
    (.letOp (n := 363) (.exec 0x10111c (LoadPre 0x10111c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10111c + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x10111c 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[360, 4]
    (.letOp (n := 364) (.out 0x101120 (xorR64R64Effect 0x101120 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[290, 362]
    (.letOp (n := 365) (.exec 0x101120 (fun s => s.RIP = 0x101120) (xorR64R64Effect 0x101120 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[290, 362]
    (.letOp (n := 366) (.out 0x101123 (xorR64R64Effect 0x101123 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[364, 338]
    (.letOp (n := 367) (.exec 0x101123 (fun s => s.RIP = 0x101123) (xorR64R64Effect 0x101123 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[364, 338]
    (.letOp (n := 368) (.out 0x101126 (movR64M64Effect 0x101126 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 369) (.exec 0x101126 (LoadPre 0x101126 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x101126 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101126 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 370) (.out 0x10112b (xorR64R64Effect 0x10112b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[368, 356]
    (.letOp (n := 371) (.exec 0x10112b (fun s => s.RIP = 0x10112b) (xorR64R64Effect 0x10112b 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[368, 356]
    (.letOp (n := 372) (.out 0x10112e (xorR64R64Effect 0x10112e 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[356, 366]
    (.letOp (n := 373) (.exec 0x10112e (fun s => s.RIP = 0x10112e) (xorR64R64Effect 0x10112e 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[356, 366]
    (.letOp (n := 374) (.out 0x101131 (xorR64R64Effect 0x101131 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[366, 278]
    (.letOp (n := 375) (.exec 0x101131 (fun s => s.RIP = 0x101131) (xorR64R64Effect 0x101131 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[366, 278]
    (.letOp (n := 376) (.exec 0x101134 (StorePre 0x101134 3 (fun s => AddrMode.addr (.base 7 .none) s (0x101134 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101134 5 (.base 7 .none)) (Reg.operands [.gpr 5, .gpr 7] [])) #v[374, 7]
    (.letOp (n := 377) (.exec 0x101137 (StorePre 0x101137 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x101137 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101137 8 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[372, 7]
    (.letOp (n := 378) (.out 0x10113b (xorR64R64Effect 0x10113b 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[342, 370]
    (.letOp (n := 379) (.exec 0x10113b (fun s => s.RIP = 0x10113b) (xorR64R64Effect 0x10113b 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[342, 370]
    (.letOp (n := 380) (.exec 0x10113e (StorePre 0x10113e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10113e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10113e 15 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[378, 7]
    (.letOp (n := 381) (.out 0x101142 (xorR64R64Effect 0x101142 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[314, 344]
    (.letOp (n := 382) (.exec 0x101142 (fun s => s.RIP = 0x101142) (xorR64R64Effect 0x101142 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[314, 344]
    (.letOp (n := 383) (.out 0x101145 (xorR64R64Effect 0x101145 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[362, 381]
    (.letOp (n := 384) (.exec 0x101145 (fun s => s.RIP = 0x101145) (xorR64R64Effect 0x101145 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[362, 381]
    (.letOp (n := 385) (.exec 0x101148 (StorePre 0x101148 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x101148 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101148 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[383, 7]
    (.letOp (n := 386) (.out 0x10114c (xorR64R64Effect 0x10114c 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[344, 350]
    (.letOp (n := 387) (.exec 0x10114c (fun s => s.RIP = 0x10114c) (xorR64R64Effect 0x10114c 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[344, 350]
    (.letOp (n := 388) (.exec 0x10114f (StorePre 0x10114f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10114f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10114f 14 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[381, 7]
    (.letOp (n := 389) (.out 0x101153 (xorR64R64Effect 0x101153 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[381, 350]
    (.letOp (n := 390) (.exec 0x101153 (fun s => s.RIP = 0x101153) (xorR64R64Effect 0x101153 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[381, 350]
    (b_l100eed_9)))))))))))))))))))))))))))))))))))

def bytes_l100eed_8 : List UInt8 :=
  [0x4D, 0x31, 0xD8, 0x4D, 0x31, 0xD5, 0x48, 0x33, 0x54, 0x24, 0x20, 0x48, 0x33, 0x14, 0x24, 0x48,
    0x31, 0xD5, 0x48, 0x31, 0xCD, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x4C, 0x31, 0xC0, 0x49, 0x31, 0xE8,
    0x4C, 0x31, 0xCD, 0x48, 0x89, 0x2F, 0x4C, 0x89, 0x47, 0x08, 0x49, 0x31, 0xC7, 0x4C, 0x89, 0x7F,
    0x10, 0x49, 0x31, 0xF6, 0x4C, 0x31, 0xF2, 0x48, 0x89, 0x57, 0x18, 0x48, 0x31, 0xDE, 0x4C, 0x89,
    0x77, 0x20, 0x49, 0x31, 0xDE] ++ bytes_l100eed_9

theorem code_l100eed_8 : ∀ x ∈ codeRange 0x101111 bytes_l100eed_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1111 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_9

@[cfg_block] def b_l100eed_7 : Block Op Label signature Reg.count 316 :=
  .letOp (n := 316) (.out 0x1010c9 (xorR64R64Effect 0x1010c9 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[259, 261]
    (.letOp (n := 317) (.exec 0x1010c9 (fun s => s.RIP = 0x1010c9) (xorR64R64Effect 0x1010c9 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[259, 261]
    (.letOp (n := 318) (.out 0x1010cc (xorR64R64Effect 0x1010cc 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[296, 316]
    (.letOp (n := 319) (.exec 0x1010cc (fun s => s.RIP = 0x1010cc) (xorR64R64Effect 0x1010cc 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[296, 316]
    (.letOp (n := 320) (.out 0x1010cf (movR64M64Effect 0x1010cf 11 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 321) (.exec 0x1010cf (LoadPre 0x1010cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1010cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010cf 11 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 322) (.out 0x1010d4 (andR64R64Effect 0x1010d4 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[320, 318]
    (.letOp (n := 323) (.exec 0x1010d4 (fun s => s.RIP = 0x1010d4) (andR64R64Effect 0x1010d4 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[320, 318]
    (.letOp (n := 324) (.out 0x1010d7 (xorR64R64Effect 0x1010d7 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[322, 304]
    (.letOp (n := 325) (.exec 0x1010d7 (fun s => s.RIP = 0x1010d7) (xorR64R64Effect 0x1010d7 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[322, 304]
    (.letOp (n := 326) (.out 0x1010da (andR64M64Effect 0x1010da 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[318, 4]
    (.letOp (n := 327) (.exec 0x1010da (LoadPre 0x1010da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1010da + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x1010da 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[318, 4]
    (.letOp (n := 328) (.out 0x1010df (movR64M64Effect 0x1010df 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 329) (.exec 0x1010df (LoadPre 0x1010df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1010df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010df 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 330) (.out 0x1010e4 (andR64R64Effect 0x1010e4 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[328, 316]
    (.letOp (n := 331) (.exec 0x1010e4 (fun s => s.RIP = 0x1010e4) (andR64R64Effect 0x1010e4 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[328, 316]
    (.letOp (n := 332) (.out 0x1010e7 (andR64M64Effect 0x1010e7 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[316, 4]
    (.letOp (n := 333) (.exec 0x1010e7 (LoadPre 0x1010e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1010e7 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x1010e7 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[316, 4]
    (.letOp (n := 334) (.out 0x1010ec (movR64M64Effect 0x1010ec 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 335) (.exec 0x1010ec (LoadPre 0x1010ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1010ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010ec 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 336) (.out 0x1010f1 (andR64R64Effect 0x1010f1 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[334, 261]
    (.letOp (n := 337) (.exec 0x1010f1 (fun s => s.RIP = 0x1010f1) (andR64R64Effect 0x1010f1 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[334, 261]
    (.letOp (n := 338) (.out 0x1010f4 (xorR64R64Effect 0x1010f4 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[326, 332]
    (.letOp (n := 339) (.exec 0x1010f4 (fun s => s.RIP = 0x1010f4) (xorR64R64Effect 0x1010f4 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[326, 332]
    (.letOp (n := 340) (.out 0x1010f7 (xorR64R64Effect 0x1010f7 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[298, 338]
    (.letOp (n := 341) (.exec 0x1010f7 (fun s => s.RIP = 0x1010f7) (xorR64R64Effect 0x1010f7 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[298, 338]
    (.letOp (n := 342) (.out 0x1010fa (xorR64R64Effect 0x1010fa 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[336, 340]
    (.letOp (n := 343) (.exec 0x1010fa (fun s => s.RIP = 0x1010fa) (xorR64R64Effect 0x1010fa 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[336, 340]
    (.letOp (n := 344) (.out 0x1010fd (xorR64R64Effect 0x1010fd 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[340, 288]
    (.letOp (n := 345) (.exec 0x1010fd (fun s => s.RIP = 0x1010fd) (xorR64R64Effect 0x1010fd 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[340, 288]
    (.letOp (n := 346) (.out 0x101100 (andR64M64Effect 0x101100 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[261, 4]
    (.letOp (n := 347) (.exec 0x101100 (LoadPre 0x101100 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101100 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x101100 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[261, 4]
    (.letOp (n := 348) (.out 0x101105 (xorR64R64Effect 0x101105 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[346, 284]
    (.letOp (n := 349) (.exec 0x101105 (fun s => s.RIP = 0x101105) (xorR64R64Effect 0x101105 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[346, 284]
    (.letOp (n := 350) (.out 0x101108 (xorR64R64Effect 0x101108 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[330, 324]
    (.letOp (n := 351) (.exec 0x101108 (fun s => s.RIP = 0x101108) (xorR64R64Effect 0x101108 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[330, 324]
    (.letOp (n := 352) (.out 0x10110b (xorR64R64Effect 0x10110b 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[306, 348]
    (.letOp (n := 353) (.exec 0x10110b (fun s => s.RIP = 0x10110b) (xorR64R64Effect 0x10110b 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[306, 348]
    (.letOp (n := 354) (.out 0x10110e (xorR64R64Effect 0x10110e 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[352, 278]
    (.letOp (n := 355) (.exec 0x10110e (fun s => s.RIP = 0x10110e) (xorR64R64Effect 0x10110e 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[352, 278]
    (b_l100eed_8))))))))))))))))))))))))))))))))))))))))

def bytes_l100eed_7 : List UInt8 :=
  [0x49, 0x31, 0xD5, 0x4C, 0x31, 0xE9, 0x4C, 0x8B, 0x5C, 0x24, 0x50, 0x49, 0x21, 0xCB, 0x4D, 0x31,
    0xFB, 0x48, 0x23, 0x4C, 0x24, 0x58, 0x48, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x21, 0xEB, 0x4C, 0x23,
    0x6C, 0x24, 0x60, 0x4C, 0x8B, 0x7C, 0x24, 0x08, 0x49, 0x21, 0xD7, 0x4C, 0x31, 0xE9, 0x48, 0x31,
    0xCE, 0x49, 0x31, 0xF7, 0x48, 0x31, 0xC6, 0x48, 0x23, 0x54, 0x24, 0x40, 0x4C, 0x31, 0xE2, 0x4C,
    0x31, 0xDB, 0x49, 0x31, 0xD0, 0x4D, 0x31, 0xC8] ++ bytes_l100eed_8

theorem code_l100eed_7 : ∀ x ∈ codeRange 0x1010c9 bytes_l100eed_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10c9 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_8

@[cfg_block] def b_l100eed_6 : Block Op Label signature Reg.count 278 :=
  .letOp (n := 278) (.out 0x101081 (andR64M64Effect 0x101081 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[273, 4]
    (.letOp (n := 279) (.exec 0x101081 (LoadPre 0x101081 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101081 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x101081 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[273, 4]
    (.letOp (n := 280) (.out 0x101086 (xorR64R64Effect 0x101086 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[263, 227]
    (.letOp (n := 281) (.exec 0x101086 (fun s => s.RIP = 0x101086) (xorR64R64Effect 0x101086 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[263, 227]
    (.letOp (n := 282) (.out 0x101089 (movR64M64Effect 0x101089 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 283) (.exec 0x101089 (LoadPre 0x101089 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101089 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101089 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x10108e (andR64R64Effect 0x10108e 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[282, 280]
    (.letOp (n := 285) (.exec 0x10108e (fun s => s.RIP = 0x10108e) (andR64R64Effect 0x10108e 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[282, 280]
    (.letOp (n := 286) (.out 0x101091 (movR64R64Effect 0x101091 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[280]
    (.letOp (n := 287) (.exec 0x101091 (fun s => s.RIP = 0x101091) (movR64R64Effect 0x101091 14 0) (Reg.operands [.gpr 0] [])) #v[280]
    (.letOp (n := 288) (.out 0x101094 (andR64M64Effect 0x101094 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[280, 4]
    (.letOp (n := 289) (.exec 0x101094 (LoadPre 0x101094 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101094 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x101094 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[280, 4]
    (.letOp (n := 290) (.out 0x101099 (andR64R64Effect 0x101099 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[193, 269]
    (.letOp (n := 291) (.exec 0x101099 (fun s => s.RIP = 0x101099) (andR64R64Effect 0x101099 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[193, 269]
    (.letOp (n := 292) (.out 0x10109c (andR64R64Effect 0x10109c 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[149, 269]
    (.letOp (n := 293) (.exec 0x10109c (fun s => s.RIP = 0x10109c) (andR64R64Effect 0x10109c 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[149, 269]
    (.letOp (n := 294) (.out 0x10109f (xorR64R64Effect 0x10109f 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[286, 261]
    (.letOp (n := 295) (.exec 0x10109f (fun s => s.RIP = 0x10109f) (xorR64R64Effect 0x10109f 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[286, 261]
    (.letOp (n := 296) (.out 0x1010a2 (xorR64R64Effect 0x1010a2 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[269, 294]
    (.letOp (n := 297) (.exec 0x1010a2 (fun s => s.RIP = 0x1010a2) (xorR64R64Effect 0x1010a2 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[269, 294]
    (.letOp (n := 298) (.out 0x1010a5 (andR64R64Effect 0x1010a5 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[211, 294]
    (.letOp (n := 299) (.exec 0x1010a5 (fun s => s.RIP = 0x1010a5) (andR64R64Effect 0x1010a5 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[211, 294]
    (.letOp (n := 300) (.out 0x1010a8 (andR64R64Effect 0x1010a8 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[294, 207]
    (.letOp (n := 301) (.exec 0x1010a8 (fun s => s.RIP = 0x1010a8) (andR64R64Effect 0x1010a8 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[294, 207]
    (.letOp (n := 302) (.exec 0x1010ab (StorePre 0x1010ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1010ab + BitVec.ofNat 64 5)) 8) (andMREffect 0x1010ab 5 64 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 303) (.exec 0x1010b0 (StorePre 0x1010b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1010b0 + BitVec.ofNat 64 5)) 8) (andMREffect 0x1010b0 5 64 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 304) (.out 0x1010b5 (xorR64R64Effect 0x1010b5 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[292, 275]
    (.letOp (n := 305) (.exec 0x1010b5 (fun s => s.RIP = 0x1010b5) (xorR64R64Effect 0x1010b5 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[292, 275]
    (.letOp (n := 306) (.out 0x1010b8 (andR64R64Effect 0x1010b8 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[114, 296]
    (.letOp (n := 307) (.exec 0x1010b8 (fun s => s.RIP = 0x1010b8) (andR64R64Effect 0x1010b8 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[114, 296]
    (.letOp (n := 308) (.out 0x1010bb (movR64M64Effect 0x1010bb 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 309) (.exec 0x1010bb (LoadPre 0x1010bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1010bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010bb 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 310) (.out 0x1010c0 (andR64R64Effect 0x1010c0 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[308, 296]
    (.letOp (n := 311) (.exec 0x1010c0 (fun s => s.RIP = 0x1010c0) (andR64R64Effect 0x1010c0 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[308, 296]
    (.letOp (n := 312) (.out 0x1010c3 (xorR64R64Effect 0x1010c3 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[300, 284]
    (.letOp (n := 313) (.exec 0x1010c3 (fun s => s.RIP = 0x1010c3) (xorR64R64Effect 0x1010c3 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[300, 284]
    (.letOp (n := 314) (.out 0x1010c6 (xorR64R64Effect 0x1010c6 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[312, 304]
    (.letOp (n := 315) (.exec 0x1010c6 (fun s => s.RIP = 0x1010c6) (xorR64R64Effect 0x1010c6 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[312, 304]
    (b_l100eed_7))))))))))))))))))))))))))))))))))))))

def bytes_l100eed_6 : List UInt8 :=
  [0x4C, 0x23, 0x4C, 0x24, 0x10, 0x4C, 0x31, 0xD8, 0x4C, 0x8B, 0x64, 0x24, 0x18, 0x49, 0x21, 0xC4,
    0x49, 0x89, 0xC6, 0x48, 0x23, 0x44, 0x24, 0x28, 0x48, 0x21, 0xCD, 0x49, 0x21, 0xCF, 0x49, 0x31,
    0xD6, 0x4C, 0x31, 0xF1, 0x4C, 0x21, 0xF6, 0x4D, 0x21, 0xD6, 0x4C, 0x21, 0x6C, 0x24, 0x30, 0x4C,
    0x21, 0x6C, 0x24, 0x20, 0x49, 0x31, 0xDF, 0x49, 0x21, 0xC8, 0x4C, 0x8B, 0x54, 0x24, 0x38, 0x49,
    0x21, 0xCA, 0x4D, 0x31, 0xE6, 0x4D, 0x31, 0xFE] ++ bytes_l100eed_7

theorem code_l100eed_6 : ∀ x ∈ codeRange 0x101081 bytes_l100eed_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1081 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_7

@[cfg_block] def b_l100eed_5 : Block Op Label signature Reg.count 239 :=
  .letOp (n := 239) (.out 0x101044 (andR64R64Effect 0x101044 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[237, 235]
    (.letOp (n := 240) (.exec 0x101044 (fun s => s.RIP = 0x101044) (andR64R64Effect 0x101044 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[237, 235]
    (.letOp (n := 241) (.out 0x101047 (movR64R64Effect 0x101047 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[191]
    (.letOp (n := 242) (.exec 0x101047 (fun s => s.RIP = 0x101047) (movR64R64Effect 0x101047 12 1) (Reg.operands [.gpr 1] [])) #v[191]
    (.letOp (n := 243) (.out 0x10104a (xorR64R64Effect 0x10104a 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[241, 225]
    (.letOp (n := 244) (.exec 0x10104a (fun s => s.RIP = 0x10104a) (xorR64R64Effect 0x10104a 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[241, 225]
    (.letOp (n := 245) (.out 0x10104d (movR64R64Effect 0x10104d 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[239]
    (.letOp (n := 246) (.exec 0x10104d (fun s => s.RIP = 0x10104d) (movR64R64Effect 0x10104d 2 0) (Reg.operands [.gpr 0] [])) #v[239]
    (.letOp (n := 247) (.out 0x101050 (xorR64R64Effect 0x101050 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[239, 231]
    (.letOp (n := 248) (.exec 0x101050 (fun s => s.RIP = 0x101050) (xorR64R64Effect 0x101050 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[239, 231]
    (.letOp (n := 249) (.out 0x101053 (movR64R64Effect 0x101053 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[231]
    (.letOp (n := 250) (.exec 0x101053 (fun s => s.RIP = 0x101053) (movR64R64Effect 0x101053 1 13) (Reg.operands [.gpr 13] [])) #v[231]
    (.letOp (n := 251) (.out 0x101056 (xorR64R64Effect 0x101056 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[249, 243]
    (.letOp (n := 252) (.exec 0x101056 (fun s => s.RIP = 0x101056) (xorR64R64Effect 0x101056 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[249, 243]
    (.letOp (n := 253) (.out 0x101059 (xorR64R64Effect 0x101059 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[221, 187]
    (.letOp (n := 254) (.exec 0x101059 (fun s => s.RIP = 0x101059) (xorR64R64Effect 0x101059 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[221, 187]
    (.letOp (n := 255) (.out 0x10105c (movR64R64Effect 0x10105c 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[251]
    (.letOp (n := 256) (.exec 0x10105c (fun s => s.RIP = 0x10105c) (movR64R64Effect 0x10105c 13 1) (Reg.operands [.gpr 1] [])) #v[251]
    (.letOp (n := 257) (.out 0x10105f (andR64R64Effect 0x10105f 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[255, 253]
    (.letOp (n := 258) (.exec 0x10105f (fun s => s.RIP = 0x10105f) (andR64R64Effect 0x10105f 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[255, 253]
    (.letOp (n := 259) (.out 0x101062 (xorR64R64Effect 0x101062 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[257, 187]
    (.letOp (n := 260) (.exec 0x101062 (fun s => s.RIP = 0x101062) (xorR64R64Effect 0x101062 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[257, 187]
    (.letOp (n := 261) (.out 0x101065 (xorR64R64Effect 0x101065 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[245, 243]
    (.letOp (n := 262) (.exec 0x101065 (fun s => s.RIP = 0x101065) (xorR64R64Effect 0x101065 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[245, 243]
    (.letOp (n := 263) (.out 0x101068 (andR64R64Effect 0x101068 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[247, 243]
    (.letOp (n := 264) (.exec 0x101068 (fun s => s.RIP = 0x101068) (andR64R64Effect 0x101068 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[247, 243]
    (.letOp (n := 265) (.out 0x10106b (xorR64R64Effect 0x10106b 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[251, 263]
    (.letOp (n := 266) (.exec 0x10106b (fun s => s.RIP = 0x10106b) (xorR64R64Effect 0x10106b 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[251, 263]
    (.letOp (n := 267) (.out 0x10106e (andR64R64Effect 0x10106e 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[265, 259]
    (.letOp (n := 268) (.exec 0x10106e (fun s => s.RIP = 0x10106e) (andR64R64Effect 0x10106e 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[265, 259]
    (.letOp (n := 269) (.out 0x101071 (xorR64R64Effect 0x101071 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[267, 253]
    (.letOp (n := 270) (.exec 0x101071 (fun s => s.RIP = 0x101071) (xorR64R64Effect 0x101071 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[267, 253]
    (.letOp (n := 271) (.out 0x101074 (movR64R64Effect 0x101074 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[269]
    (.letOp (n := 272) (.exec 0x101074 (fun s => s.RIP = 0x101074) (movR64R64Effect 0x101074 9 1) (Reg.operands [.gpr 1] [])) #v[269]
    (.letOp (n := 273) (.out 0x101077 (xorR64R64Effect 0x101077 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[271, 259]
    (.letOp (n := 274) (.exec 0x101077 (fun s => s.RIP = 0x101077) (xorR64R64Effect 0x101077 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[271, 259]
    (.letOp (n := 275) (.out 0x10107a (andR64R64Effect 0x10107a 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[225, 273]
    (.letOp (n := 276) (.exec 0x10107a (fun s => s.RIP = 0x10107a) (andR64R64Effect 0x10107a 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[225, 273]
    (.letOp (n := 277) (.exec 0x10107d (StorePre 0x10107d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10107d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10107d 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[275, 4]
    (b_l100eed_6)))))))))))))))))))))))))))))))))))))))

def bytes_l100eed_5 : List UInt8 :=
  [0x48, 0x21, 0xD0, 0x49, 0x89, 0xCC, 0x49, 0x31, 0xDC, 0x48, 0x89, 0xC2, 0x4C, 0x31, 0xE8, 0x4C,
    0x89, 0xE9, 0x4C, 0x31, 0xE1, 0x4D, 0x31, 0xF1, 0x49, 0x89, 0xCD, 0x4D, 0x21, 0xCD, 0x4D, 0x31,
    0xF5, 0x4C, 0x31, 0xE2, 0x4C, 0x21, 0xE0, 0x48, 0x31, 0xC1, 0x4C, 0x21, 0xE9, 0x4C, 0x31, 0xC9,
    0x49, 0x89, 0xC9, 0x4D, 0x31, 0xE9, 0x4C, 0x21, 0xCB, 0x48, 0x89, 0x1C, 0x24] ++ bytes_l100eed_6

theorem code_l100eed_5 : ∀ x ∈ codeRange 0x101044 bytes_l100eed_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1044 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_6

@[cfg_block] def b_l100eed_4 : Block Op Label signature Reg.count 199 :=
  .letOp (n := 199) (.out 0x101005 (xorR64R64Effect 0x101005 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[197, 168]
    (.letOp (n := 200) (.exec 0x101005 (fun s => s.RIP = 0x101005) (xorR64R64Effect 0x101005 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[197, 168]
    (.letOp (n := 201) (.out 0x101008 (xorR64R64Effect 0x101008 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[199, 170]
    (.letOp (n := 202) (.exec 0x101008 (fun s => s.RIP = 0x101008) (xorR64R64Effect 0x101008 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[199, 170]
    (.letOp (n := 203) (.out 0x10100b (xorR64R64Effect 0x10100b 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[89, 164]
    (.letOp (n := 204) (.exec 0x10100b (fun s => s.RIP = 0x10100b) (xorR64R64Effect 0x10100b 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[89, 164]
    (.letOp (n := 205) (.out 0x10100e (movR64M64Effect 0x10100e 10 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 206) (.exec 0x10100e (LoadPre 0x10100e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10100e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10100e 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 207) (.out 0x101013 (xorR64R64Effect 0x101013 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[205, 133]
    (.letOp (n := 208) (.exec 0x101013 (fun s => s.RIP = 0x101013) (xorR64R64Effect 0x101013 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[205, 133]
    (.letOp (n := 209) (.out 0x101016 (movR64R64Effect 0x101016 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[193]
    (.letOp (n := 210) (.exec 0x101016 (fun s => s.RIP = 0x101016) (movR64R64Effect 0x101016 6 5) (Reg.operands [.gpr 5] [])) #v[193]
    (.letOp (n := 211) (.out 0x101019 (xorR64R64Effect 0x101019 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[209, 129]
    (.letOp (n := 212) (.exec 0x101019 (fun s => s.RIP = 0x101019) (xorR64R64Effect 0x101019 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[209, 129]
    (.letOp (n := 213) (.out 0x10101c (movR64R64Effect 0x10101c 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[207]
    (.letOp (n := 214) (.exec 0x10101c (fun s => s.RIP = 0x10101c) (movR64R64Effect 0x10101c 11 10) (Reg.operands [.gpr 10] [])) #v[207]
    (.letOp (n := 215) (.out 0x10101f (andR64R64Effect 0x10101f 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[213, 211]
    (.letOp (n := 216) (.exec 0x10101f (fun s => s.RIP = 0x10101f) (andR64R64Effect 0x10101f 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[213, 211]
    (.letOp (n := 217) (.out 0x101022 (xorR64R64Effect 0x101022 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[203, 215]
    (.letOp (n := 218) (.exec 0x101022 (fun s => s.RIP = 0x101022) (xorR64R64Effect 0x101022 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[203, 215]
    (.letOp (n := 219) (.out 0x101025 (xorR64R64Effect 0x101025 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[201, 123]
    (.letOp (n := 220) (.exec 0x101025 (fun s => s.RIP = 0x101025) (xorR64R64Effect 0x101025 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[201, 123]
    (.letOp (n := 221) (.out 0x101028 (xorR64R64Effect 0x101028 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[217, 123]
    (.letOp (n := 222) (.exec 0x101028 (fun s => s.RIP = 0x101028) (xorR64R64Effect 0x101028 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[217, 123]
    (.letOp (n := 223) (.out 0x10102b (movR64R64Effect 0x10102b 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[219]
    (.letOp (n := 224) (.exec 0x10102b (fun s => s.RIP = 0x10102b) (movR64R64Effect 0x10102b 11 0) (Reg.operands [.gpr 0] [])) #v[219]
    (.letOp (n := 225) (.out 0x10102e (movR64M64Effect 0x10102e 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 226) (.exec 0x10102e (LoadPre 0x10102e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10102e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10102e 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 227) (.out 0x101032 (xorR64R64Effect 0x101032 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[223, 225]
    (.letOp (n := 228) (.exec 0x101032 (fun s => s.RIP = 0x101032) (xorR64R64Effect 0x101032 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[223, 225]
    (.letOp (n := 229) (.out 0x101035 (movR64R64Effect 0x101035 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 11] []) (.reg (.gpr 13))) #v[227]
    (.letOp (n := 230) (.exec 0x101035 (fun s => s.RIP = 0x101035) (movR64R64Effect 0x101035 13 11) (Reg.operands [.gpr 11] [])) #v[227]
    (.letOp (n := 231) (.out 0x101038 (andR64R64Effect 0x101038 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[229, 221]
    (.letOp (n := 232) (.exec 0x101038 (fun s => s.RIP = 0x101038) (andR64R64Effect 0x101038 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[229, 221]
    (.letOp (n := 233) (.out 0x10103b (movR64R64Effect 0x10103b 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[231]
    (.letOp (n := 234) (.exec 0x10103b (fun s => s.RIP = 0x10103b) (movR64R64Effect 0x10103b 2 13) (Reg.operands [.gpr 13] [])) #v[231]
    (.letOp (n := 235) (.out 0x10103e (xorR64R64Effect 0x10103e 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[233, 187]
    (.letOp (n := 236) (.exec 0x10103e (fun s => s.RIP = 0x10103e) (xorR64R64Effect 0x10103e 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[233, 187]
    (.letOp (n := 237) (.out 0x101041 (xorR64R64Effect 0x101041 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[219, 191]
    (.letOp (n := 238) (.exec 0x101041 (fun s => s.RIP = 0x101041) (xorR64R64Effect 0x101041 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[219, 191]
    (b_l100eed_5))))))))))))))))))))))))))))))))))))))))

def bytes_l100eed_4 : List UInt8 :=
  [0x48, 0x31, 0xD8, 0x4C, 0x31, 0xD8, 0x49, 0x31, 0xF1, 0x4C, 0x8B, 0x54, 0x24, 0x18, 0x4D, 0x31,
    0xEA, 0x48, 0x89, 0xEE, 0x4C, 0x31, 0xE6, 0x4D, 0x89, 0xD3, 0x49, 0x21, 0xF3, 0x4D, 0x31, 0xD9,
    0x48, 0x31, 0xD0, 0x49, 0x31, 0xD1, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x1C, 0x24, 0x49, 0x31, 0xDB,
    0x4D, 0x89, 0xDD, 0x4D, 0x21, 0xCD, 0x4C, 0x89, 0xEA, 0x4C, 0x31, 0xF2, 0x48, 0x31, 0xC8] ++ bytes_l100eed_5

theorem code_l100eed_4 : ∀ x ∈ codeRange 0x101005 bytes_l100eed_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1005 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_5

@[cfg_block] def b_l100eed_3 : Block Op Label signature Reg.count 162 :=
  .letOp (n := 162) (.out 0x100fbd (movR64R64Effect 0x100fbd 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[87]
    (.letOp (n := 163) (.exec 0x100fbd (fun s => s.RIP = 0x100fbd) (movR64R64Effect 0x100fbd 6 14) (Reg.operands [.gpr 14] [])) #v[87]
    (.letOp (n := 164) (.out 0x100fc0 (andR64M64Effect 0x100fc0 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[162, 4]
    (.letOp (n := 165) (.exec 0x100fc0 (LoadPre 0x100fc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100fc0 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x100fc0 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[162, 4]
    (.letOp (n := 166) (.out 0x100fc5 (movR64R64Effect 0x100fc5 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[146]
    (.letOp (n := 167) (.exec 0x100fc5 (fun s => s.RIP = 0x100fc5) (movR64R64Effect 0x100fc5 11 3) (Reg.operands [.gpr 3] [])) #v[146]
    (.letOp (n := 168) (.out 0x100fc8 (movR64M64Effect 0x100fc8 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 169) (.exec 0x100fc8 (LoadPre 0x100fc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100fc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100fc8 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 170) (.out 0x100fcd (andR64R64Effect 0x100fcd 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[166, 168]
    (.letOp (n := 171) (.exec 0x100fcd (fun s => s.RIP = 0x100fcd) (andR64R64Effect 0x100fcd 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[166, 168]
    (.letOp (n := 172) (.out 0x100fd0 (movR64M64Effect 0x100fd0 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 173) (.exec 0x100fd0 (LoadPre 0x100fd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100fd0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100fd0 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.out 0x100fd5 (xorR64R64Effect 0x100fd5 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[172, 149]
    (.letOp (n := 175) (.exec 0x100fd5 (fun s => s.RIP = 0x100fd5) (xorR64R64Effect 0x100fd5 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[172, 149]
    (.letOp (n := 176) (.exec 0x100fd8 (StorePre 0x100fd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100fd8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100fd8 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[174, 4]
    (.letOp (n := 177) (.out 0x100fdd (andR64R64Effect 0x100fdd 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[174, 133]
    (.letOp (n := 178) (.exec 0x100fdd (fun s => s.RIP = 0x100fdd) (andR64R64Effect 0x100fdd 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[174, 133]
    (.letOp (n := 179) (.exec 0x100fe0 (StorePre 0x100fe0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100fe0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100fe0 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[133, 4]
    (.letOp (n := 180) (.out 0x100fe5 (xorR64R64Effect 0x100fe5 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[177, 129]
    (.letOp (n := 181) (.exec 0x100fe5 (fun s => s.RIP = 0x100fe5) (xorR64R64Effect 0x100fe5 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[177, 129]
    (.letOp (n := 182) (.exec 0x100fe8 (StorePre 0x100fe8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100fe8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100fe8 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[129, 4]
    (.letOp (n := 183) (.out 0x100fed (xorR64R64Effect 0x100fed 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[180, 164]
    (.letOp (n := 184) (.exec 0x100fed (fun s => s.RIP = 0x100fed) (xorR64R64Effect 0x100fed 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[180, 164]
    (.letOp (n := 185) (.out 0x100ff0 (xorR64R64Effect 0x100ff0 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[183, 114]
    (.letOp (n := 186) (.exec 0x100ff0 (fun s => s.RIP = 0x100ff0) (xorR64R64Effect 0x100ff0 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[183, 114]
    (.letOp (n := 187) (.out 0x100ff3 (xorR64R64Effect 0x100ff3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[185, 131]
    (.letOp (n := 188) (.exec 0x100ff3 (fun s => s.RIP = 0x100ff3) (xorR64R64Effect 0x100ff3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[185, 131]
    (.letOp (n := 189) (.out 0x100ff6 (xorR64R64Effect 0x100ff6 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[131, 170]
    (.letOp (n := 190) (.exec 0x100ff6 (fun s => s.RIP = 0x100ff6) (xorR64R64Effect 0x100ff6 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[131, 170]
    (.letOp (n := 191) (.out 0x100ff9 (xorR64R64Effect 0x100ff9 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[189, 160]
    (.letOp (n := 192) (.exec 0x100ff9 (fun s => s.RIP = 0x100ff9) (xorR64R64Effect 0x100ff9 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[189, 160]
    (.letOp (n := 193) (.out 0x100ffc (xorR64R64Effect 0x100ffc 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[53, 149]
    (.letOp (n := 194) (.exec 0x100ffc (fun s => s.RIP = 0x100ffc) (xorR64R64Effect 0x100ffc 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[53, 149]
    (.letOp (n := 195) (.out 0x100fff (movR64R64Effect 0x100fff 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[193]
    (.letOp (n := 196) (.exec 0x100fff (fun s => s.RIP = 0x100fff) (movR64R64Effect 0x100fff 0 5) (Reg.operands [.gpr 5] [])) #v[193]
    (.letOp (n := 197) (.out 0x101002 (andR64R64Effect 0x101002 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[195, 149]
    (.letOp (n := 198) (.exec 0x101002 (fun s => s.RIP = 0x101002) (andR64R64Effect 0x101002 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[195, 149]
    (b_l100eed_4)))))))))))))))))))))))))))))))))))))

def bytes_l100eed_3 : List UInt8 :=
  [0x4C, 0x89, 0xF6, 0x48, 0x23, 0x74, 0x24, 0x28, 0x49, 0x89, 0xDB, 0x48, 0x8B, 0x5C, 0x24, 0x10,
    0x49, 0x21, 0xDB, 0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4D, 0x31, 0xFE, 0x4C, 0x89, 0x74, 0x24, 0x08,
    0x4D, 0x21, 0xEE, 0x4C, 0x89, 0x6C, 0x24, 0x40, 0x4D, 0x31, 0xE6, 0x4C, 0x89, 0x64, 0x24, 0x38,
    0x49, 0x31, 0xF6, 0x4D, 0x31, 0xC6, 0x49, 0x31, 0xCE, 0x4C, 0x31, 0xD9, 0x4C, 0x31, 0xD1, 0x4C,
    0x31, 0xFD, 0x48, 0x89, 0xE8, 0x4C, 0x21, 0xF8] ++ bytes_l100eed_4

theorem code_l100eed_3 : ∀ x ∈ codeRange 0x100fbd bytes_l100eed_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfbd 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_4

@[cfg_block] def b_l100eed_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.out 0x100f7c (movR64R64Effect 0x100f7c 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[114]
    (.letOp (n := 126) (.exec 0x100f7c (fun s => s.RIP = 0x100f7c) (movR64R64Effect 0x100f7c 1 8) (Reg.operands [.gpr 8] [])) #v[114]
    (.letOp (n := 127) (.out 0x100f7f (andR64R64Effect 0x100f7f 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[125, 109]
    (.letOp (n := 128) (.exec 0x100f7f (fun s => s.RIP = 0x100f7f) (andR64R64Effect 0x100f7f 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[125, 109]
    (.letOp (n := 129) (.out 0x100f82 (movR64R64Effect 0x100f82 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 10] []) (.reg (.gpr 12))) #v[109]
    (.letOp (n := 130) (.exec 0x100f82 (fun s => s.RIP = 0x100f82) (movR64R64Effect 0x100f82 12 10) (Reg.operands [.gpr 10] [])) #v[109]
    (.letOp (n := 131) (.out 0x100f85 (xorR64R64Effect 0x100f85 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[127, 105]
    (.letOp (n := 132) (.exec 0x100f85 (fun s => s.RIP = 0x100f85) (xorR64R64Effect 0x100f85 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[127, 105]
    (.letOp (n := 133) (.out 0x100f88 (movR64M64Effect 0x100f88 13 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[7]
    (.letOp (n := 134) (.exec 0x100f88 (LoadPre 0x100f88 (fun s => AddrMode.addr (.base 7 .none) s (0x100f88 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100f88 13 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 135) (.out 0x100f8b (movR64R64Effect 0x100f8b 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[102]
    (.letOp (n := 136) (.exec 0x100f8b (fun s => s.RIP = 0x100f8b) (movR64R64Effect 0x100f8b 6 3) (Reg.operands [.gpr 3] [])) #v[102]
    (.letOp (n := 137) (.out 0x100f8e (xorR64R64Effect 0x100f8e 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[135, 133]
    (.letOp (n := 138) (.exec 0x100f8e (fun s => s.RIP = 0x100f8e) (xorR64R64Effect 0x100f8e 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[135, 133]
    (.letOp (n := 139) (.out 0x100f91 (movR64R64Effect 0x100f91 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[137]
    (.letOp (n := 140) (.exec 0x100f91 (fun s => s.RIP = 0x100f91) (movR64R64Effect 0x100f91 11 6) (Reg.operands [.gpr 6] [])) #v[137]
    (.letOp (n := 141) (.exec 0x100f94 (StorePre 0x100f94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100f94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f94 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[137, 4]
    (.letOp (n := 142) (.out 0x100f99 (movR64R64Effect 0x100f99 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[102]
    (.letOp (n := 143) (.exec 0x100f99 (fun s => s.RIP = 0x100f99) (movR64R64Effect 0x100f99 6 3) (Reg.operands [.gpr 3] [])) #v[102]
    (.letOp (n := 144) (.out 0x100f9c (xorR64R64Effect 0x100f9c 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[142, 107]
    (.letOp (n := 145) (.exec 0x100f9c (fun s => s.RIP = 0x100f9c) (xorR64R64Effect 0x100f9c 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[142, 107]
    (.letOp (n := 146) (.out 0x100f9f (movR64R64Effect 0x100f9f 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[144]
    (.letOp (n := 147) (.exec 0x100f9f (fun s => s.RIP = 0x100f9f) (movR64R64Effect 0x100f9f 3 6) (Reg.operands [.gpr 6] [])) #v[144]
    (.letOp (n := 148) (.exec 0x100fa2 (StorePre 0x100fa2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100fa2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100fa2 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[144, 4]
    (.letOp (n := 149) (.out 0x100fa6 (xorR64R64Effect 0x100fa6 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[107, 133]
    (.letOp (n := 150) (.exec 0x100fa6 (fun s => s.RIP = 0x100fa6) (xorR64R64Effect 0x100fa6 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[107, 133]
    (.letOp (n := 151) (.out 0x100fa9 (movR64R64Effect 0x100fa9 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[149]
    (.letOp (n := 152) (.exec 0x100fa9 (fun s => s.RIP = 0x100fa9) (movR64R64Effect 0x100fa9 6 15) (Reg.operands [.gpr 15] [])) #v[149]
    (.letOp (n := 153) (.out 0x100fac (xorR64R64Effect 0x100fac 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[151, 61]
    (.letOp (n := 154) (.exec 0x100fac (fun s => s.RIP = 0x100fac) (xorR64R64Effect 0x100fac 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[151, 61]
    (.letOp (n := 155) (.exec 0x100faf (StorePre 0x100faf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100faf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100faf 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[153, 4]
    (.letOp (n := 156) (.out 0x100fb4 (movR64R64Effect 0x100fb4 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[139]
    (.letOp (n := 157) (.exec 0x100fb4 (fun s => s.RIP = 0x100fb4) (movR64R64Effect 0x100fb4 10 11) (Reg.operands [.gpr 11] [])) #v[139]
    (.letOp (n := 158) (.out 0x100fb7 (andR64R64Effect 0x100fb7 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[156, 153]
    (.letOp (n := 159) (.exec 0x100fb7 (fun s => s.RIP = 0x100fb7) (andR64R64Effect 0x100fb7 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[156, 153]
    (.letOp (n := 160) (.out 0x100fba (xorR64R64Effect 0x100fba 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[158, 61]
    (.letOp (n := 161) (.exec 0x100fba (fun s => s.RIP = 0x100fba) (xorR64R64Effect 0x100fba 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[158, 61]
    (b_l100eed_3)))))))))))))))))))))))))))))))))))))

def bytes_l100eed_2 : List UInt8 :=
  [0x4C, 0x89, 0xC1, 0x4C, 0x21, 0xD1, 0x4D, 0x89, 0xD4, 0x48, 0x31, 0xF1, 0x4C, 0x8B, 0x2F, 0x48,
    0x89, 0xDE, 0x4C, 0x31, 0xEE, 0x49, 0x89, 0xF3, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x89, 0xDE,
    0x4C, 0x31, 0xFE, 0x48, 0x89, 0xF3, 0x48, 0x89, 0x34, 0x24, 0x4D, 0x31, 0xEF, 0x4C, 0x89, 0xFE,
    0x48, 0x31, 0xC6, 0x48, 0x89, 0x74, 0x24, 0x30, 0x4D, 0x89, 0xDA, 0x49, 0x21, 0xF2, 0x49, 0x31,
    0xC2] ++ bytes_l100eed_3

theorem code_l100eed_2 : ∀ x ∈ codeRange 0x100f7c bytes_l100eed_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf7c 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_3

@[cfg_block] def b_l100eed_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x100f37 (xorR64R64Effect 0x100f37 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[83, 59]
    (.letOp (n := 90) (.exec 0x100f37 (fun s => s.RIP = 0x100f37) (xorR64R64Effect 0x100f37 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[83, 59]
    (.letOp (n := 91) (.out 0x100f3a (movR64R64Effect 0x100f3a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 92) (.exec 0x100f3a (fun s => s.RIP = 0x100f3a) (movR64R64Effect 0x100f3a 1 0) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 93) (.out 0x100f3d (xorR64R64Effect 0x100f3d 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[91, 65]
    (.letOp (n := 94) (.exec 0x100f3d (fun s => s.RIP = 0x100f3d) (xorR64R64Effect 0x100f3d 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[91, 65]
    (.letOp (n := 95) (.exec 0x100f40 (StorePre 0x100f40 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100f40 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f40 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 96) (.out 0x100f45 (movR64R64Effect 0x100f45 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[89]
    (.letOp (n := 97) (.exec 0x100f45 (fun s => s.RIP = 0x100f45) (movR64R64Effect 0x100f45 8 9) (Reg.operands [.gpr 9] [])) #v[89]
    (.letOp (n := 98) (.out 0x100f48 (xorR64R64Effect 0x100f48 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[96, 93]
    (.letOp (n := 99) (.exec 0x100f48 (fun s => s.RIP = 0x100f48) (xorR64R64Effect 0x100f48 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[96, 93]
    (.letOp (n := 100) (.out 0x100f4b (movR64R64Effect 0x100f4b 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[98]
    (.letOp (n := 101) (.exec 0x100f4b (fun s => s.RIP = 0x100f4b) (movR64R64Effect 0x100f4b 6 8) (Reg.operands [.gpr 8] [])) #v[98]
    (.letOp (n := 102) (.out 0x100f4e (movR64R64Effect 0x100f4e 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[98]
    (.letOp (n := 103) (.exec 0x100f4e (fun s => s.RIP = 0x100f4e) (movR64R64Effect 0x100f4e 3 8) (Reg.operands [.gpr 8] [])) #v[98]
    (.letOp (n := 104) (.exec 0x100f51 (StorePre 0x100f51 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100f51 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f51 8 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 105) (.out 0x100f56 (andR64R64Effect 0x100f56 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[100, 93]
    (.letOp (n := 106) (.exec 0x100f56 (fun s => s.RIP = 0x100f56) (andR64R64Effect 0x100f56 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[100, 93]
    (.letOp (n := 107) (.out 0x100f59 (xorR64M64Effect 0x100f59 15 (.base 7 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[59, 7]
    (.letOp (n := 108) (.exec 0x100f59 (LoadPre 0x100f59 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100f59 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x100f59 15 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[59, 7]
    (.letOp (n := 109) (.out 0x100f5d (xorR64R64Effect 0x100f5d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[55, 61]
    (.letOp (n := 110) (.exec 0x100f5d (fun s => s.RIP = 0x100f5d) (xorR64R64Effect 0x100f5d 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 61]
    (.letOp (n := 111) (.out 0x100f60 (movR64R64Effect 0x100f60 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[87]
    (.letOp (n := 112) (.exec 0x100f60 (fun s => s.RIP = 0x100f60) (movR64R64Effect 0x100f60 8 14) (Reg.operands [.gpr 14] [])) #v[87]
    (.letOp (n := 113) (.exec 0x100f63 (StorePre 0x100f63 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100f63 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f63 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 114) (.out 0x100f68 (xorR64R64Effect 0x100f68 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[111, 107]
    (.letOp (n := 115) (.exec 0x100f68 (fun s => s.RIP = 0x100f68) (xorR64R64Effect 0x100f68 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[111, 107]
    (.letOp (n := 116) (.out 0x100f6b (movR64R64Effect 0x100f6b 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[102]
    (.letOp (n := 117) (.exec 0x100f6b (fun s => s.RIP = 0x100f6b) (movR64R64Effect 0x100f6b 2 3) (Reg.operands [.gpr 3] [])) #v[102]
    (.letOp (n := 118) (.out 0x100f6e (xorR64R64Effect 0x100f6e 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[116, 114]
    (.letOp (n := 119) (.exec 0x100f6e (fun s => s.RIP = 0x100f6e) (xorR64R64Effect 0x100f6e 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[116, 114]
    (.letOp (n := 120) (.exec 0x100f71 (StorePre 0x100f71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100f71 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f71 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[118, 4]
    (.letOp (n := 121) (.out 0x100f76 (andR64R64Effect 0x100f76 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[118, 78]
    (.letOp (n := 122) (.exec 0x100f76 (fun s => s.RIP = 0x100f76) (andR64R64Effect 0x100f76 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[118, 78]
    (.letOp (n := 123) (.out 0x100f79 (xorR64R64Effect 0x100f79 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[121, 105]
    (.letOp (n := 124) (.exec 0x100f79 (fun s => s.RIP = 0x100f79) (xorR64R64Effect 0x100f79 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[121, 105]
    (b_l100eed_2))))))))))))))))))))))))))))))))))))

def bytes_l100eed_1 : List UInt8 :=
  [0x4D, 0x31, 0xF9, 0x48, 0x89, 0xC1, 0x4C, 0x31, 0xC1, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x4D, 0x89,
    0xC8, 0x49, 0x31, 0xC8, 0x4C, 0x89, 0xC6, 0x4C, 0x89, 0xC3, 0x4C, 0x89, 0x44, 0x24, 0x48, 0x48,
    0x21, 0xCE, 0x4C, 0x33, 0x7F, 0x28, 0x49, 0x31, 0xC2, 0x4D, 0x89, 0xF0, 0x4C, 0x89, 0x74, 0x24,
    0x18, 0x4D, 0x31, 0xF8, 0x48, 0x89, 0xDA, 0x4C, 0x31, 0xC2, 0x48, 0x89, 0x54, 0x24, 0x50, 0x4C,
    0x21, 0xDA, 0x48, 0x31, 0xF2] ++ bytes_l100eed_2

theorem code_l100eed_1 : ∀ x ∈ codeRange 0x100f37 bytes_l100eed_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf37 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_2

@[cfg_block] def b_l100eed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100eed (movR64M64Effect 0x100eed 5 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[7]
    (.letOp (n := 54) (.exec 0x100eed (LoadPre 0x100eed (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100eed + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100eed 5 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x100ef1 (movR64M64Effect 0x100ef1 10 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 56) (.exec 0x100ef1 (LoadPre 0x100ef1 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100ef1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ef1 10 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x100ef5 (movR64M64Effect 0x100ef5 6 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 58) (.exec 0x100ef5 (LoadPre 0x100ef5 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x100ef5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ef5 6 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x100ef9 (movR64M64Effect 0x100ef9 15 (.base 7 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 60) (.exec 0x100ef9 (LoadPre 0x100ef9 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x100ef9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ef9 15 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x100efd (movR64M64Effect 0x100efd 0 (.base 7 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 62) (.exec 0x100efd (LoadPre 0x100efd (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100efd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100efd 0 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x100f01 (movR64R64Effect 0x100f01 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 64) (.exec 0x100f01 (fun s => s.RIP = 0x100f01) (movR64R64Effect 0x100f01 2 6) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 65) (.out 0x100f04 (movR64R64Effect 0x100f04 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 66) (.exec 0x100f04 (fun s => s.RIP = 0x100f04) (movR64R64Effect 0x100f04 8 6) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 67) (.exec 0x100f07 (StorePre 0x100f07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f07 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 68) (.out 0x100f0c (xorR64R64Effect 0x100f0c 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[63, 55]
    (.letOp (n := 69) (.exec 0x100f0c (fun s => s.RIP = 0x100f0c) (xorR64R64Effect 0x100f0c 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[63, 55]
    (.letOp (n := 70) (.out 0x100f0f (movR64R64Effect 0x100f0f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 71) (.exec 0x100f0f (fun s => s.RIP = 0x100f0f) (movR64R64Effect 0x100f0f 6 0) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 72) (.out 0x100f12 (xorR64R64Effect 0x100f12 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[70, 53]
    (.letOp (n := 73) (.exec 0x100f12 (fun s => s.RIP = 0x100f12) (xorR64R64Effect 0x100f12 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[70, 53]
    (.letOp (n := 74) (.exec 0x100f15 (StorePre 0x100f15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100f15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f15 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x100f1a (xorR64R64Effect 0x100f1a 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[72, 68]
    (.letOp (n := 76) (.exec 0x100f1a (fun s => s.RIP = 0x100f1a) (xorR64R64Effect 0x100f1a 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[72, 68]
    (.letOp (n := 77) (.exec 0x100f1d (StorePre 0x100f1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100f1d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f1d 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x100f22 (movR64R64Effect 0x100f22 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[68]
    (.letOp (n := 79) (.exec 0x100f22 (fun s => s.RIP = 0x100f22) (movR64R64Effect 0x100f22 11 2) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 80) (.exec 0x100f25 (StorePre 0x100f25 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100f25 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f25 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 81) (.out 0x100f2a (movR64M64Effect 0x100f2a 9 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 82) (.exec 0x100f2a (LoadPre 0x100f2a (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100f2a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100f2a 9 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 83) (.out 0x100f2e (xorR64R64Effect 0x100f2e 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[81, 75]
    (.letOp (n := 84) (.exec 0x100f2e (fun s => s.RIP = 0x100f2e) (xorR64R64Effect 0x100f2e 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[81, 75]
    (.letOp (n := 85) (.out 0x100f31 (movR64R64Effect 0x100f31 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[83]
    (.letOp (n := 86) (.exec 0x100f31 (fun s => s.RIP = 0x100f31) (movR64R64Effect 0x100f31 14 9) (Reg.operands [.gpr 9] [])) #v[83]
    (.letOp (n := 87) (.out 0x100f34 (xorR64R64Effect 0x100f34 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[85, 55]
    (.letOp (n := 88) (.exec 0x100f34 (fun s => s.RIP = 0x100f34) (xorR64R64Effect 0x100f34 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[85, 55]
    (b_l100eed_1))))))))))))))))))))))))))))))))))))

def bytes_l100eed : List UInt8 :=
  [0x48, 0x8B, 0x6F, 0x08, 0x4C, 0x8B, 0x57, 0x10, 0x48, 0x8B, 0x77, 0x20, 0x4C, 0x8B, 0x7F, 0x30,
    0x48, 0x8B, 0x47, 0x38, 0x48, 0x89, 0xF2, 0x49, 0x89, 0xF0, 0x48, 0x89, 0x74, 0x24, 0x08, 0x4C,
    0x31, 0xD2, 0x48, 0x89, 0xC6, 0x48, 0x31, 0xEE, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x31, 0xD6,
    0x48, 0x89, 0x74, 0x24, 0x28, 0x49, 0x89, 0xD3, 0x48, 0x89, 0x54, 0x24, 0x58, 0x4C, 0x8B, 0x4F,
    0x18, 0x49, 0x31, 0xF1, 0x4D, 0x89, 0xCE, 0x4D, 0x31, 0xD6] ++ bytes_l100eed_1

theorem code_l100eed : ∀ x ∈ codeRange 0x100eed bytes_l100eed, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xeed 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100eed_1

@[cfg_block] def b_l101177 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101177 (xorR32R32Effect 0x101177 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x101177 (fun s => s.RIP = 0x101177) (xorR32R32Effect 0x101177 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x101179 (xorR32R32Effect 0x101179 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x101179 (fun s => s.RIP = 0x101179) (xorR32R32Effect 0x101179 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.out 0x10117b (movR64Imm32Effect 0x10117b 2 0x200e60) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10117b (fun s => s.RIP = 0x10117b) (movR64Imm32Effect 0x10117b 2 0x200e60) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x101182 (callEffect (fun _ => 0x103837) 0x101187) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101182 (PushPre 0x101182 5) (callEffect (fun _ => 0x103837) 0x101187) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101187⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l101187, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101177 : List UInt8 :=
  [0x31, 0xFF, 0x31, 0xF6, 0x48, 0xC7, 0xC2, 0x60, 0x0E, 0x20, 0x00, 0xE8, 0xB0, 0x26, 0x00, 0x00]

theorem code_l101177 : ∀ x ∈ codeRange 0x101177 bytes_l101177, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1177 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101187 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101187 (movR32Imm32Effect 0x101187 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x101187 (fun s => s.RIP = 0x101187) (movR32Imm32Effect 0x101187 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10118c (movR32Imm32Effect 0x10118c 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10118c (fun s => s.RIP = 0x10118c) (movR32Imm32Effect 0x10118c 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x101191 (movR64Imm32Effect 0x101191 2 0x200e78) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x101191 (fun s => s.RIP = 0x101191) (movR64Imm32Effect 0x101191 2 0x200e78) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x101198 (callEffect (fun _ => 0x103837) 0x10119d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101198 (PushPre 0x101198 5) (callEffect (fun _ => 0x103837) 0x10119d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10119d⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10119d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101187 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x78, 0x0E, 0x20,
    0x00, 0xE8, 0x9A, 0x26, 0x00, 0x00]

theorem code_l101187 : ∀ x ∈ codeRange 0x101187 bytes_l101187, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1187 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10119d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10119d (movR32Imm32Effect 0x10119d 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10119d (fun s => s.RIP = 0x10119d) (movR32Imm32Effect 0x10119d 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1011a2 (movR32Imm32Effect 0x1011a2 5 6 0x2) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1011a2 (fun s => s.RIP = 0x1011a2) (movR32Imm32Effect 0x1011a2 5 6 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1011a7 (movR64Imm32Effect 0x1011a7 2 0x200e90) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1011a7 (fun s => s.RIP = 0x1011a7) (movR64Imm32Effect 0x1011a7 2 0x200e90) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1011ae (callEffect (fun _ => 0x103837) 0x1011b3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1011ae (PushPre 0x1011ae 5) (callEffect (fun _ => 0x103837) 0x1011b3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1011b3⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l1011b3, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10119d : List UInt8 :=
  [0xBF, 0x02, 0x00, 0x00, 0x00, 0xBE, 0x02, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x90, 0x0E, 0x20,
    0x00, 0xE8, 0x84, 0x26, 0x00, 0x00]

theorem code_l10119d : ∀ x ∈ codeRange 0x10119d bytes_l10119d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x119d 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1011b3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1011b3 (movR32Imm32Effect 0x1011b3 5 7 0x3) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1011b3 (fun s => s.RIP = 0x1011b3) (movR32Imm32Effect 0x1011b3 5 7 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1011b8 (movR32Imm32Effect 0x1011b8 5 6 0x3) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1011b8 (fun s => s.RIP = 0x1011b8) (movR32Imm32Effect 0x1011b8 5 6 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1011bd (movR64Imm32Effect 0x1011bd 2 0x200ea8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1011bd (fun s => s.RIP = 0x1011bd) (movR64Imm32Effect 0x1011bd 2 0x200ea8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1011c4 (callEffect (fun _ => 0x103837) 0x1011c9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1011c4 (PushPre 0x1011c4 5) (callEffect (fun _ => 0x103837) 0x1011c9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1011c9⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l1011c9, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1011b3 : List UInt8 :=
  [0xBF, 0x03, 0x00, 0x00, 0x00, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xA8, 0x0E, 0x20,
    0x00, 0xE8, 0x6E, 0x26, 0x00, 0x00]

theorem code_l1011b3 : ∀ x ∈ codeRange 0x1011b3 bytes_l1011b3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b3 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1011c9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1011c9 (movR32Imm32Effect 0x1011c9 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1011c9 (fun s => s.RIP = 0x1011c9) (movR32Imm32Effect 0x1011c9 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1011ce (movR32Imm32Effect 0x1011ce 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1011ce (fun s => s.RIP = 0x1011ce) (movR32Imm32Effect 0x1011ce 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1011d3 (movR64Imm32Effect 0x1011d3 2 0x200ec0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1011d3 (fun s => s.RIP = 0x1011d3) (movR64Imm32Effect 0x1011d3 2 0x200ec0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1011da (callEffect (fun _ => 0x103837) 0x1011df) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1011da (PushPre 0x1011da 5) (callEffect (fun _ => 0x103837) 0x1011df) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1011df⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l1011df, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1011c9 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xC0, 0x0E, 0x20,
    0x00, 0xE8, 0x58, 0x26, 0x00, 0x00]

theorem code_l1011c9 : ∀ x ∈ codeRange 0x1011c9 bytes_l1011c9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11c9 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1011df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1011df (movR32Imm32Effect 0x1011df 5 7 0x5) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1011df (fun s => s.RIP = 0x1011df) (movR32Imm32Effect 0x1011df 5 7 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1011e4 (movR32Imm32Effect 0x1011e4 5 6 0x5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1011e4 (fun s => s.RIP = 0x1011e4) (movR32Imm32Effect 0x1011e4 5 6 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1011e9 (movR64Imm32Effect 0x1011e9 2 0x200ed8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1011e9 (fun s => s.RIP = 0x1011e9) (movR64Imm32Effect 0x1011e9 2 0x200ed8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1011f0 (callEffect (fun _ => 0x103837) 0x1011f5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1011f0 (PushPre 0x1011f0 5) (callEffect (fun _ => 0x103837) 0x1011f5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1011f5⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l1011f5, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1011df : List UInt8 :=
  [0xBF, 0x05, 0x00, 0x00, 0x00, 0xBE, 0x05, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xD8, 0x0E, 0x20,
    0x00, 0xE8, 0x42, 0x26, 0x00, 0x00]

theorem code_l1011df : ∀ x ∈ codeRange 0x1011df bytes_l1011df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11df 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1011f5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1011f5 (movR32Imm32Effect 0x1011f5 5 7 0x6) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1011f5 (fun s => s.RIP = 0x1011f5) (movR32Imm32Effect 0x1011f5 5 7 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1011fa (movR32Imm32Effect 0x1011fa 5 6 0x6) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1011fa (fun s => s.RIP = 0x1011fa) (movR32Imm32Effect 0x1011fa 5 6 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1011ff (movR64Imm32Effect 0x1011ff 2 0x200ef0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1011ff (fun s => s.RIP = 0x1011ff) (movR64Imm32Effect 0x1011ff 2 0x200ef0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x101206 (callEffect (fun _ => 0x103837) 0x10120b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101206 (PushPre 0x101206 5) (callEffect (fun _ => 0x103837) 0x10120b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10120b⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10120b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1011f5 : List UInt8 :=
  [0xBF, 0x06, 0x00, 0x00, 0x00, 0xBE, 0x06, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xF0, 0x0E, 0x20,
    0x00, 0xE8, 0x2C, 0x26, 0x00, 0x00]

theorem code_l1011f5 : ∀ x ∈ codeRange 0x1011f5 bytes_l1011f5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11f5 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10120b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10120b (movR32Imm32Effect 0x10120b 5 7 0x7) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10120b (fun s => s.RIP = 0x10120b) (movR32Imm32Effect 0x10120b 5 7 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101210 (movR32Imm32Effect 0x101210 5 6 0x7) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x101210 (fun s => s.RIP = 0x101210) (movR32Imm32Effect 0x101210 5 6 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x101215 (movR64Imm32Effect 0x101215 2 0x200f08) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x101215 (fun s => s.RIP = 0x101215) (movR64Imm32Effect 0x101215 2 0x200f08) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10121c (callEffect (fun _ => 0x103837) 0x101221) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10121c (PushPre 0x10121c 5) (callEffect (fun _ => 0x103837) 0x101221) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101221⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l101221, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10120b : List UInt8 :=
  [0xBF, 0x07, 0x00, 0x00, 0x00, 0xBE, 0x07, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x08, 0x0F, 0x20,
    0x00, 0xE8, 0x16, 0x26, 0x00, 0x00]

theorem code_l10120b : ∀ x ∈ codeRange 0x10120b bytes_l10120b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x120b 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101221 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101221 (fun s => s.RIP = 0x101221) (fun _ => nopEffect 0x101221 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10122b (fun s => s.RIP = 0x10122b) (fun _ => nopEffect 0x10122b 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101230, RegMap.args [] 55⟩)))

def bytes_l101221 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l101221 : ∀ x ∈ codeRange 0x101221 bytes_l101221, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1221 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101230 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l101230, RegMap.args (entryMap (live .l101230)) 53⟩)

def bytes_l101230 : List UInt8 :=
  [0xEB, 0xFE]

theorem code_l101230 : ∀ x ∈ codeRange 0x101230 bytes_l101230, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1230 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101240 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101240 (pushR64Effect 0x101240 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101240 (PushPre 0x101240 1) (pushR64Effect 0x101240 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101241 (pushR64Effect 0x101241 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101241 (PushPre 0x101241 2) (pushR64Effect 0x101241 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101243 (pushR64Effect 0x101243 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101243 (PushPre 0x101243 2) (pushR64Effect 0x101243 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101245 (pushR64Effect 0x101245 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101245 (PushPre 0x101245 2) (pushR64Effect 0x101245 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101247 (pushR64Effect 0x101247 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101247 (PushPre 0x101247 2) (pushR64Effect 0x101247 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101249 (pushR64Effect 0x101249 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101249 (PushPre 0x101249 1) (pushR64Effect 0x101249 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10124a (subR64Imm32Effect 0x10124a 4 0x198) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10124a (fun s => s.RIP = 0x10124a) (subR64Imm32Effect 0x10124a 4 0x198) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101251 (movR64R64Effect 0x101251 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[9]
    (.letOp (n := 68) (.exec 0x101251 (fun s => s.RIP = 0x101251) (movR64R64Effect 0x101251 13 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101254 (movR64R64Effect 0x101254 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[8]
    (.letOp (n := 70) (.exec 0x101254 (fun s => s.RIP = 0x101254) (movR64R64Effect 0x101254 12 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x101257 (movR64R64Effect 0x101257 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 72) (.exec 0x101257 (fun s => s.RIP = 0x101257) (movR64R64Effect 0x101257 3 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x10125a (movR64R64Effect 0x10125a 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 74) (.exec 0x10125a (fun s => s.RIP = 0x10125a) (movR64R64Effect 0x10125a 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x10125d (movR64R64Effect 0x10125d 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 76) (.exec 0x10125d (fun s => s.RIP = 0x10125d) (movR64R64Effect 0x10125d 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x101260 (movR64R64Effect 0x101260 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 78) (.exec 0x101260 (fun s => s.RIP = 0x101260) (movR64R64Effect 0x101260 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x101263 (leaR64Effect 0x101263 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 80) (.exec 0x101263 (fun s => s.RIP = 0x101263) (leaR64Effect 0x101263 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.out 0x101268 (movR64R64Effect 0x101268 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 82) (.exec 0x101268 (fun s => s.RIP = 0x101268) (movR64R64Effect 0x101268 7 5) (Reg.operands [.gpr 5] [])) #v[79]
    (.letOp (n := 83) (.out 0x10126b (callEffect (fun _ => 0x104370) 0x101270) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 84) (.exec 0x10126b (PushPre 0x10126b 5) (callEffect (fun _ => 0x104370) 0x101270) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 85) (.const ⟨64, 0x101270⟩) #v[]
    (.terminate (.call ⟨.l104370, RegMap.args [(1, 1), (2, 2), (3, 71), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l101270, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l101240 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x01, 0x00,
    0x00, 0x4D, 0x89, 0xCD, 0x4D, 0x89, 0xC4, 0x48, 0x89, 0xCB, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xF7,
    0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x10, 0x48, 0x89, 0xEF, 0xE8, 0x00, 0x31, 0x00, 0x00]

theorem code_l101240 : ∀ x ∈ codeRange 0x101240 bytes_l101240, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1240 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101270 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101270 (leaR64Effect 0x101270 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101270 (fun s => s.RIP = 0x101270) (leaR64Effect 0x101270 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101278 (movR64R64Effect 0x101278 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x101278 (fun s => s.RIP = 0x101278) (movR64R64Effect 0x101278 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x10127b (callEffect (fun _ => 0x102040) 0x101280) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10127b (PushPre 0x10127b 5) (callEffect (fun _ => 0x102040) 0x101280) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x101280⟩) #v[]
    (.terminate (.call ⟨.l102040, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l101280, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l101270 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEE, 0xE8, 0xC0, 0x0D, 0x00, 0x00]

theorem code_l101270 : ∀ x ∈ codeRange 0x101270 bytes_l101270, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1270 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101280 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101280 (movR32Imm32Effect 0x101280 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101280 (fun s => s.RIP = 0x101280) (movR32Imm32Effect 0x101280 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101285 (cmpR64Imm8Effect 0x101285 13 0x10) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 56) (.exec 0x101285 (fun s => s.RIP = 0x101285) (cmpR64Imm8Effect 0x101285 13 0x10) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.pure (condOp 2)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1012d2, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10128b, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l101280 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFD, 0x10, 0x72, 0x47]

theorem code_l101280 : ∀ x ∈ codeRange 0x101280 bytes_l101280, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1280 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10128b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10128b (leaR64Effect 0x10128b 0 (.base 13 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x10128b (fun s => s.RIP = 0x10128b) (leaR64Effect 0x10128b 0 (.base 13 (.d8 0xf0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x10128f (movR64M64Effect 0x10128f 1 (.sib 12 (some 13) 0 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12, .gpr 13] []) (.reg (.gpr 1))) #v[12, 13]
    (.letOp (n := 56) (.exec 0x10128f (LoadPre 0x10128f (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf0)) s (0x10128f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10128f 1 (.sib 12 (some 13) 0 (.d8 0xf0))) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 13]
    (.letOp (n := 57) (.out 0x101294 (movR64M64Effect 0x101294 2 (.sib 12 (some 13) 0 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 13] []) (.reg (.gpr 2))) #v[12, 13]
    (.letOp (n := 58) (.exec 0x101294 (LoadPre 0x101294 (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf8)) s (0x101294 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101294 2 (.sib 12 (some 13) 0 (.d8 0xf8))) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 13]
    (.letOp (n := 59) (.exec 0x101299 (StorePre 0x101299 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101299 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101299 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x10129e (StorePre 0x10129e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10129e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10129e 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.exec 0x1012a2 (StorePre 0x1012a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1012a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012a2 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 62) (.exec 0x1012a7 (StorePre 0x1012a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1012a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012a7 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 63) (.exec 0x1012ac (StorePre 0x1012ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1012ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012ac 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.out 0x1012b1 (leaR64Effect 0x1012b1 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 65) (.exec 0x1012b1 (fun s => s.RIP = 0x1012b1) (leaR64Effect 0x1012b1 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1012b9 (leaR64Effect 0x1012b9 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 67) (.exec 0x1012b9 (fun s => s.RIP = 0x1012b9) (leaR64Effect 0x1012b9 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1012be (movR64R64Effect 0x1012be 9 4) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 69) (.exec 0x1012be (fun s => s.RIP = 0x1012be) (movR64R64Effect 0x1012be 9 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1012c1 (movR64R64Effect 0x1012c1 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 71) (.exec 0x1012c1 (fun s => s.RIP = 0x1012c1) (movR64R64Effect 0x1012c1 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 72) (.out 0x1012c4 (movR64R64Effect 0x1012c4 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 73) (.exec 0x1012c4 (fun s => s.RIP = 0x1012c4) (movR64R64Effect 0x1012c4 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 74) (.out 0x1012c7 (movR64R64Effect 0x1012c7 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 75) (.exec 0x1012c7 (fun s => s.RIP = 0x1012c7) (movR64R64Effect 0x1012c7 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 76) (.out 0x1012ca (callEffect (fun _ => 0x1022c0) 0x1012cf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x1012ca (PushPre 0x1012ca 5) (callEffect (fun _ => 0x1022c0) 0x1012cf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.const ⟨64, 0x1012cf⟩) #v[]
    (.terminate (.call ⟨.l1022c0, RegMap.args [(0, 53), (1, 74), (2, 72), (3, 3), (4, 76), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l1012cf, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l10128b : List UInt8 :=
  [0x49, 0x8D, 0x45, 0xF0, 0x4B, 0x8B, 0x4C, 0x2C, 0xF0, 0x4B, 0x8B, 0x54, 0x2C, 0xF8, 0x48, 0x89,
    0x54, 0x24, 0x08, 0x48, 0x89, 0x0C, 0x24, 0x4C, 0x89, 0x64, 0x24, 0x10, 0x4C, 0x89, 0x64, 0x24,
    0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x8D,
    0x44, 0x24, 0x10, 0x49, 0x89, 0xE1, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0x48, 0x89, 0xD9, 0xE8,
    0xF1, 0x0F, 0x00, 0x00]

theorem code_l10128b : ∀ x ∈ codeRange 0x10128b bytes_l10128b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x128b 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1012cf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1012cf (movzxR32R8Effect 0x1012cf 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1012cf (fun s => s.RIP = 0x1012cf) (movzxR32R8Effect 0x1012cf 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l1012d2, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1012cf : List UInt8 :=
  [0x0F, 0xB6, 0xC0]

theorem code_l1012cf : ∀ x ∈ codeRange 0x1012cf bytes_l1012cf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12cf 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1012d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1012d2 (addR64Imm32Effect 0x1012d2 4 0x198) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1012d2 (fun s => s.RIP = 0x1012d2) (addR64Imm32Effect 0x1012d2 4 0x198) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1012d9 (popR64Effect 0x1012d9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1012d9 (popR64Effect 0x1012d9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1012d9 (PopPre 0x1012d9) (popR64Effect 0x1012d9 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1012da (popR64Effect 0x1012da 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x1012da (popR64Effect 0x1012da 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1012da (PopPre 0x1012da) (popR64Effect 0x1012da 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1012dc (popR64Effect 0x1012dc 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x1012dc (popR64Effect 0x1012dc 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1012dc (PopPre 0x1012dc) (popR64Effect 0x1012dc 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1012de (popR64Effect 0x1012de 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1012de (popR64Effect 0x1012de 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1012de (PopPre 0x1012de) (popR64Effect 0x1012de 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1012e0 (popR64Effect 0x1012e0 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1012e0 (popR64Effect 0x1012e0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1012e0 (PopPre 0x1012e0) (popR64Effect 0x1012e0 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1012e2 (popR64Effect 0x1012e2 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1012e2 (popR64Effect 0x1012e2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1012e2 (PopPre 0x1012e2) (popR64Effect 0x1012e2 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1012e3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1012e3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1012e3 (RetPre 0x1012e3) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l1012d2 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x98, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1012d2 : ∀ x ∈ codeRange 0x1012d2 bytes_l1012d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12d2 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1012f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1012f0 (pushR64Effect 0x1012f0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1012f0 (PushPre 0x1012f0 1) (pushR64Effect 0x1012f0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1012f1 (pushR64Effect 0x1012f1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1012f1 (PushPre 0x1012f1 2) (pushR64Effect 0x1012f1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1012f3 (pushR64Effect 0x1012f3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1012f3 (PushPre 0x1012f3 2) (pushR64Effect 0x1012f3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1012f5 (pushR64Effect 0x1012f5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1012f5 (PushPre 0x1012f5 2) (pushR64Effect 0x1012f5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1012f7 (pushR64Effect 0x1012f7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1012f7 (PushPre 0x1012f7 2) (pushR64Effect 0x1012f7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1012f9 (pushR64Effect 0x1012f9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1012f9 (PushPre 0x1012f9 1) (pushR64Effect 0x1012f9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1012fa (subR64Imm32Effect 0x1012fa 4 0x198) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1012fa (fun s => s.RIP = 0x1012fa) (subR64Imm32Effect 0x1012fa 4 0x198) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101301 (movR64R64Effect 0x101301 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 68) (.exec 0x101301 (fun s => s.RIP = 0x101301) (movR64R64Effect 0x101301 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101304 (movR64R64Effect 0x101304 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 70) (.exec 0x101304 (fun s => s.RIP = 0x101304) (movR64R64Effect 0x101304 14 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.exec 0x101307 (StorePre 0x101307 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101307 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101307 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 72) (.out 0x10130c (movR64R64Effect 0x10130c 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 73) (.exec 0x10130c (fun s => s.RIP = 0x10130c) (movR64R64Effect 0x10130c 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.out 0x10130f (movR64R64Effect 0x10130f 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 75) (.exec 0x10130f (fun s => s.RIP = 0x10130f) (movR64R64Effect 0x10130f 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x101312 (movR64R64Effect 0x101312 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 77) (.exec 0x101312 (fun s => s.RIP = 0x101312) (movR64R64Effect 0x101312 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x101315 (leaR64Effect 0x101315 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 79) (.exec 0x101315 (fun s => s.RIP = 0x101315) (leaR64Effect 0x101315 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.out 0x10131a (movR64R64Effect 0x10131a 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x10131a (fun s => s.RIP = 0x10131a) (movR64R64Effect 0x10131a 7 5) (Reg.operands [.gpr 5] [])) #v[78]
    (.letOp (n := 82) (.out 0x10131d (callEffect (fun _ => 0x104370) 0x101322) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 83) (.exec 0x10131d (PushPre 0x10131d 5) (callEffect (fun _ => 0x104370) 0x101322) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 84) (.const ⟨64, 0x101322⟩) #v[]
    (.terminate (.call ⟨.l104370, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l101322, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l1012f0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xCB, 0x4D, 0x89, 0xC6, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x49, 0x89, 0xD4, 0x49,
    0x89, 0xF5, 0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x10, 0x48, 0x89, 0xEF, 0xE8, 0x4E, 0x30,
    0x00, 0x00]

theorem code_l1012f0 : ∀ x ∈ codeRange 0x1012f0 bytes_l1012f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12f0 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101322 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101322 (leaR64Effect 0x101322 15 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x101322 (fun s => s.RIP = 0x101322) (leaR64Effect 0x101322 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10132a (movR64R64Effect 0x10132a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10132a (fun s => s.RIP = 0x10132a) (movR64R64Effect 0x10132a 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x10132d (movR64R64Effect 0x10132d 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x10132d (fun s => s.RIP = 0x10132d) (movR64R64Effect 0x10132d 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x101330 (callEffect (fun _ => 0x102040) 0x101335) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101330 (PushPre 0x101330 5) (callEffect (fun _ => 0x102040) 0x101335) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101335⟩) #v[]
    (.terminate (.call ⟨.l102040, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101335, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101322 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xE8, 0x0B,
    0x0D, 0x00, 0x00]

theorem code_l101322 : ∀ x ∈ codeRange 0x101322 bytes_l101322, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1322 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101335 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101335 (StorePre 0x101335 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101335 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101335 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.out 0x10133a (movR64M64Effect 0x10133a 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x10133a (LoadPre 0x10133a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10133a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10133a 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x101342 (addR64R64Effect 0x101342 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 54]
    (.letOp (n := 57) (.exec 0x101342 (fun s => s.RIP = 0x101342) (addR64R64Effect 0x101342 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 54]
    (.letOp (n := 58) (.exec 0x101345 (StorePre 0x101345 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101345 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101345 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 59) (.exec 0x10134a (StorePre 0x10134a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10134a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10134a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 60) (.out 0x10134f (leaR64Effect 0x10134f 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 61) (.exec 0x10134f (fun s => s.RIP = 0x10134f) (leaR64Effect 0x10134f 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x101354 (movR64R64Effect 0x101354 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 63) (.exec 0x101354 (fun s => s.RIP = 0x101354) (movR64R64Effect 0x101354 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x101357 (movR64R64Effect 0x101357 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 65) (.exec 0x101357 (fun s => s.RIP = 0x101357) (movR64R64Effect 0x101357 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x10135a (movR64R64Effect 0x10135a 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 67) (.exec 0x10135a (fun s => s.RIP = 0x10135a) (movR64R64Effect 0x10135a 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 68) (.out 0x10135d (movR64M64Effect 0x10135d 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x10135d (LoadPre 0x10135d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10135d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10135d 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x101362 (movR64R64Effect 0x101362 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[56]
    (.letOp (n := 71) (.exec 0x101362 (fun s => s.RIP = 0x101362) (movR64R64Effect 0x101362 9 14) (Reg.operands [.gpr 14] [])) #v[56]
    (.letOp (n := 72) (.out 0x101365 (callEffect (fun _ => 0x1022c0) 0x10136a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x101365 (PushPre 0x101365 5) (callEffect (fun _ => 0x1022c0) 0x10136a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x10136a⟩) #v[]
    (.terminate (.call ⟨.l1022c0, RegMap.args [(0, 54), (1, 68), (2, 66), (3, 3), (4, 72), (5, 5), (6, 64), (7, 62), (8, 60), (9, 70), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l10136a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l101335 : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x49, 0x01, 0xC6,
    0x48, 0x89, 0x5C, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x8D, 0x44, 0x24, 0x10, 0x4C,
    0x89, 0xFF, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xE2, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x4D, 0x89, 0xF1,
    0xE8, 0x56, 0x0F, 0x00, 0x00]

theorem code_l101335 : ∀ x ∈ codeRange 0x101335 bytes_l101335, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1335 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10136a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10136a (movzxR32R8Effect 0x10136a 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10136a (fun s => s.RIP = 0x10136a) (movzxR32R8Effect 0x10136a 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10136d (addR64Imm32Effect 0x10136d 4 0x198) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10136d (fun s => s.RIP = 0x10136d) (addR64Imm32Effect 0x10136d 4 0x198) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101374 (popR64Effect 0x101374 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x101374 (popR64Effect 0x101374 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x101374 (PopPre 0x101374) (popR64Effect 0x101374 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x101375 (popR64Effect 0x101375 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x101375 (popR64Effect 0x101375 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x101375 (PopPre 0x101375) (popR64Effect 0x101375 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x101377 (popR64Effect 0x101377 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x101377 (popR64Effect 0x101377 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x101377 (PopPre 0x101377) (popR64Effect 0x101377 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x101379 (popR64Effect 0x101379 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x101379 (popR64Effect 0x101379 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x101379 (PopPre 0x101379) (popR64Effect 0x101379 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10137b (popR64Effect 0x10137b 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10137b (popR64Effect 0x10137b 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10137b (PopPre 0x10137b) (popR64Effect 0x10137b 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10137d (popR64Effect 0x10137d 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x10137d (popR64Effect 0x10137d 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10137d (PopPre 0x10137d) (popR64Effect 0x10137d 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x10137e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x10137e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x10137e (RetPre 0x10137e) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10136a : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x81, 0xC4, 0x98, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10136a : ∀ x ∈ codeRange 0x10136a bytes_l10136a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x136a 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101380 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101380 (pushR64Effect 0x101380 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101380 (PushPre 0x101380 1) (pushR64Effect 0x101380 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101381 (pushR64Effect 0x101381 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101381 (PushPre 0x101381 2) (pushR64Effect 0x101381 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101383 (pushR64Effect 0x101383 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101383 (PushPre 0x101383 2) (pushR64Effect 0x101383 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101385 (pushR64Effect 0x101385 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101385 (PushPre 0x101385 2) (pushR64Effect 0x101385 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101387 (pushR64Effect 0x101387 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101387 (PushPre 0x101387 2) (pushR64Effect 0x101387 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101389 (pushR64Effect 0x101389 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101389 (PushPre 0x101389 1) (pushR64Effect 0x101389 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10138a (subR64Imm32Effect 0x10138a 4 0x1a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10138a (fun s => s.RIP = 0x10138a) (subR64Imm32Effect 0x10138a 4 0x1a8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101391 (movR64R64Effect 0x101391 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 68) (.exec 0x101391 (fun s => s.RIP = 0x101391) (movR64R64Effect 0x101391 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101394 (movR64R64Effect 0x101394 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 70) (.exec 0x101394 (fun s => s.RIP = 0x101394) (movR64R64Effect 0x101394 14 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x101397 (movR64R64Effect 0x101397 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 72) (.exec 0x101397 (fun s => s.RIP = 0x101397) (movR64R64Effect 0x101397 15 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x10139a (movR64R64Effect 0x10139a 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 74) (.exec 0x10139a (fun s => s.RIP = 0x10139a) (movR64R64Effect 0x10139a 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x10139d (movR64R64Effect 0x10139d 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 76) (.exec 0x10139d (fun s => s.RIP = 0x10139d) (movR64R64Effect 0x10139d 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x1013a0 (movR64R64Effect 0x1013a0 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 78) (.exec 0x1013a0 (fun s => s.RIP = 0x1013a0) (movR64R64Effect 0x1013a0 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x1013a3 (leaR64Effect 0x1013a3 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 80) (.exec 0x1013a3 (fun s => s.RIP = 0x1013a3) (leaR64Effect 0x1013a3 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.out 0x1013a8 (movR64R64Effect 0x1013a8 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 82) (.exec 0x1013a8 (fun s => s.RIP = 0x1013a8) (movR64R64Effect 0x1013a8 7 5) (Reg.operands [.gpr 5] [])) #v[79]
    (.letOp (n := 83) (.out 0x1013ab (callEffect (fun _ => 0x104370) 0x1013b0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 84) (.exec 0x1013ab (PushPre 0x1013ab 5) (callEffect (fun _ => 0x104370) 0x1013b0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 85) (.const ⟨64, 0x1013b0⟩) #v[]
    (.terminate (.call ⟨.l104370, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l1013b0, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l101380 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xCB, 0x4D, 0x89, 0xC6, 0x49, 0x89, 0xCF, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xF5,
    0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x20, 0x48, 0x89, 0xEF, 0xE8, 0xC0, 0x2F, 0x00, 0x00]

theorem code_l101380 : ∀ x ∈ codeRange 0x101380 bytes_l101380, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1380 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1013b0 (leaR64Effect 0x1013b0 7 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1013b0 (fun s => s.RIP = 0x1013b0) (leaR64Effect 0x1013b0 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1013b8 (movR64R64Effect 0x1013b8 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x1013b8 (fun s => s.RIP = 0x1013b8) (movR64R64Effect 0x1013b8 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x1013bb (movR64M64Effect 0x1013bb 5 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x1013bb (LoadPre 0x1013bb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x1013bb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013bb 5 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1013c3 (callEffect (fun _ => 0x102040) 0x1013c8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1013c3 (PushPre 0x1013c3 5) (callEffect (fun _ => 0x102040) 0x1013c8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1013c8⟩) #v[]
    (.terminate (.call ⟨.l102040, RegMap.args [(3, 3), (4, 59), (5, 57), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1013c8, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1013b0 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEE, 0x48, 0x8B, 0xAC, 0x24, 0xE0,
    0x01, 0x00, 0x00, 0xE8, 0x78, 0x0C, 0x00, 0x00]

theorem code_l1013b0 : ∀ x ∈ codeRange 0x1013b0 bytes_l1013b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13b0 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013c8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1013c8 (xorR32R32Effect 0x1013c8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1013c8 (fun s => s.RIP = 0x1013c8) (xorR32R32Effect 0x1013c8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x1013ca (cmpR64R64Effect 0x1013ca 3 5) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 5] []) (.flag .CF)) #v[3, 5]
    (.letOp (n := 56) (.out 0x1013ca (cmpR64R64Effect 0x1013ca 3 5) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 5] []) (.flag .ZF)) #v[3, 5]
    (.letOp (n := 57) (.exec 0x1013ca (fun s => s.RIP = 0x1013ca) (cmpR64R64Effect 0x1013ca 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 58) (.out 0x1013cd (atFlags (condHolds 6) (cmovR64R64Effect 0x1013cd 4 0 3)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[53, 3, 55, 56]
    (.letOp (n := 59) (.exec 0x1013cd (fun s => s.RIP = 0x1013cd) (atFlags (condHolds 6) (cmovR64R64Effect 0x1013cd 4 0 3)) (Reg.operands [.gpr 0, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[53, 3, 55, 56]
    (.letOp (n := 60) (.out 0x1013d1 (movR32Imm32Effect 0x1013d1 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x1013d1 (fun s => s.RIP = 0x1013d1) (movR32Imm32Effect 0x1013d1 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1013d6 (atFlags (condHolds 6) (cmovR64R64Effect 0x1013d6 4 1 14)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 1))) #v[60, 14, 55, 56]
    (.letOp (n := 63) (.exec 0x1013d6 (fun s => s.RIP = 0x1013d6) (atFlags (condHolds 6) (cmovR64R64Effect 0x1013d6 4 1 14)) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[60, 14, 55, 56]
    (.letOp (n := 64) (.exec 0x1013da (StorePre 0x1013da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1013da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013da 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1013df (StorePre 0x1013df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1013df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013df 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.exec 0x1013e4 (StorePre 0x1013e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1013e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013e4 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 67) (.out 0x1013e9 (leaR64Effect 0x1013e9 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 68) (.exec 0x1013e9 (fun s => s.RIP = 0x1013e9) (leaR64Effect 0x1013e9 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1013ee (leaR64Effect 0x1013ee 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 70) (.exec 0x1013ee (fun s => s.RIP = 0x1013ee) (leaR64Effect 0x1013ee 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1013f3 (leaR64Effect 0x1013f3 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 72) (.exec 0x1013f3 (fun s => s.RIP = 0x1013f3) (leaR64Effect 0x1013f3 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1013fb (movR64R64Effect 0x1013fb 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 74) (.exec 0x1013fb (fun s => s.RIP = 0x1013fb) (movR64R64Effect 0x1013fb 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 75) (.out 0x1013fe (movR64R64Effect 0x1013fe 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 76) (.exec 0x1013fe (fun s => s.RIP = 0x1013fe) (movR64R64Effect 0x1013fe 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 77) (.out 0x101401 (movR64R64Effect 0x101401 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 78) (.exec 0x101401 (fun s => s.RIP = 0x101401) (movR64R64Effect 0x101401 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 79) (.out 0x101404 (callEffect (fun _ => 0x102520) 0x101409) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x101404 (PushPre 0x101404 5) (callEffect (fun _ => 0x102520) 0x101409) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x101409⟩) #v[]
    (.terminate (.call ⟨.l102520, RegMap.args [(0, 58), (1, 75), (2, 73), (3, 3), (4, 79), (5, 5), (6, 71), (7, 67), (8, 77), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l101409, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1013c8 : List UInt8 :=
  [0x31, 0xC0, 0x48, 0x39, 0xEB, 0x48, 0x0F, 0x46, 0xC3, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x49, 0x0F,
    0x46, 0xCE, 0x48, 0x89, 0x4C, 0x24, 0x20, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24,
    0x30, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0x4C, 0x8D, 0x4C, 0x24, 0x20, 0x48, 0x8D, 0xB4, 0x24, 0xD0,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xEA, 0x4C, 0x89, 0xE1, 0x4D, 0x89, 0xF8, 0xE8, 0x17, 0x11, 0x00,
    0x00]

theorem code_l1013c8 : ∀ x ∈ codeRange 0x1013c8 bytes_l1013c8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13c8 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101409 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101409 (cmpM8Imm8Effect 0x101409 5 (.sib 4 none 0 (.d8 0xf)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101409 (LoadPre 0x101409 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101409 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101409 5 (.sib 4 none 0 (.d8 0xf)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101417, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l101410, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101409 : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x0F, 0x01, 0x75, 0x07]

theorem code_l101409 : ∀ x ∈ codeRange 0x101409 bytes_l101409, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1409 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101410 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101410 (movR32Imm32Effect 0x101410 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101410 (fun s => s.RIP = 0x101410) (movR32Imm32Effect 0x101410 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101459, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l101410 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x42]

theorem code_l101410 : ∀ x ∈ codeRange 0x101410 bytes_l101410, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1410 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101417 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101417 (movR64M64Effect 0x101417 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101417 (LoadPre 0x101417 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101417 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101417 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10141c (movR64M64Effect 0x10141c 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10141c (LoadPre 0x10141c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10141c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10141c 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101421 (StorePre 0x101421 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101421 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101421 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x101426 (StorePre 0x101426 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101426 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101426 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x10142b (movR64R64Effect 0x10142b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 60) (.exec 0x10142b (fun s => s.RIP = 0x10142b) (movR64R64Effect 0x10142b 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x10142e (subR64Imm8Effect 0x10142e 0 0xf0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.out 0x10142e (subR64Imm8Effect 0x10142e 0 0xf0) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 63) (.exec 0x10142e (fun s => s.RIP = 0x10142e) (subR64Imm8Effect 0x10142e 0 0xf0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.out 0x101432 (atFlags (condHolds 3) (setccR8Effect 0x101432 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[55, 62]
    (.letOp (n := 65) (.exec 0x101432 (fun s => s.RIP = 0x101432) (atFlags (condHolds 3) (setccR8Effect 0x101432 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[55, 62]
    (.letOp (n := 66) (.out 0x101435 (cmpR64R64Effect 0x101435 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[61, 5]
    (.letOp (n := 67) (.out 0x101435 (cmpR64R64Effect 0x101435 0 5) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 5] []) (.flag .ZF)) #v[61, 5]
    (.letOp (n := 68) (.exec 0x101435 (fun s => s.RIP = 0x101435) (cmpR64R64Effect 0x101435 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[61, 5]
    (.letOp (n := 69) (.out 0x101438 (atFlags (condHolds 7) (setccR8Effect 0x101438 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[61, 66, 67]
    (.letOp (n := 70) (.exec 0x101438 (fun s => s.RIP = 0x101438) (atFlags (condHolds 7) (setccR8Effect 0x101438 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[61, 66, 67]
    (.letOp (n := 71) (.out 0x10143b (orR8R8Effect 0x10143b 2 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[69, 64]
    (.letOp (n := 72) (.exec 0x10143b (fun s => s.RIP = 0x10143b) (orR8R8Effect 0x10143b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[69, 64]
    (.letOp (n := 73) (.out 0x10143d (movR32Imm32Effect 0x10143d 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 74) (.exec 0x10143d (fun s => s.RIP = 0x10143d) (movR32Imm32Effect 0x10143d 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 75) ⟨.l101459, RegMap.args [(0, 73), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ ⟨.l101444, RegMap.args [(0, 73), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l101417 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48,
    0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xE8, 0xF0, 0x0F, 0x93, 0xC1, 0x48, 0x39,
    0xE8, 0x0F, 0x97, 0xC0, 0x08, 0xC8, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x75, 0x15]

theorem code_l101417 : ∀ x ∈ codeRange 0x101417 bytes_l101417, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1417 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101444 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101444 (movR64M64Effect 0x101444 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101444 (LoadPre 0x101444 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101444 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101444 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101449 (movR64M64Effect 0x101449 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x101449 (LoadPre 0x101449 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101449 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101449 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10144e (StorePre 0x10144e 5 (fun s => AddrMode.addr (.sib 14 (some 3) 0 (.d8 0x8)) s (0x10144e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10144e 1 (.sib 14 (some 3) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14, .gpr 3] [])) #v[55, 14, 3]
    (.letOp (n := 58) (.exec 0x101453 (StorePre 0x101453 4 (fun s => AddrMode.addr (.sib 14 (some 3) 0 .none) s (0x101453 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101453 0 (.sib 14 (some 3) 0 .none)) (Reg.operands [.gpr 0, .gpr 14, .gpr 3] [])) #v[53, 14, 3]
    (.letOp (n := 59) (.out 0x101457 (xorR32R32Effect 0x101457 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 60) (.exec 0x101457 (fun s => s.RIP = 0x101457) (xorR32R32Effect 0x101457 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.terminate (.br ⟨.l101459, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l101444 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x49, 0x89, 0x4C, 0x1E, 0x08, 0x49,
    0x89, 0x04, 0x1E, 0x31, 0xC0]

theorem code_l101444 : ∀ x ∈ codeRange 0x101444 bytes_l101444, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1444 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101459 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101459 (addR64Imm32Effect 0x101459 4 0x1a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x101459 (fun s => s.RIP = 0x101459) (addR64Imm32Effect 0x101459 4 0x1a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101460 (popR64Effect 0x101460 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x101460 (popR64Effect 0x101460 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x101460 (PopPre 0x101460) (popR64Effect 0x101460 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x101461 (popR64Effect 0x101461 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x101461 (popR64Effect 0x101461 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x101461 (PopPre 0x101461) (popR64Effect 0x101461 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x101463 (popR64Effect 0x101463 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x101463 (popR64Effect 0x101463 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x101463 (PopPre 0x101463) (popR64Effect 0x101463 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x101465 (popR64Effect 0x101465 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x101465 (popR64Effect 0x101465 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x101465 (PopPre 0x101465) (popR64Effect 0x101465 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x101467 (popR64Effect 0x101467 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x101467 (popR64Effect 0x101467 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x101467 (PopPre 0x101467) (popR64Effect 0x101467 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x101469 (popR64Effect 0x101469 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x101469 (popR64Effect 0x101469 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x101469 (PopPre 0x101469) (popR64Effect 0x101469 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x10146a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x10146a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x10146a (RetPre 0x10146a) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l101459 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xA8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l101459 : ∀ x ∈ codeRange 0x101459 bytes_l101459, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1459 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101470 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101470 (pushR64Effect 0x101470 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101470 (PushPre 0x101470 1) (pushR64Effect 0x101470 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101471 (pushR64Effect 0x101471 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101471 (PushPre 0x101471 2) (pushR64Effect 0x101471 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101473 (pushR64Effect 0x101473 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101473 (PushPre 0x101473 2) (pushR64Effect 0x101473 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101475 (pushR64Effect 0x101475 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101475 (PushPre 0x101475 2) (pushR64Effect 0x101475 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101477 (pushR64Effect 0x101477 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101477 (PushPre 0x101477 2) (pushR64Effect 0x101477 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101479 (pushR64Effect 0x101479 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101479 (PushPre 0x101479 1) (pushR64Effect 0x101479 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10147a (subR64Imm32Effect 0x10147a 4 0x1a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10147a (fun s => s.RIP = 0x10147a) (subR64Imm32Effect 0x10147a 4 0x1a8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101481 (movR64R64Effect 0x101481 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 68) (.exec 0x101481 (fun s => s.RIP = 0x101481) (movR64R64Effect 0x101481 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101484 (movR64R64Effect 0x101484 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 70) (.exec 0x101484 (fun s => s.RIP = 0x101484) (movR64R64Effect 0x101484 14 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.exec 0x101487 (StorePre 0x101487 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101487 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101487 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 72) (.out 0x10148b (movR64R64Effect 0x10148b 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 73) (.exec 0x10148b (fun s => s.RIP = 0x10148b) (movR64R64Effect 0x10148b 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.out 0x10148e (movR64R64Effect 0x10148e 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 75) (.exec 0x10148e (fun s => s.RIP = 0x10148e) (movR64R64Effect 0x10148e 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x101491 (movR64R64Effect 0x101491 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 77) (.exec 0x101491 (fun s => s.RIP = 0x101491) (movR64R64Effect 0x101491 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x101494 (leaR64Effect 0x101494 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 79) (.exec 0x101494 (fun s => s.RIP = 0x101494) (leaR64Effect 0x101494 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.out 0x101499 (movR64R64Effect 0x101499 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x101499 (fun s => s.RIP = 0x101499) (movR64R64Effect 0x101499 7 5) (Reg.operands [.gpr 5] [])) #v[78]
    (.letOp (n := 82) (.out 0x10149c (callEffect (fun _ => 0x104370) 0x1014a1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 83) (.exec 0x10149c (PushPre 0x10149c 5) (callEffect (fun _ => 0x104370) 0x1014a1) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 84) (.const ⟨64, 0x1014a1⟩) #v[]
    (.terminate (.call ⟨.l104370, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l1014a1, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l101470 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xCB, 0x4D, 0x89, 0xC6, 0x48, 0x89, 0x0C, 0x24, 0x49, 0x89, 0xD4, 0x49, 0x89,
    0xF5, 0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x20, 0x48, 0x89, 0xEF, 0xE8, 0xCF, 0x2E, 0x00,
    0x00]

theorem code_l101470 : ∀ x ∈ codeRange 0x101470 bytes_l101470, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1470 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014a1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014a1 (leaR64Effect 0x1014a1 15 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x1014a1 (fun s => s.RIP = 0x1014a1) (leaR64Effect 0x1014a1 15 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1014a9 (movR64R64Effect 0x1014a9 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1014a9 (fun s => s.RIP = 0x1014a9) (movR64R64Effect 0x1014a9 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x1014ac (movR64R64Effect 0x1014ac 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x1014ac (fun s => s.RIP = 0x1014ac) (movR64R64Effect 0x1014ac 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x1014af (callEffect (fun _ => 0x102040) 0x1014b4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1014af (PushPre 0x1014af 5) (callEffect (fun _ => 0x102040) 0x1014b4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1014b4⟩) #v[]
    (.terminate (.call ⟨.l102040, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1014b4, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1014a1 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xE8, 0x8C,
    0x0B, 0x00, 0x00]

theorem code_l1014a1 : ∀ x ∈ codeRange 0x1014a1 bytes_l1014a1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14a1 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1014b4 (StorePre 0x1014b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1014b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014b4 14 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.out 0x1014b9 (movR64M64Effect 0x1014b9 14 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 55) (.exec 0x1014b9 (LoadPre 0x1014b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x1014b9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1014b9 14 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1014c1 (StorePre 0x1014c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1014c1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014c1 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 57) (.exec 0x1014c6 (StorePre 0x1014c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1014c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014c6 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x1014cb (leaR64Effect 0x1014cb 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 59) (.exec 0x1014cb (fun s => s.RIP = 0x1014cb) (leaR64Effect 0x1014cb 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1014d0 (leaR64Effect 0x1014d0 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 61) (.exec 0x1014d0 (fun s => s.RIP = 0x1014d0) (leaR64Effect 0x1014d0 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1014d5 (movR64R64Effect 0x1014d5 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x1014d5 (fun s => s.RIP = 0x1014d5) (movR64R64Effect 0x1014d5 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x1014d8 (movR64R64Effect 0x1014d8 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 65) (.exec 0x1014d8 (fun s => s.RIP = 0x1014d8) (movR64R64Effect 0x1014d8 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x1014db (movR64R64Effect 0x1014db 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 67) (.exec 0x1014db (fun s => s.RIP = 0x1014db) (movR64R64Effect 0x1014db 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 68) (.out 0x1014de (movR64M64Effect 0x1014de 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x1014de (LoadPre 0x1014de (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1014de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1014de 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1014e2 (callEffect (fun _ => 0x102520) 0x1014e7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 71) (.exec 0x1014e2 (PushPre 0x1014e2 5) (callEffect (fun _ => 0x102520) 0x1014e7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.const ⟨64, 0x1014e7⟩) #v[]
    (.terminate (.call ⟨.l102520, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 70), (5, 5), (6, 62), (7, 58), (8, 68), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ { target := .l1014e7, kept := #v[], arity := rfl, guard := some (Fin.last 72) })))))))))))))))))))))

def bytes_l1014b4 : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x20, 0x4C, 0x8B, 0xB4, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x5C,
    0x24, 0x28, 0x4C, 0x89, 0x74, 0x24, 0x30, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0x4C, 0x8D, 0x4C, 0x24,
    0x20, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xEA, 0x4C, 0x89, 0xE1, 0x4C, 0x8B, 0x04, 0x24, 0xE8, 0x39,
    0x10, 0x00, 0x00]

theorem code_l1014b4 : ∀ x ∈ codeRange 0x1014b4 bytes_l1014b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14b4 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014e7 (movR32Imm32Effect 0x1014e7 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1014e7 (fun s => s.RIP = 0x1014e7) (movR32Imm32Effect 0x1014e7 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1014ec (cmpM8Imm8Effect 0x1014ec 5 (.sib 4 none 0 (.d8 0xf)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 56) (.exec 0x1014ec (LoadPre 0x1014ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1014ec + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1014ec 5 (.sib 4 none 0 (.d8 0xf)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l101508, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1014f3, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1014e7 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0x80, 0x7C, 0x24, 0x0F, 0x00, 0x75, 0x15]

theorem code_l1014e7 : ∀ x ∈ codeRange 0x1014e7 bytes_l1014e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14e7 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014f3 (movR64M64Effect 0x1014f3 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1014f3 (LoadPre 0x1014f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1014f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1014f3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1014f8 (movR64M64Effect 0x1014f8 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1014f8 (LoadPre 0x1014f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1014f8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1014f8 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1014fd (StorePre 0x1014fd 5 (fun s => AddrMode.addr (.sib 3 (some 14) 0 (.d8 0x8)) s (0x1014fd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014fd 1 (.sib 3 (some 14) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3, .gpr 14] [])) #v[55, 3, 14]
    (.letOp (n := 58) (.exec 0x101502 (StorePre 0x101502 4 (fun s => AddrMode.addr (.sib 3 (some 14) 0 .none) s (0x101502 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101502 0 (.sib 3 (some 14) 0 .none)) (Reg.operands [.gpr 0, .gpr 3, .gpr 14] [])) #v[53, 3, 14]
    (.letOp (n := 59) (.out 0x101506 (xorR32R32Effect 0x101506 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 60) (.exec 0x101506 (fun s => s.RIP = 0x101506) (xorR32R32Effect 0x101506 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.terminate (.br ⟨.l101508, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1014f3 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x4A, 0x89, 0x4C, 0x33, 0x08, 0x4A,
    0x89, 0x04, 0x33, 0x31, 0xC0]

theorem code_l1014f3 : ∀ x ∈ codeRange 0x1014f3 bytes_l1014f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14f3 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101508 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101508 (addR64Imm32Effect 0x101508 4 0x1a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x101508 (fun s => s.RIP = 0x101508) (addR64Imm32Effect 0x101508 4 0x1a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10150f (popR64Effect 0x10150f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x10150f (popR64Effect 0x10150f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x10150f (PopPre 0x10150f) (popR64Effect 0x10150f 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x101510 (popR64Effect 0x101510 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x101510 (popR64Effect 0x101510 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x101510 (PopPre 0x101510) (popR64Effect 0x101510 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x101512 (popR64Effect 0x101512 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x101512 (popR64Effect 0x101512 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x101512 (PopPre 0x101512) (popR64Effect 0x101512 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x101514 (popR64Effect 0x101514 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x101514 (popR64Effect 0x101514 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x101514 (PopPre 0x101514) (popR64Effect 0x101514 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x101516 (popR64Effect 0x101516 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x101516 (popR64Effect 0x101516 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x101516 (PopPre 0x101516) (popR64Effect 0x101516 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x101518 (popR64Effect 0x101518 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x101518 (popR64Effect 0x101518 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x101518 (PopPre 0x101518) (popR64Effect 0x101518 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x101519 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x101519 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x101519 (RetPre 0x101519) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l101508 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xA8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l101508 : ∀ x ∈ codeRange 0x101508 bytes_l101508, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1508 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101520 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101520 (pushR64Effect 0x101520 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101520 (PushPre 0x101520 1) (pushR64Effect 0x101520 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101521 (pushR64Effect 0x101521 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101521 (PushPre 0x101521 2) (pushR64Effect 0x101521 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101523 (pushR64Effect 0x101523 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101523 (PushPre 0x101523 2) (pushR64Effect 0x101523 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101525 (pushR64Effect 0x101525 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101525 (PushPre 0x101525 2) (pushR64Effect 0x101525 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101527 (pushR64Effect 0x101527 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101527 (PushPre 0x101527 2) (pushR64Effect 0x101527 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101529 (pushR64Effect 0x101529 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101529 (PushPre 0x101529 1) (pushR64Effect 0x101529 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10152a (subR64Imm32Effect 0x10152a 4 0x218) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10152a (fun s => s.RIP = 0x10152a) (subR64Imm32Effect 0x10152a 4 0x218) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101531 (movR64R64Effect 0x101531 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[9]
    (.letOp (n := 68) (.exec 0x101531 (fun s => s.RIP = 0x101531) (movR64R64Effect 0x101531 13 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101534 (movR64R64Effect 0x101534 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[8]
    (.letOp (n := 70) (.exec 0x101534 (fun s => s.RIP = 0x101534) (movR64R64Effect 0x101534 12 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x101537 (movR64R64Effect 0x101537 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 72) (.exec 0x101537 (fun s => s.RIP = 0x101537) (movR64R64Effect 0x101537 3 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x10153a (movR64R64Effect 0x10153a 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 74) (.exec 0x10153a (fun s => s.RIP = 0x10153a) (movR64R64Effect 0x10153a 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x10153d (movR64R64Effect 0x10153d 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 76) (.exec 0x10153d (fun s => s.RIP = 0x10153d) (movR64R64Effect 0x10153d 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x101540 (movR64R64Effect 0x101540 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 78) (.exec 0x101540 (fun s => s.RIP = 0x101540) (movR64R64Effect 0x101540 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x101543 (leaR64Effect 0x101543 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 80) (.exec 0x101543 (fun s => s.RIP = 0x101543) (leaR64Effect 0x101543 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.out 0x101548 (movR64R64Effect 0x101548 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 82) (.exec 0x101548 (fun s => s.RIP = 0x101548) (movR64R64Effect 0x101548 7 5) (Reg.operands [.gpr 5] [])) #v[79]
    (.letOp (n := 83) (.out 0x10154b (callEffect (fun _ => 0x1057c0) 0x101550) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 84) (.exec 0x10154b (PushPre 0x10154b 5) (callEffect (fun _ => 0x1057c0) 0x101550) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 85) (.const ⟨64, 0x101550⟩) #v[]
    (.terminate (.call ⟨.l1057c0, RegMap.args [(1, 1), (2, 2), (3, 71), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l101550, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l101520 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x18, 0x02, 0x00,
    0x00, 0x4D, 0x89, 0xCD, 0x4D, 0x89, 0xC4, 0x48, 0x89, 0xCB, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xF7,
    0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x10, 0x48, 0x89, 0xEF, 0xE8, 0x70, 0x42, 0x00, 0x00]

theorem code_l101520 : ∀ x ∈ codeRange 0x101520 bytes_l101520, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1520 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101550 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101550 (leaR64Effect 0x101550 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101550 (fun s => s.RIP = 0x101550) (leaR64Effect 0x101550 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101558 (movR64R64Effect 0x101558 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x101558 (fun s => s.RIP = 0x101558) (movR64R64Effect 0x101558 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x10155b (callEffect (fun _ => 0x102180) 0x101560) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10155b (PushPre 0x10155b 5) (callEffect (fun _ => 0x102180) 0x101560) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x101560⟩) #v[]
    (.terminate (.call ⟨.l102180, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l101560, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l101550 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xEE, 0xE8, 0x20, 0x0C, 0x00, 0x00]

theorem code_l101550 : ∀ x ∈ codeRange 0x101550 bytes_l101550, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1550 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101560 (movR32Imm32Effect 0x101560 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101560 (fun s => s.RIP = 0x101560) (movR32Imm32Effect 0x101560 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101565 (cmpR64Imm8Effect 0x101565 13 0x10) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 56) (.exec 0x101565 (fun s => s.RIP = 0x101565) (cmpR64Imm8Effect 0x101565 13 0x10) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.pure (condOp 2)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1015b2, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10156b, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l101560 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFD, 0x10, 0x72, 0x47]

theorem code_l101560 : ∀ x ∈ codeRange 0x101560 bytes_l101560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1560 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10156b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10156b (leaR64Effect 0x10156b 0 (.base 13 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x10156b (fun s => s.RIP = 0x10156b) (leaR64Effect 0x10156b 0 (.base 13 (.d8 0xf0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x10156f (movR64M64Effect 0x10156f 1 (.sib 12 (some 13) 0 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12, .gpr 13] []) (.reg (.gpr 1))) #v[12, 13]
    (.letOp (n := 56) (.exec 0x10156f (LoadPre 0x10156f (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf0)) s (0x10156f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10156f 1 (.sib 12 (some 13) 0 (.d8 0xf0))) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 13]
    (.letOp (n := 57) (.out 0x101574 (movR64M64Effect 0x101574 2 (.sib 12 (some 13) 0 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 13] []) (.reg (.gpr 2))) #v[12, 13]
    (.letOp (n := 58) (.exec 0x101574 (LoadPre 0x101574 (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf8)) s (0x101574 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101574 2 (.sib 12 (some 13) 0 (.d8 0xf8))) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 13]
    (.letOp (n := 59) (.exec 0x101579 (StorePre 0x101579 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101579 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101579 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x10157e (StorePre 0x10157e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10157e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10157e 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.exec 0x101582 (StorePre 0x101582 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101582 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101582 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 62) (.exec 0x101587 (StorePre 0x101587 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101587 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101587 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 63) (.exec 0x10158c (StorePre 0x10158c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10158c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10158c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.out 0x101591 (leaR64Effect 0x101591 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 65) (.exec 0x101591 (fun s => s.RIP = 0x101591) (leaR64Effect 0x101591 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x101599 (leaR64Effect 0x101599 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 67) (.exec 0x101599 (fun s => s.RIP = 0x101599) (leaR64Effect 0x101599 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x10159e (movR64R64Effect 0x10159e 9 4) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 69) (.exec 0x10159e (fun s => s.RIP = 0x10159e) (movR64R64Effect 0x10159e 9 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1015a1 (movR64R64Effect 0x1015a1 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 71) (.exec 0x1015a1 (fun s => s.RIP = 0x1015a1) (movR64R64Effect 0x1015a1 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 72) (.out 0x1015a4 (movR64R64Effect 0x1015a4 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 73) (.exec 0x1015a4 (fun s => s.RIP = 0x1015a4) (movR64R64Effect 0x1015a4 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 74) (.out 0x1015a7 (movR64R64Effect 0x1015a7 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 75) (.exec 0x1015a7 (fun s => s.RIP = 0x1015a7) (movR64R64Effect 0x1015a7 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 76) (.out 0x1015aa (callEffect (fun _ => 0x102720) 0x1015af) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x1015aa (PushPre 0x1015aa 5) (callEffect (fun _ => 0x102720) 0x1015af) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.const ⟨64, 0x1015af⟩) #v[]
    (.terminate (.call ⟨.l102720, RegMap.args [(0, 53), (1, 74), (2, 72), (3, 3), (4, 76), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l1015af, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l10156b : List UInt8 :=
  [0x49, 0x8D, 0x45, 0xF0, 0x4B, 0x8B, 0x4C, 0x2C, 0xF0, 0x4B, 0x8B, 0x54, 0x2C, 0xF8, 0x48, 0x89,
    0x54, 0x24, 0x08, 0x48, 0x89, 0x0C, 0x24, 0x4C, 0x89, 0x64, 0x24, 0x10, 0x4C, 0x89, 0x64, 0x24,
    0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8D,
    0x44, 0x24, 0x10, 0x49, 0x89, 0xE1, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0x48, 0x89, 0xD9, 0xE8,
    0x71, 0x11, 0x00, 0x00]

theorem code_l10156b : ∀ x ∈ codeRange 0x10156b bytes_l10156b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x156b 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015af (movzxR32R8Effect 0x1015af 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1015af (fun s => s.RIP = 0x1015af) (movzxR32R8Effect 0x1015af 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l1015b2, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1015af : List UInt8 :=
  [0x0F, 0xB6, 0xC0]

theorem code_l1015af : ∀ x ∈ codeRange 0x1015af bytes_l1015af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15af 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015b2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015b2 (addR64Imm32Effect 0x1015b2 4 0x218) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1015b2 (fun s => s.RIP = 0x1015b2) (addR64Imm32Effect 0x1015b2 4 0x218) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1015b9 (popR64Effect 0x1015b9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1015b9 (popR64Effect 0x1015b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1015b9 (PopPre 0x1015b9) (popR64Effect 0x1015b9 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1015ba (popR64Effect 0x1015ba 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x1015ba (popR64Effect 0x1015ba 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1015ba (PopPre 0x1015ba) (popR64Effect 0x1015ba 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1015bc (popR64Effect 0x1015bc 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x1015bc (popR64Effect 0x1015bc 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1015bc (PopPre 0x1015bc) (popR64Effect 0x1015bc 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1015be (popR64Effect 0x1015be 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1015be (popR64Effect 0x1015be 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1015be (PopPre 0x1015be) (popR64Effect 0x1015be 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1015c0 (popR64Effect 0x1015c0 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1015c0 (popR64Effect 0x1015c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1015c0 (PopPre 0x1015c0) (popR64Effect 0x1015c0 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1015c2 (popR64Effect 0x1015c2 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1015c2 (popR64Effect 0x1015c2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1015c2 (PopPre 0x1015c2) (popR64Effect 0x1015c2 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1015c3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1015c3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1015c3 (RetPre 0x1015c3) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l1015b2 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x18, 0x02, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1015b2 : ∀ x ∈ codeRange 0x1015b2 bytes_l1015b2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15b2 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015d0 (pushR64Effect 0x1015d0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1015d0 (PushPre 0x1015d0 1) (pushR64Effect 0x1015d0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1015d1 (pushR64Effect 0x1015d1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1015d1 (PushPre 0x1015d1 2) (pushR64Effect 0x1015d1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1015d3 (pushR64Effect 0x1015d3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1015d3 (PushPre 0x1015d3 2) (pushR64Effect 0x1015d3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1015d5 (pushR64Effect 0x1015d5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1015d5 (PushPre 0x1015d5 2) (pushR64Effect 0x1015d5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1015d7 (pushR64Effect 0x1015d7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1015d7 (PushPre 0x1015d7 2) (pushR64Effect 0x1015d7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1015d9 (pushR64Effect 0x1015d9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1015d9 (PushPre 0x1015d9 1) (pushR64Effect 0x1015d9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1015da (subR64Imm32Effect 0x1015da 4 0x218) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1015da (fun s => s.RIP = 0x1015da) (subR64Imm32Effect 0x1015da 4 0x218) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1015e1 (movR64R64Effect 0x1015e1 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 68) (.exec 0x1015e1 (fun s => s.RIP = 0x1015e1) (movR64R64Effect 0x1015e1 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x1015e4 (movR64R64Effect 0x1015e4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 70) (.exec 0x1015e4 (fun s => s.RIP = 0x1015e4) (movR64R64Effect 0x1015e4 14 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.exec 0x1015e7 (StorePre 0x1015e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1015e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015e7 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 72) (.out 0x1015ec (movR64R64Effect 0x1015ec 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 73) (.exec 0x1015ec (fun s => s.RIP = 0x1015ec) (movR64R64Effect 0x1015ec 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.out 0x1015ef (movR64R64Effect 0x1015ef 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 75) (.exec 0x1015ef (fun s => s.RIP = 0x1015ef) (movR64R64Effect 0x1015ef 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x1015f2 (movR64R64Effect 0x1015f2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 77) (.exec 0x1015f2 (fun s => s.RIP = 0x1015f2) (movR64R64Effect 0x1015f2 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x1015f5 (leaR64Effect 0x1015f5 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 79) (.exec 0x1015f5 (fun s => s.RIP = 0x1015f5) (leaR64Effect 0x1015f5 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.out 0x1015fa (movR64R64Effect 0x1015fa 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x1015fa (fun s => s.RIP = 0x1015fa) (movR64R64Effect 0x1015fa 7 5) (Reg.operands [.gpr 5] [])) #v[78]
    (.letOp (n := 82) (.out 0x1015fd (callEffect (fun _ => 0x1057c0) 0x101602) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 83) (.exec 0x1015fd (PushPre 0x1015fd 5) (callEffect (fun _ => 0x1057c0) 0x101602) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 84) (.const ⟨64, 0x101602⟩) #v[]
    (.terminate (.call ⟨.l1057c0, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l101602, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l1015d0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x18, 0x02, 0x00,
    0x00, 0x4C, 0x89, 0xCB, 0x4D, 0x89, 0xC6, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x49, 0x89, 0xD4, 0x49,
    0x89, 0xF5, 0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x10, 0x48, 0x89, 0xEF, 0xE8, 0xBE, 0x41,
    0x00, 0x00]

theorem code_l1015d0 : ∀ x ∈ codeRange 0x1015d0 bytes_l1015d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15d0 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101602 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101602 (leaR64Effect 0x101602 15 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x101602 (fun s => s.RIP = 0x101602) (leaR64Effect 0x101602 15 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10160a (movR64R64Effect 0x10160a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10160a (fun s => s.RIP = 0x10160a) (movR64R64Effect 0x10160a 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x10160d (movR64R64Effect 0x10160d 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x10160d (fun s => s.RIP = 0x10160d) (movR64R64Effect 0x10160d 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x101610 (callEffect (fun _ => 0x102180) 0x101615) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101610 (PushPre 0x101610 5) (callEffect (fun _ => 0x102180) 0x101615) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101615⟩) #v[]
    (.terminate (.call ⟨.l102180, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101615, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101602 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xE8, 0x6B,
    0x0B, 0x00, 0x00]

theorem code_l101602 : ∀ x ∈ codeRange 0x101602 bytes_l101602, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1602 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101615 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101615 (StorePre 0x101615 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101615 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101615 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.out 0x10161a (movR64M64Effect 0x10161a 0 (.sib 4 none 0 (.d32 0x250))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x10161a (LoadPre 0x10161a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x10161a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10161a 0 (.sib 4 none 0 (.d32 0x250))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x101622 (addR64R64Effect 0x101622 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 54]
    (.letOp (n := 57) (.exec 0x101622 (fun s => s.RIP = 0x101622) (addR64R64Effect 0x101622 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 54]
    (.letOp (n := 58) (.exec 0x101625 (StorePre 0x101625 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101625 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101625 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 59) (.exec 0x10162a (StorePre 0x10162a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10162a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10162a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 60) (.out 0x10162f (leaR64Effect 0x10162f 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 61) (.exec 0x10162f (fun s => s.RIP = 0x10162f) (leaR64Effect 0x10162f 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x101634 (movR64R64Effect 0x101634 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 63) (.exec 0x101634 (fun s => s.RIP = 0x101634) (movR64R64Effect 0x101634 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x101637 (movR64R64Effect 0x101637 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 65) (.exec 0x101637 (fun s => s.RIP = 0x101637) (movR64R64Effect 0x101637 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x10163a (movR64R64Effect 0x10163a 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 67) (.exec 0x10163a (fun s => s.RIP = 0x10163a) (movR64R64Effect 0x10163a 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 68) (.out 0x10163d (movR64M64Effect 0x10163d 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x10163d (LoadPre 0x10163d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10163d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10163d 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x101642 (movR64R64Effect 0x101642 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[56]
    (.letOp (n := 71) (.exec 0x101642 (fun s => s.RIP = 0x101642) (movR64R64Effect 0x101642 9 14) (Reg.operands [.gpr 14] [])) #v[56]
    (.letOp (n := 72) (.out 0x101645 (callEffect (fun _ => 0x102720) 0x10164a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x101645 (PushPre 0x101645 5) (callEffect (fun _ => 0x102720) 0x10164a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x10164a⟩) #v[]
    (.terminate (.call ⟨.l102720, RegMap.args [(0, 54), (1, 68), (2, 66), (3, 3), (4, 72), (5, 5), (6, 64), (7, 62), (8, 60), (9, 70), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l10164a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l101615 : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00, 0x49, 0x01, 0xC6,
    0x48, 0x89, 0x5C, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x8D, 0x44, 0x24, 0x10, 0x4C,
    0x89, 0xFF, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xE2, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x4D, 0x89, 0xF1,
    0xE8, 0xD6, 0x10, 0x00, 0x00]

theorem code_l101615 : ∀ x ∈ codeRange 0x101615 bytes_l101615, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1615 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10164a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10164a (movzxR32R8Effect 0x10164a 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10164a (fun s => s.RIP = 0x10164a) (movzxR32R8Effect 0x10164a 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10164d (addR64Imm32Effect 0x10164d 4 0x218) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10164d (fun s => s.RIP = 0x10164d) (addR64Imm32Effect 0x10164d 4 0x218) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101654 (popR64Effect 0x101654 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x101654 (popR64Effect 0x101654 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x101654 (PopPre 0x101654) (popR64Effect 0x101654 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x101655 (popR64Effect 0x101655 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x101655 (popR64Effect 0x101655 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x101655 (PopPre 0x101655) (popR64Effect 0x101655 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x101657 (popR64Effect 0x101657 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x101657 (popR64Effect 0x101657 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x101657 (PopPre 0x101657) (popR64Effect 0x101657 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x101659 (popR64Effect 0x101659 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x101659 (popR64Effect 0x101659 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x101659 (PopPre 0x101659) (popR64Effect 0x101659 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10165b (popR64Effect 0x10165b 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10165b (popR64Effect 0x10165b 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10165b (PopPre 0x10165b) (popR64Effect 0x10165b 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10165d (popR64Effect 0x10165d 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x10165d (popR64Effect 0x10165d 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10165d (PopPre 0x10165d) (popR64Effect 0x10165d 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x10165e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x10165e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x10165e (RetPre 0x10165e) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10164a : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x81, 0xC4, 0x18, 0x02, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10164a : ∀ x ∈ codeRange 0x10164a bytes_l10164a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x164a 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101660 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101660 (pushR64Effect 0x101660 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101660 (PushPre 0x101660 1) (pushR64Effect 0x101660 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101661 (pushR64Effect 0x101661 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101661 (PushPre 0x101661 2) (pushR64Effect 0x101661 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101663 (pushR64Effect 0x101663 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101663 (PushPre 0x101663 2) (pushR64Effect 0x101663 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101665 (pushR64Effect 0x101665 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101665 (PushPre 0x101665 2) (pushR64Effect 0x101665 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101667 (pushR64Effect 0x101667 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101667 (PushPre 0x101667 2) (pushR64Effect 0x101667 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101669 (pushR64Effect 0x101669 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101669 (PushPre 0x101669 1) (pushR64Effect 0x101669 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10166a (subR64Imm32Effect 0x10166a 4 0x228) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10166a (fun s => s.RIP = 0x10166a) (subR64Imm32Effect 0x10166a 4 0x228) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101671 (movR64R64Effect 0x101671 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 68) (.exec 0x101671 (fun s => s.RIP = 0x101671) (movR64R64Effect 0x101671 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101674 (movR64R64Effect 0x101674 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 70) (.exec 0x101674 (fun s => s.RIP = 0x101674) (movR64R64Effect 0x101674 14 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x101677 (movR64R64Effect 0x101677 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 72) (.exec 0x101677 (fun s => s.RIP = 0x101677) (movR64R64Effect 0x101677 15 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x10167a (movR64R64Effect 0x10167a 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 74) (.exec 0x10167a (fun s => s.RIP = 0x10167a) (movR64R64Effect 0x10167a 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x10167d (movR64R64Effect 0x10167d 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 76) (.exec 0x10167d (fun s => s.RIP = 0x10167d) (movR64R64Effect 0x10167d 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x101680 (movR64R64Effect 0x101680 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 78) (.exec 0x101680 (fun s => s.RIP = 0x101680) (movR64R64Effect 0x101680 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x101683 (leaR64Effect 0x101683 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 80) (.exec 0x101683 (fun s => s.RIP = 0x101683) (leaR64Effect 0x101683 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.out 0x101688 (movR64R64Effect 0x101688 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 82) (.exec 0x101688 (fun s => s.RIP = 0x101688) (movR64R64Effect 0x101688 7 5) (Reg.operands [.gpr 5] [])) #v[79]
    (.letOp (n := 83) (.out 0x10168b (callEffect (fun _ => 0x1057c0) 0x101690) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 84) (.exec 0x10168b (PushPre 0x10168b 5) (callEffect (fun _ => 0x1057c0) 0x101690) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 85) (.const ⟨64, 0x101690⟩) #v[]
    (.terminate (.call ⟨.l1057c0, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l101690, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l101660 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x28, 0x02, 0x00,
    0x00, 0x4C, 0x89, 0xCB, 0x4D, 0x89, 0xC6, 0x49, 0x89, 0xCF, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xF5,
    0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x20, 0x48, 0x89, 0xEF, 0xE8, 0x30, 0x41, 0x00, 0x00]

theorem code_l101660 : ∀ x ∈ codeRange 0x101660 bytes_l101660, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1660 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101690 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101690 (leaR64Effect 0x101690 7 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101690 (fun s => s.RIP = 0x101690) (leaR64Effect 0x101690 7 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101698 (movR64R64Effect 0x101698 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x101698 (fun s => s.RIP = 0x101698) (movR64R64Effect 0x101698 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x10169b (movR64M64Effect 0x10169b 5 (.sib 4 none 0 (.d32 0x260))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x10169b (LoadPre 0x10169b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x10169b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10169b 5 (.sib 4 none 0 (.d32 0x260))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1016a3 (callEffect (fun _ => 0x102180) 0x1016a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1016a3 (PushPre 0x1016a3 5) (callEffect (fun _ => 0x102180) 0x1016a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1016a8⟩) #v[]
    (.terminate (.call ⟨.l102180, RegMap.args [(3, 3), (4, 59), (5, 57), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1016a8, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101690 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0xEE, 0x48, 0x8B, 0xAC, 0x24, 0x60,
    0x02, 0x00, 0x00, 0xE8, 0xD8, 0x0A, 0x00, 0x00]

theorem code_l101690 : ∀ x ∈ codeRange 0x101690 bytes_l101690, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1690 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1016a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1016a8 (xorR32R32Effect 0x1016a8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1016a8 (fun s => s.RIP = 0x1016a8) (xorR32R32Effect 0x1016a8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x1016aa (cmpR64R64Effect 0x1016aa 3 5) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 5] []) (.flag .CF)) #v[3, 5]
    (.letOp (n := 56) (.out 0x1016aa (cmpR64R64Effect 0x1016aa 3 5) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 5] []) (.flag .ZF)) #v[3, 5]
    (.letOp (n := 57) (.exec 0x1016aa (fun s => s.RIP = 0x1016aa) (cmpR64R64Effect 0x1016aa 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 58) (.out 0x1016ad (atFlags (condHolds 6) (cmovR64R64Effect 0x1016ad 4 0 3)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[53, 3, 55, 56]
    (.letOp (n := 59) (.exec 0x1016ad (fun s => s.RIP = 0x1016ad) (atFlags (condHolds 6) (cmovR64R64Effect 0x1016ad 4 0 3)) (Reg.operands [.gpr 0, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[53, 3, 55, 56]
    (.letOp (n := 60) (.out 0x1016b1 (movR32Imm32Effect 0x1016b1 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x1016b1 (fun s => s.RIP = 0x1016b1) (movR32Imm32Effect 0x1016b1 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1016b6 (atFlags (condHolds 6) (cmovR64R64Effect 0x1016b6 4 1 14)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 1))) #v[60, 14, 55, 56]
    (.letOp (n := 63) (.exec 0x1016b6 (fun s => s.RIP = 0x1016b6) (atFlags (condHolds 6) (cmovR64R64Effect 0x1016b6 4 1 14)) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[60, 14, 55, 56]
    (.letOp (n := 64) (.exec 0x1016ba (StorePre 0x1016ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1016ba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016ba 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1016bf (StorePre 0x1016bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1016bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016bf 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.exec 0x1016c4 (StorePre 0x1016c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1016c4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016c4 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 67) (.out 0x1016c9 (leaR64Effect 0x1016c9 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 68) (.exec 0x1016c9 (fun s => s.RIP = 0x1016c9) (leaR64Effect 0x1016c9 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1016ce (leaR64Effect 0x1016ce 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 70) (.exec 0x1016ce (fun s => s.RIP = 0x1016ce) (leaR64Effect 0x1016ce 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1016d3 (leaR64Effect 0x1016d3 6 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 72) (.exec 0x1016d3 (fun s => s.RIP = 0x1016d3) (leaR64Effect 0x1016d3 6 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1016db (movR64R64Effect 0x1016db 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 74) (.exec 0x1016db (fun s => s.RIP = 0x1016db) (movR64R64Effect 0x1016db 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 75) (.out 0x1016de (movR64R64Effect 0x1016de 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 76) (.exec 0x1016de (fun s => s.RIP = 0x1016de) (movR64R64Effect 0x1016de 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 77) (.out 0x1016e1 (movR64R64Effect 0x1016e1 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 78) (.exec 0x1016e1 (fun s => s.RIP = 0x1016e1) (movR64R64Effect 0x1016e1 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 79) (.out 0x1016e4 (callEffect (fun _ => 0x102980) 0x1016e9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x1016e4 (PushPre 0x1016e4 5) (callEffect (fun _ => 0x102980) 0x1016e9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x1016e9⟩) #v[]
    (.terminate (.call ⟨.l102980, RegMap.args [(0, 58), (1, 75), (2, 73), (3, 3), (4, 79), (5, 5), (6, 71), (7, 67), (8, 77), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l1016e9, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1016a8 : List UInt8 :=
  [0x31, 0xC0, 0x48, 0x39, 0xEB, 0x48, 0x0F, 0x46, 0xC3, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x49, 0x0F,
    0x46, 0xCE, 0x48, 0x89, 0x4C, 0x24, 0x20, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24,
    0x30, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0x4C, 0x8D, 0x4C, 0x24, 0x20, 0x48, 0x8D, 0xB4, 0x24, 0x10,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0xEA, 0x4C, 0x89, 0xE1, 0x4D, 0x89, 0xF8, 0xE8, 0x97, 0x12, 0x00,
    0x00]

theorem code_l1016a8 : ∀ x ∈ codeRange 0x1016a8 bytes_l1016a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16a8 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1016e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1016e9 (cmpM8Imm8Effect 0x1016e9 5 (.sib 4 none 0 (.d8 0xf)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x1016e9 (LoadPre 0x1016e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1016e9 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1016e9 5 (.sib 4 none 0 (.d8 0xf)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1016f7, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1016f0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1016e9 : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x0F, 0x01, 0x75, 0x07]

theorem code_l1016e9 : ∀ x ∈ codeRange 0x1016e9 bytes_l1016e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16e9 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1016f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1016f0 (movR32Imm32Effect 0x1016f0 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1016f0 (fun s => s.RIP = 0x1016f0) (movR32Imm32Effect 0x1016f0 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101739, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1016f0 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x42]

theorem code_l1016f0 : ∀ x ∈ codeRange 0x1016f0 bytes_l1016f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16f0 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1016f7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1016f7 (movR64M64Effect 0x1016f7 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1016f7 (LoadPre 0x1016f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1016f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1016f7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1016fc (movR64M64Effect 0x1016fc 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1016fc (LoadPre 0x1016fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1016fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1016fc 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101701 (StorePre 0x101701 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101701 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101701 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x101706 (StorePre 0x101706 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101706 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101706 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x10170b (movR64R64Effect 0x10170b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 60) (.exec 0x10170b (fun s => s.RIP = 0x10170b) (movR64R64Effect 0x10170b 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x10170e (subR64Imm8Effect 0x10170e 0 0xf0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.out 0x10170e (subR64Imm8Effect 0x10170e 0 0xf0) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 63) (.exec 0x10170e (fun s => s.RIP = 0x10170e) (subR64Imm8Effect 0x10170e 0 0xf0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.out 0x101712 (atFlags (condHolds 3) (setccR8Effect 0x101712 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[55, 62]
    (.letOp (n := 65) (.exec 0x101712 (fun s => s.RIP = 0x101712) (atFlags (condHolds 3) (setccR8Effect 0x101712 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[55, 62]
    (.letOp (n := 66) (.out 0x101715 (cmpR64R64Effect 0x101715 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[61, 5]
    (.letOp (n := 67) (.out 0x101715 (cmpR64R64Effect 0x101715 0 5) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 5] []) (.flag .ZF)) #v[61, 5]
    (.letOp (n := 68) (.exec 0x101715 (fun s => s.RIP = 0x101715) (cmpR64R64Effect 0x101715 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[61, 5]
    (.letOp (n := 69) (.out 0x101718 (atFlags (condHolds 7) (setccR8Effect 0x101718 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[61, 66, 67]
    (.letOp (n := 70) (.exec 0x101718 (fun s => s.RIP = 0x101718) (atFlags (condHolds 7) (setccR8Effect 0x101718 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[61, 66, 67]
    (.letOp (n := 71) (.out 0x10171b (orR8R8Effect 0x10171b 2 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[69, 64]
    (.letOp (n := 72) (.exec 0x10171b (fun s => s.RIP = 0x10171b) (orR8R8Effect 0x10171b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[69, 64]
    (.letOp (n := 73) (.out 0x10171d (movR32Imm32Effect 0x10171d 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 74) (.exec 0x10171d (fun s => s.RIP = 0x10171d) (movR32Imm32Effect 0x10171d 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 75) ⟨.l101739, RegMap.args [(0, 73), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ ⟨.l101724, RegMap.args [(0, 73), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l1016f7 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48,
    0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xE8, 0xF0, 0x0F, 0x93, 0xC1, 0x48, 0x39,
    0xE8, 0x0F, 0x97, 0xC0, 0x08, 0xC8, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x75, 0x15]

theorem code_l1016f7 : ∀ x ∈ codeRange 0x1016f7 bytes_l1016f7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16f7 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101724 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101724 (movR64M64Effect 0x101724 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101724 (LoadPre 0x101724 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101724 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101724 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101729 (movR64M64Effect 0x101729 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x101729 (LoadPre 0x101729 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101729 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101729 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10172e (StorePre 0x10172e 5 (fun s => AddrMode.addr (.sib 14 (some 3) 0 (.d8 0x8)) s (0x10172e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10172e 1 (.sib 14 (some 3) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14, .gpr 3] [])) #v[55, 14, 3]
    (.letOp (n := 58) (.exec 0x101733 (StorePre 0x101733 4 (fun s => AddrMode.addr (.sib 14 (some 3) 0 .none) s (0x101733 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101733 0 (.sib 14 (some 3) 0 .none)) (Reg.operands [.gpr 0, .gpr 14, .gpr 3] [])) #v[53, 14, 3]
    (.letOp (n := 59) (.out 0x101737 (xorR32R32Effect 0x101737 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 60) (.exec 0x101737 (fun s => s.RIP = 0x101737) (xorR32R32Effect 0x101737 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.terminate (.br ⟨.l101739, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l101724 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x49, 0x89, 0x4C, 0x1E, 0x08, 0x49,
    0x89, 0x04, 0x1E, 0x31, 0xC0]

theorem code_l101724 : ∀ x ∈ codeRange 0x101724 bytes_l101724, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1724 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101739 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101739 (addR64Imm32Effect 0x101739 4 0x228) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x101739 (fun s => s.RIP = 0x101739) (addR64Imm32Effect 0x101739 4 0x228) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101740 (popR64Effect 0x101740 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x101740 (popR64Effect 0x101740 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x101740 (PopPre 0x101740) (popR64Effect 0x101740 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x101741 (popR64Effect 0x101741 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x101741 (popR64Effect 0x101741 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x101741 (PopPre 0x101741) (popR64Effect 0x101741 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x101743 (popR64Effect 0x101743 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x101743 (popR64Effect 0x101743 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x101743 (PopPre 0x101743) (popR64Effect 0x101743 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x101745 (popR64Effect 0x101745 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x101745 (popR64Effect 0x101745 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x101745 (PopPre 0x101745) (popR64Effect 0x101745 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x101747 (popR64Effect 0x101747 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x101747 (popR64Effect 0x101747 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x101747 (PopPre 0x101747) (popR64Effect 0x101747 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x101749 (popR64Effect 0x101749 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x101749 (popR64Effect 0x101749 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x101749 (PopPre 0x101749) (popR64Effect 0x101749 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x10174a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x10174a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x10174a (RetPre 0x10174a) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l101739 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x28, 0x02, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l101739 : ∀ x ∈ codeRange 0x101739 bytes_l101739, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1739 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101750 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101750 (pushR64Effect 0x101750 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101750 (PushPre 0x101750 1) (pushR64Effect 0x101750 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101751 (pushR64Effect 0x101751 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101751 (PushPre 0x101751 2) (pushR64Effect 0x101751 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101753 (pushR64Effect 0x101753 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101753 (PushPre 0x101753 2) (pushR64Effect 0x101753 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101755 (pushR64Effect 0x101755 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101755 (PushPre 0x101755 2) (pushR64Effect 0x101755 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101757 (pushR64Effect 0x101757 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101757 (PushPre 0x101757 2) (pushR64Effect 0x101757 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101759 (pushR64Effect 0x101759 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101759 (PushPre 0x101759 1) (pushR64Effect 0x101759 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10175a (subR64Imm32Effect 0x10175a 4 0x228) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10175a (fun s => s.RIP = 0x10175a) (subR64Imm32Effect 0x10175a 4 0x228) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101761 (movR64R64Effect 0x101761 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 68) (.exec 0x101761 (fun s => s.RIP = 0x101761) (movR64R64Effect 0x101761 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x101764 (movR64R64Effect 0x101764 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 70) (.exec 0x101764 (fun s => s.RIP = 0x101764) (movR64R64Effect 0x101764 14 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.exec 0x101767 (StorePre 0x101767 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101767 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101767 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 72) (.out 0x10176b (movR64R64Effect 0x10176b 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 73) (.exec 0x10176b (fun s => s.RIP = 0x10176b) (movR64R64Effect 0x10176b 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.out 0x10176e (movR64R64Effect 0x10176e 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 75) (.exec 0x10176e (fun s => s.RIP = 0x10176e) (movR64R64Effect 0x10176e 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x101771 (movR64R64Effect 0x101771 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 77) (.exec 0x101771 (fun s => s.RIP = 0x101771) (movR64R64Effect 0x101771 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x101774 (leaR64Effect 0x101774 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 79) (.exec 0x101774 (fun s => s.RIP = 0x101774) (leaR64Effect 0x101774 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.out 0x101779 (movR64R64Effect 0x101779 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x101779 (fun s => s.RIP = 0x101779) (movR64R64Effect 0x101779 7 5) (Reg.operands [.gpr 5] [])) #v[78]
    (.letOp (n := 82) (.out 0x10177c (callEffect (fun _ => 0x1057c0) 0x101781) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 83) (.exec 0x10177c (PushPre 0x10177c 5) (callEffect (fun _ => 0x1057c0) 0x101781) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 84) (.const ⟨64, 0x101781⟩) #v[]
    (.terminate (.call ⟨.l1057c0, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l101781, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l101750 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x28, 0x02, 0x00,
    0x00, 0x4C, 0x89, 0xCB, 0x4D, 0x89, 0xC6, 0x48, 0x89, 0x0C, 0x24, 0x49, 0x89, 0xD4, 0x49, 0x89,
    0xF5, 0x48, 0x89, 0xFE, 0x48, 0x8D, 0x6C, 0x24, 0x20, 0x48, 0x89, 0xEF, 0xE8, 0x3F, 0x40, 0x00,
    0x00]

theorem code_l101750 : ∀ x ∈ codeRange 0x101750 bytes_l101750, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1750 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101781 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101781 (leaR64Effect 0x101781 15 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x101781 (fun s => s.RIP = 0x101781) (leaR64Effect 0x101781 15 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101789 (movR64R64Effect 0x101789 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x101789 (fun s => s.RIP = 0x101789) (movR64R64Effect 0x101789 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x10178c (movR64R64Effect 0x10178c 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x10178c (fun s => s.RIP = 0x10178c) (movR64R64Effect 0x10178c 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x10178f (callEffect (fun _ => 0x102180) 0x101794) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10178f (PushPre 0x10178f 5) (callEffect (fun _ => 0x102180) 0x101794) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101794⟩) #v[]
    (.terminate (.call ⟨.l102180, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101794, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101781 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xE8, 0xEC,
    0x09, 0x00, 0x00]

theorem code_l101781 : ∀ x ∈ codeRange 0x101781 bytes_l101781, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1781 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101794 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101794 (StorePre 0x101794 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101794 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101794 14 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.out 0x101799 (movR64M64Effect 0x101799 14 (.sib 4 none 0 (.d32 0x260))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 55) (.exec 0x101799 (LoadPre 0x101799 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x101799 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101799 14 (.sib 4 none 0 (.d32 0x260))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1017a1 (StorePre 0x1017a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1017a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017a1 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 57) (.exec 0x1017a6 (StorePre 0x1017a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1017a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017a6 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x1017ab (leaR64Effect 0x1017ab 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 59) (.exec 0x1017ab (fun s => s.RIP = 0x1017ab) (leaR64Effect 0x1017ab 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1017b0 (leaR64Effect 0x1017b0 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 61) (.exec 0x1017b0 (fun s => s.RIP = 0x1017b0) (leaR64Effect 0x1017b0 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1017b5 (movR64R64Effect 0x1017b5 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x1017b5 (fun s => s.RIP = 0x1017b5) (movR64R64Effect 0x1017b5 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x1017b8 (movR64R64Effect 0x1017b8 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 65) (.exec 0x1017b8 (fun s => s.RIP = 0x1017b8) (movR64R64Effect 0x1017b8 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x1017bb (movR64R64Effect 0x1017bb 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 67) (.exec 0x1017bb (fun s => s.RIP = 0x1017bb) (movR64R64Effect 0x1017bb 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 68) (.out 0x1017be (movR64M64Effect 0x1017be 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x1017be (LoadPre 0x1017be (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1017be + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017be 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1017c2 (callEffect (fun _ => 0x102980) 0x1017c7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 71) (.exec 0x1017c2 (PushPre 0x1017c2 5) (callEffect (fun _ => 0x102980) 0x1017c7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.const ⟨64, 0x1017c7⟩) #v[]
    (.terminate (.call ⟨.l102980, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 70), (5, 5), (6, 62), (7, 58), (8, 68), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ { target := .l1017c7, kept := #v[], arity := rfl, guard := some (Fin.last 72) })))))))))))))))))))))

def bytes_l101794 : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x20, 0x4C, 0x8B, 0xB4, 0x24, 0x60, 0x02, 0x00, 0x00, 0x48, 0x89, 0x5C,
    0x24, 0x28, 0x4C, 0x89, 0x74, 0x24, 0x30, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0x4C, 0x8D, 0x4C, 0x24,
    0x20, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xEA, 0x4C, 0x89, 0xE1, 0x4C, 0x8B, 0x04, 0x24, 0xE8, 0xB9,
    0x11, 0x00, 0x00]

theorem code_l101794 : ∀ x ∈ codeRange 0x101794 bytes_l101794, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1794 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1017c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1017c7 (movR32Imm32Effect 0x1017c7 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1017c7 (fun s => s.RIP = 0x1017c7) (movR32Imm32Effect 0x1017c7 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1017cc (cmpM8Imm8Effect 0x1017cc 5 (.sib 4 none 0 (.d8 0xf)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 56) (.exec 0x1017cc (LoadPre 0x1017cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1017cc + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1017cc 5 (.sib 4 none 0 (.d8 0xf)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1017e8, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1017d3, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1017c7 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0x80, 0x7C, 0x24, 0x0F, 0x00, 0x75, 0x15]

theorem code_l1017c7 : ∀ x ∈ codeRange 0x1017c7 bytes_l1017c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17c7 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1017d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1017d3 (movR64M64Effect 0x1017d3 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1017d3 (LoadPre 0x1017d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1017d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1017d3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1017d8 (movR64M64Effect 0x1017d8 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1017d8 (LoadPre 0x1017d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1017d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1017d8 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1017dd (StorePre 0x1017dd 5 (fun s => AddrMode.addr (.sib 3 (some 14) 0 (.d8 0x8)) s (0x1017dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017dd 1 (.sib 3 (some 14) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3, .gpr 14] [])) #v[55, 3, 14]
    (.letOp (n := 58) (.exec 0x1017e2 (StorePre 0x1017e2 4 (fun s => AddrMode.addr (.sib 3 (some 14) 0 .none) s (0x1017e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1017e2 0 (.sib 3 (some 14) 0 .none)) (Reg.operands [.gpr 0, .gpr 3, .gpr 14] [])) #v[53, 3, 14]
    (.letOp (n := 59) (.out 0x1017e6 (xorR32R32Effect 0x1017e6 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 60) (.exec 0x1017e6 (fun s => s.RIP = 0x1017e6) (xorR32R32Effect 0x1017e6 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.terminate (.br ⟨.l1017e8, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1017d3 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x4A, 0x89, 0x4C, 0x33, 0x08, 0x4A,
    0x89, 0x04, 0x33, 0x31, 0xC0]

theorem code_l1017d3 : ∀ x ∈ codeRange 0x1017d3 bytes_l1017d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17d3 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1017e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1017e8 (addR64Imm32Effect 0x1017e8 4 0x228) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1017e8 (fun s => s.RIP = 0x1017e8) (addR64Imm32Effect 0x1017e8 4 0x228) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1017ef (popR64Effect 0x1017ef 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1017ef (popR64Effect 0x1017ef 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1017ef (PopPre 0x1017ef) (popR64Effect 0x1017ef 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1017f0 (popR64Effect 0x1017f0 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x1017f0 (popR64Effect 0x1017f0 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1017f0 (PopPre 0x1017f0) (popR64Effect 0x1017f0 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1017f2 (popR64Effect 0x1017f2 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x1017f2 (popR64Effect 0x1017f2 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1017f2 (PopPre 0x1017f2) (popR64Effect 0x1017f2 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1017f4 (popR64Effect 0x1017f4 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1017f4 (popR64Effect 0x1017f4 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1017f4 (PopPre 0x1017f4) (popR64Effect 0x1017f4 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1017f6 (popR64Effect 0x1017f6 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1017f6 (popR64Effect 0x1017f6 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1017f6 (PopPre 0x1017f6) (popR64Effect 0x1017f6 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1017f8 (popR64Effect 0x1017f8 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1017f8 (popR64Effect 0x1017f8 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1017f8 (PopPre 0x1017f8) (popR64Effect 0x1017f8 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1017f9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1017f9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1017f9 (RetPre 0x1017f9) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l1017e8 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x28, 0x02, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1017e8 : ∀ x ∈ codeRange 0x1017e8 bytes_l1017e8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17e8 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101800_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x10184d (StorePre 0x10184d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10184d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10184d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 65]
    (.letOp (n := 89) (.out 0x101852 (movR64R64Effect 0x101852 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 90) (.exec 0x101852 (fun s => s.RIP = 0x101852) (movR64R64Effect 0x101852 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 91) (.out 0x101855 (shrR64Effect 0x101855 4 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[89]
    (.letOp (n := 92) (.exec 0x101855 (fun s => s.RIP = 0x101855) (shrR64Effect 0x101855 4 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (.letOp (n := 93) (.out 0x101859 (leaR64Effect 0x101859 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 94) (.exec 0x101859 (fun s => s.RIP = 0x101859) (leaR64Effect 0x101859 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 95) (.out 0x10185e (movR64R64Effect 0x10185e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 96) (.exec 0x10185e (fun s => s.RIP = 0x10185e) (movR64R64Effect 0x10185e 6 12) (Reg.operands [.gpr 12] [])) #v[67]
    (.letOp (n := 97) (.out 0x101861 (callEffect (fun _ => 0x109980) 0x101866) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 98) (.exec 0x101861 (PushPre 0x101861 5) (callEffect (fun _ => 0x109980) 0x101866) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 99) (.const ⟨64, 0x101866⟩) #v[]
    (.terminate (.call ⟨.l109980, RegMap.args [(0, 83), (1, 85), (2, 91), (3, 72), (4, 97), (5, 5), (6, 95), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 100⟩ { target := .l101866, kept := #v[], arity := rfl, guard := some (Fin.last 99) })))))))))))))

def bytes_l101800_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x50, 0x4C, 0x89, 0xC2, 0x48, 0xC1, 0xEA, 0x04, 0x48, 0x8D, 0x7C, 0x24,
    0x50, 0x4C, 0x89, 0xE6, 0xE8, 0x1A, 0x81, 0x00, 0x00]

theorem code_l101800_1 : ∀ x ∈ codeRange 0x10184d bytes_l101800_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x184d 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101800 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101800 (pushR64Effect 0x101800 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101800 (PushPre 0x101800 1) (pushR64Effect 0x101800 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101801 (pushR64Effect 0x101801 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101801 (PushPre 0x101801 2) (pushR64Effect 0x101801 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101803 (pushR64Effect 0x101803 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101803 (PushPre 0x101803 2) (pushR64Effect 0x101803 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101805 (pushR64Effect 0x101805 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101805 (PushPre 0x101805 2) (pushR64Effect 0x101805 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101807 (pushR64Effect 0x101807 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101807 (PushPre 0x101807 2) (pushR64Effect 0x101807 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101809 (pushR64Effect 0x101809 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101809 (PushPre 0x101809 1) (pushR64Effect 0x101809 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10180a (subR64Imm32Effect 0x10180a 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10180a (fun s => s.RIP = 0x10180a) (subR64Imm32Effect 0x10180a 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101811 (movR64R64Effect 0x101811 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[1]
    (.letOp (n := 68) (.exec 0x101811 (fun s => s.RIP = 0x101811) (movR64R64Effect 0x101811 12 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.exec 0x101814 (StorePre 0x101814 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101814 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101814 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 70) (.out 0x101819 (movR64R64Effect 0x101819 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[9]
    (.letOp (n := 71) (.exec 0x101819 (fun s => s.RIP = 0x101819) (movR64R64Effect 0x101819 14 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 72) (.out 0x10181c (movR64R64Effect 0x10181c 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[8]
    (.letOp (n := 73) (.exec 0x10181c (fun s => s.RIP = 0x10181c) (movR64R64Effect 0x10181c 3 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 74) (.exec 0x10181f (StorePre 0x10181f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10181f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10181f 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 75) (.out 0x101827 (movR64M64Effect 0x101827 15 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 76) (.exec 0x101827 (LoadPre 0x101827 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101827 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101827 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.out 0x10182f (movR64M64Effect 0x10182f 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 78) (.exec 0x10182f (LoadPre 0x10182f (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10182f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10182f 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.exec 0x101833 (StorePre 0x101833 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101833 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101833 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 80) (.out 0x101838 (movR64M64Effect 0x101838 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 81) (.exec 0x101838 (LoadPre 0x101838 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101838 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101838 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.exec 0x10183c (StorePre 0x10183c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10183c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10183c 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 83) (.out 0x101841 (movR64M64Effect 0x101841 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 84) (.exec 0x101841 (LoadPre 0x101841 (fun s => AddrMode.addr (.base 6 .none) s (0x101841 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101841 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 85) (.out 0x101844 (movR64M64Effect 0x101844 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 86) (.exec 0x101844 (LoadPre 0x101844 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101844 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101844 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 87) (.exec 0x101848 (StorePre 0x101848 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101848 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101848 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 65]
    (b_l101800_1)))))))))))))))))))))))))))))))))))

def bytes_l101800 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xCC, 0x48, 0x89, 0x54, 0x24, 0x78, 0x4D, 0x89, 0xCE, 0x4C, 0x89, 0xC3, 0x48,
    0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x60, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x58] ++ bytes_l101800_1

theorem code_l101800 : ∀ x ∈ codeRange 0x101800 bytes_l101800, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1800 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101800_1

@[cfg_block] def b_l101866 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101866 (movR64R64Effect 0x101866 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[3]
    (.letOp (n := 54) (.exec 0x101866 (fun s => s.RIP = 0x101866) (movR64R64Effect 0x101866 13 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x101869 (andR64Imm8Effect 0x101869 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 56) (.out 0x101869 (andR64Imm8Effect 0x101869 13 0xf) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x101869 (fun s => s.RIP = 0x101869) (andR64Imm8Effect 0x101869 13 0xf) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l10193e, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l101873, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l101866 : List UInt8 :=
  [0x49, 0x89, 0xDD, 0x49, 0x83, 0xE5, 0x0F, 0x0F, 0x84, 0xCB, 0x00, 0x00, 0x00]

theorem code_l101866 : ∀ x ∈ codeRange 0x101866 bytes_l101866, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1866 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101873 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101873 (movR64Imm64Effect 0x101873 0 0x1ffffffffffffff0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101873 (fun s => s.RIP = 0x101873) (movR64Imm64Effect 0x101873 0 0x1ffffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10187d (andR64R64Effect 0x10187d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x10187d (fun s => s.RIP = 0x10187d) (andR64R64Effect 0x10187d 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x101880 (addR64R64Effect 0x101880 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 55]
    (.letOp (n := 58) (.exec 0x101880 (fun s => s.RIP = 0x101880) (addR64R64Effect 0x101880 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 55]
    (.letOp (n := 59) (.out 0x101883 (movR32Imm32Effect 0x101883 5 2 0x10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x101883 (fun s => s.RIP = 0x101883) (movR32Imm32Effect 0x101883 5 2 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x101888 (subR64R64Effect 0x101888 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x101888 (fun s => s.RIP = 0x101888) (subR64R64Effect 0x101888 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x10188b (leaR64Effect 0x10188b 7 (.sib 4 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 13] []) (.reg (.gpr 7))) #v[4, 13]
    (.letOp (n := 64) (.exec 0x10188b (fun s => s.RIP = 0x10188b) (leaR64Effect 0x10188b 7 (.sib 4 (some 13) 0 .none)) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 65) (.out 0x10188f (addR64Imm8Effect 0x10188f 7 0x40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x10188f (fun s => s.RIP = 0x10188f) (addR64Imm8Effect 0x10188f 7 0x40) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x101893 (xorR32R32Effect 0x101893 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x101893 (fun s => s.RIP = 0x101893) (xorR32R32Effect 0x101893 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x101895 (callEffect (callMemPtr 0x101895 (.rip 0xff98d)) (0x101895 + BitVec.ofNat 64 (callMemLen (.rip 0xff98d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x101895 (GoesTo (CallMemPre 0x101895 (.rip 0xff98d)) (callEffect (callMemPtr 0x101895 (.rip 0xff98d)) (0x101895 + BitVec.ofNat 64 (callMemLen (.rip 0xff98d)))) 0x103eb0) (callEffect (callMemPtr 0x101895 (.rip 0xff98d)) (0x101895 + BitVec.ofNat 64 (callMemLen (.rip 0xff98d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x10189b⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10189b, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l101873 : List UInt8 :=
  [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F, 0x48, 0x21, 0xD8, 0x49, 0x01, 0xC4,
    0xBA, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xEA, 0x4A, 0x8D, 0x3C, 0x2C, 0x48, 0x83, 0xC7, 0x40,
    0x31, 0xF6, 0xFF, 0x15, 0x8D, 0xF9, 0x0F, 0x00]

theorem code_l101873 : ∀ x ∈ codeRange 0x101873 bytes_l101873, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1873 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10189b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10189b (leaR64Effect 0x10189b 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10189b (fun s => s.RIP = 0x10189b) (leaR64Effect 0x10189b 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1018a0 (movR64R64Effect 0x1018a0 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x1018a0 (fun s => s.RIP = 0x1018a0) (movR64R64Effect 0x1018a0 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1018a3 (movR64R64Effect 0x1018a3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 58) (.exec 0x1018a3 (fun s => s.RIP = 0x1018a3) (movR64R64Effect 0x1018a3 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x1018a6 (callEffect (callMemPtr 0x1018a6 (.rip 0xff95c)) (0x1018a6 + BitVec.ofNat 64 (callMemLen (.rip 0xff95c)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1018a6 (GoesTo (CallMemPre 0x1018a6 (.rip 0xff95c)) (callEffect (callMemPtr 0x1018a6 (.rip 0xff95c)) (0x1018a6 + BitVec.ofNat 64 (callMemLen (.rip 0xff95c)))) 0x103f00) (callEffect (callMemPtr 0x1018a6 (.rip 0xff95c)) (0x1018a6 + BitVec.ofNat 64 (callMemLen (.rip 0xff95c)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1018ac⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1018ac, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10189b : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xEA, 0xFF, 0x15, 0x5C, 0xF9, 0x0F,
    0x00]

theorem code_l10189b : ∀ x ∈ codeRange 0x10189b bytes_l10189b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x189b 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1018ac_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x10190a (movzxR32M8Effect 0x10190a 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 86) (.exec 0x10190a (LoadPre 0x10190a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x10190a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10190a 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x10190f (StorePre 0x10190f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x10190f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10190f 4 1 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.exec 0x101913 (StorePre 0x101913 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101913 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101913 4 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 89) (.out 0x101917 (movzxR32M8Effect 0x101917 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 90) (.exec 0x101917 (LoadPre 0x101917 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101917 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101917 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x10191c (movzxR32M8Effect 0x10191c 5 1 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 92) (.exec 0x10191c (LoadPre 0x10191c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x10191c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10191c 5 1 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x101921 (StorePre 0x101921 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101921 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101921 4 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.exec 0x101925 (StorePre 0x101925 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101925 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101925 4 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 95) (.exec 0x101929 (StorePre 0x101929 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101929 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101929 6 16 (.sib 4 none 0 (.d8 0x17)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x10192f (leaR64Effect 0x10192f 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 97) (.exec 0x10192f (fun s => s.RIP = 0x10192f) (leaR64Effect 0x10192f 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x101934 (leaR64Effect 0x101934 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 99) (.exec 0x101934 (fun s => s.RIP = 0x101934) (leaR64Effect 0x101934 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x101939 (callEffect (fun _ => 0x1034c0) 0x10193e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 101) (.exec 0x101939 (PushPre 0x101939 5) (callEffect (fun _ => 0x1034c0) 0x10193e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.const ⟨64, 0x10193e⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 103⟩ { target := .l10193e, kept := #v[], arity := rfl, guard := some (Fin.last 102) })))))))))))))))))))

def bytes_l1018ac_1 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x1A, 0x88, 0x4C, 0x24, 0x15, 0x88, 0x44, 0x24, 0x1A, 0x0F, 0xB6, 0x44,
    0x24, 0x16, 0x0F, 0xB6, 0x4C, 0x24, 0x19, 0x88, 0x4C, 0x24, 0x16, 0x88, 0x44, 0x24, 0x19, 0x66,
    0xC1, 0x44, 0x24, 0x17, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x50, 0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8,
    0x82, 0x1B, 0x00, 0x00]

theorem code_l1018ac_1 : ∀ x ∈ codeRange 0x10190a bytes_l1018ac_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x190a 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1018ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1018ac (movR64M64Effect 0x1018ac 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1018ac (LoadPre 0x1018ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1018ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1018ac 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1018b1 (movR64M64Effect 0x1018b1 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1018b1 (LoadPre 0x1018b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1018b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1018b1 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1018b6 (StorePre 0x1018b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1018b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1018b6 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1018bb (StorePre 0x1018bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1018bb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1018bb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x1018c0 (movzxR32M8Effect 0x1018c0 5 1 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1018c0 (LoadPre 0x1018c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1018c0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1018c0 5 1 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1018c5 (StorePre 0x1018c5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1018c5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1018c5 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x1018c9 (StorePre 0x1018c9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1018c9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1018c9 4 0 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.out 0x1018cd (movzxR32M16Effect 0x1018cd 5 0 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1018cd (LoadPre 0x1018cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1018cd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018cd 5 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1018d2 (rolR16Effect 0x1018d2 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x1018d2 (fun s => s.RIP = 0x1018d2) (rolR16Effect 0x1018d2 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x1018d6 (movzxR32M16Effect 0x1018d6 5 1 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x1018d6 (LoadPre 0x1018d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1018d6 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018d6 5 1 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1018db (rolR16Effect 0x1018db 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x1018db (fun s => s.RIP = 0x1018db) (rolR16Effect 0x1018db 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x1018df (movzxR32M16Effect 0x1018df 5 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x1018df (LoadPre 0x1018df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1018df + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018df 5 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x1018e4 (StorePre 0x1018e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1018e4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1018e4 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 74) (.out 0x1018e9 (rolR16Effect 0x1018e9 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 75) (.exec 0x1018e9 (fun s => s.RIP = 0x1018e9) (rolR16Effect 0x1018e9 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 76) (.exec 0x1018ed (StorePre 0x1018ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1018ed + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1018ed 5 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 77) (.out 0x1018f2 (movzxR32M16Effect 0x1018f2 5 0 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x1018f2 (LoadPre 0x1018f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1018f2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018f2 5 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1018f7 (rolR16Effect 0x1018f7 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x1018f7 (fun s => s.RIP = 0x1018f7) (rolR16Effect 0x1018f7 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x1018fb (StorePre 0x1018fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1018fb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1018fb 5 0 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x101900 (StorePre 0x101900 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101900 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101900 5 2 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 83) (.out 0x101905 (movzxR32M8Effect 0x101905 5 0 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x101905 (LoadPre 0x101905 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101905 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101905 5 0 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1018ac_1))))))))))))))))))))))))))))))))

def bytes_l1018ac : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x1F, 0x88, 0x4C, 0x24, 0x10, 0x88, 0x44, 0x24,
    0x1F, 0x0F, 0xB7, 0x44, 0x24, 0x11, 0x66, 0xC1, 0xC0, 0x08, 0x0F, 0xB7, 0x4C, 0x24, 0x1D, 0x66,
    0xC1, 0xC1, 0x08, 0x0F, 0xB7, 0x54, 0x24, 0x13, 0x66, 0x89, 0x4C, 0x24, 0x11, 0x66, 0xC1, 0xC2,
    0x08, 0x66, 0x89, 0x44, 0x24, 0x1D, 0x0F, 0xB7, 0x44, 0x24, 0x1B, 0x66, 0xC1, 0xC0, 0x08, 0x66,
    0x89, 0x44, 0x24, 0x13, 0x66, 0x89, 0x54, 0x24, 0x1B, 0x0F, 0xB6, 0x44, 0x24, 0x15] ++ bytes_l1018ac_1

theorem code_l1018ac : ∀ x ∈ codeRange 0x1018ac bytes_l1018ac, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18ac 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1018ac_1

@[cfg_block] def b_l10193e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10193e (movR64R64Effect 0x10193e 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x10193e (fun s => s.RIP = 0x10193e) (movR64R64Effect 0x10193e 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x101941 (shrR64Effect 0x101941 4 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x101941 (fun s => s.RIP = 0x101941) (shrR64Effect 0x101941 4 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x101945 (leaR64Effect 0x101945 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x101945 (fun s => s.RIP = 0x101945) (leaR64Effect 0x101945 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10194a (movR64R64Effect 0x10194a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x10194a (fun s => s.RIP = 0x10194a) (movR64R64Effect 0x10194a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x10194d (callEffect (fun _ => 0x109980) 0x101952) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10194d (PushPre 0x10194d 5) (callEffect (fun _ => 0x109980) 0x101952) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x101952⟩) #v[]
    (.terminate (.call ⟨.l109980, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l101952, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10193e : List UInt8 :=
  [0x4C, 0x89, 0xFA, 0x48, 0xC1, 0xEA, 0x04, 0x48, 0x8D, 0x7C, 0x24, 0x50, 0x4C, 0x89, 0xF6, 0xE8,
    0x2E, 0x80, 0x00, 0x00]

theorem code_l10193e : ∀ x ∈ codeRange 0x10193e bytes_l10193e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x193e 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101952 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101952 (movR64R64Effect 0x101952 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 54) (.exec 0x101952 (fun s => s.RIP = 0x101952) (movR64R64Effect 0x101952 12 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x101955 (andR64Imm8Effect 0x101955 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.out 0x101955 (andR64Imm8Effect 0x101955 12 0xf) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x101955 (fun s => s.RIP = 0x101955) (andR64Imm8Effect 0x101955 12 0xf) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l101a2a, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l10195f, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l101952 : List UInt8 :=
  [0x4D, 0x89, 0xFC, 0x49, 0x83, 0xE4, 0x0F, 0x0F, 0x84, 0xCB, 0x00, 0x00, 0x00]

theorem code_l101952 : ∀ x ∈ codeRange 0x101952 bytes_l101952, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1952 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10195f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10195f (movR64Imm64Effect 0x10195f 0 0xffffffff0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x10195f (fun s => s.RIP = 0x10195f) (movR64Imm64Effect 0x10195f 0 0xffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101969 (andR64R64Effect 0x101969 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101969 (fun s => s.RIP = 0x101969) (andR64R64Effect 0x101969 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10196c (addR64R64Effect 0x10196c 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 55]
    (.letOp (n := 58) (.exec 0x10196c (fun s => s.RIP = 0x10196c) (addR64R64Effect 0x10196c 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 55]
    (.letOp (n := 59) (.out 0x10196f (movR32Imm32Effect 0x10196f 5 2 0x10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10196f (fun s => s.RIP = 0x10196f) (movR32Imm32Effect 0x10196f 5 2 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x101974 (subR64R64Effect 0x101974 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101974 (fun s => s.RIP = 0x101974) (subR64R64Effect 0x101974 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101977 (leaR64Effect 0x101977 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 12]
    (.letOp (n := 64) (.exec 0x101977 (fun s => s.RIP = 0x101977) (leaR64Effect 0x101977 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 65) (.out 0x10197b (addR64Imm8Effect 0x10197b 7 0x40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x10197b (fun s => s.RIP = 0x10197b) (addR64Imm8Effect 0x10197b 7 0x40) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x10197f (xorR32R32Effect 0x10197f 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x10197f (fun s => s.RIP = 0x10197f) (xorR32R32Effect 0x10197f 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x101981 (callEffect (callMemPtr 0x101981 (.rip 0xff8a1)) (0x101981 + BitVec.ofNat 64 (callMemLen (.rip 0xff8a1)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x101981 (GoesTo (CallMemPre 0x101981 (.rip 0xff8a1)) (callEffect (callMemPtr 0x101981 (.rip 0xff8a1)) (0x101981 + BitVec.ofNat 64 (callMemLen (.rip 0xff8a1)))) 0x103eb0) (callEffect (callMemPtr 0x101981 (.rip 0xff8a1)) (0x101981 + BitVec.ofNat 64 (callMemLen (.rip 0xff8a1)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x101987⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l101987, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l10195f : List UInt8 :=
  [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xF8, 0x49, 0x01, 0xC6,
    0xBA, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xE2, 0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x83, 0xC7, 0x40,
    0x31, 0xF6, 0xFF, 0x15, 0xA1, 0xF8, 0x0F, 0x00]

theorem code_l10195f : ∀ x ∈ codeRange 0x10195f bytes_l10195f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x195f 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101987 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101987 (leaR64Effect 0x101987 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101987 (fun s => s.RIP = 0x101987) (leaR64Effect 0x101987 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10198c (movR64R64Effect 0x10198c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x10198c (fun s => s.RIP = 0x10198c) (movR64R64Effect 0x10198c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x10198f (movR64R64Effect 0x10198f 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 58) (.exec 0x10198f (fun s => s.RIP = 0x10198f) (movR64R64Effect 0x10198f 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x101992 (callEffect (callMemPtr 0x101992 (.rip 0xff870)) (0x101992 + BitVec.ofNat 64 (callMemLen (.rip 0xff870)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101992 (GoesTo (CallMemPre 0x101992 (.rip 0xff870)) (callEffect (callMemPtr 0x101992 (.rip 0xff870)) (0x101992 + BitVec.ofNat 64 (callMemLen (.rip 0xff870)))) 0x103f00) (callEffect (callMemPtr 0x101992 (.rip 0xff870)) (0x101992 + BitVec.ofNat 64 (callMemLen (.rip 0xff870)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101998⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101998, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101987 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0xE2, 0xFF, 0x15, 0x70, 0xF8, 0x0F,
    0x00]

theorem code_l101987 : ∀ x ∈ codeRange 0x101987 bytes_l101987, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1987 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101998_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x1019f6 (movzxR32M8Effect 0x1019f6 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 86) (.exec 0x1019f6 (LoadPre 0x1019f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1019f6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1019f6 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1019fb (StorePre 0x1019fb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1019fb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019fb 4 1 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.exec 0x1019ff (StorePre 0x1019ff 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1019ff + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019ff 4 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 89) (.out 0x101a03 (movzxR32M8Effect 0x101a03 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 90) (.exec 0x101a03 (LoadPre 0x101a03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101a03 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101a03 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x101a08 (movzxR32M8Effect 0x101a08 5 1 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 92) (.exec 0x101a08 (LoadPre 0x101a08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101a08 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101a08 5 1 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x101a0d (StorePre 0x101a0d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101a0d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a0d 4 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.exec 0x101a11 (StorePre 0x101a11 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101a11 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a11 4 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 95) (.exec 0x101a15 (StorePre 0x101a15 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101a15 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101a15 6 16 (.sib 4 none 0 (.d8 0x17)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x101a1b (leaR64Effect 0x101a1b 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 97) (.exec 0x101a1b (fun s => s.RIP = 0x101a1b) (leaR64Effect 0x101a1b 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x101a20 (leaR64Effect 0x101a20 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 99) (.exec 0x101a20 (fun s => s.RIP = 0x101a20) (leaR64Effect 0x101a20 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x101a25 (callEffect (fun _ => 0x1034c0) 0x101a2a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 101) (.exec 0x101a25 (PushPre 0x101a25 5) (callEffect (fun _ => 0x1034c0) 0x101a2a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.const ⟨64, 0x101a2a⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 103⟩ { target := .l101a2a, kept := #v[], arity := rfl, guard := some (Fin.last 102) })))))))))))))))))))

def bytes_l101998_1 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x1A, 0x88, 0x4C, 0x24, 0x15, 0x88, 0x44, 0x24, 0x1A, 0x0F, 0xB6, 0x44,
    0x24, 0x16, 0x0F, 0xB6, 0x4C, 0x24, 0x19, 0x88, 0x4C, 0x24, 0x16, 0x88, 0x44, 0x24, 0x19, 0x66,
    0xC1, 0x44, 0x24, 0x17, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x50, 0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8,
    0x96, 0x1A, 0x00, 0x00]

theorem code_l101998_1 : ∀ x ∈ codeRange 0x1019f6 bytes_l101998_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19f6 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101998 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101998 (movR64M64Effect 0x101998 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101998 (LoadPre 0x101998 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101998 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101998 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10199d (movR64M64Effect 0x10199d 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10199d (LoadPre 0x10199d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10199d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10199d 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1019a2 (StorePre 0x1019a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1019a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1019a2 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1019a7 (StorePre 0x1019a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1019a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1019a7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x1019ac (movzxR32M8Effect 0x1019ac 5 1 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1019ac (LoadPre 0x1019ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1019ac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1019ac 5 1 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1019b1 (StorePre 0x1019b1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1019b1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019b1 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x1019b5 (StorePre 0x1019b5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1019b5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019b5 4 0 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.out 0x1019b9 (movzxR32M16Effect 0x1019b9 5 0 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1019b9 (LoadPre 0x1019b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1019b9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019b9 5 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1019be (rolR16Effect 0x1019be 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x1019be (fun s => s.RIP = 0x1019be) (rolR16Effect 0x1019be 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x1019c2 (movzxR32M16Effect 0x1019c2 5 1 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x1019c2 (LoadPre 0x1019c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1019c2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019c2 5 1 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1019c7 (rolR16Effect 0x1019c7 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x1019c7 (fun s => s.RIP = 0x1019c7) (rolR16Effect 0x1019c7 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x1019cb (movzxR32M16Effect 0x1019cb 5 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x1019cb (LoadPre 0x1019cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1019cb + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019cb 5 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x1019d0 (StorePre 0x1019d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1019d0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019d0 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 74) (.out 0x1019d5 (rolR16Effect 0x1019d5 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 75) (.exec 0x1019d5 (fun s => s.RIP = 0x1019d5) (rolR16Effect 0x1019d5 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 76) (.exec 0x1019d9 (StorePre 0x1019d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1019d9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019d9 5 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 77) (.out 0x1019de (movzxR32M16Effect 0x1019de 5 0 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x1019de (LoadPre 0x1019de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1019de + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019de 5 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1019e3 (rolR16Effect 0x1019e3 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x1019e3 (fun s => s.RIP = 0x1019e3) (rolR16Effect 0x1019e3 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x1019e7 (StorePre 0x1019e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1019e7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019e7 5 0 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x1019ec (StorePre 0x1019ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1019ec + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019ec 5 2 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 83) (.out 0x1019f1 (movzxR32M8Effect 0x1019f1 5 0 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x1019f1 (LoadPre 0x1019f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1019f1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1019f1 5 0 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101998_1))))))))))))))))))))))))))))))))

def bytes_l101998 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x1F, 0x88, 0x4C, 0x24, 0x10, 0x88, 0x44, 0x24,
    0x1F, 0x0F, 0xB7, 0x44, 0x24, 0x11, 0x66, 0xC1, 0xC0, 0x08, 0x0F, 0xB7, 0x4C, 0x24, 0x1D, 0x66,
    0xC1, 0xC1, 0x08, 0x0F, 0xB7, 0x54, 0x24, 0x13, 0x66, 0x89, 0x4C, 0x24, 0x11, 0x66, 0xC1, 0xC2,
    0x08, 0x66, 0x89, 0x44, 0x24, 0x1D, 0x0F, 0xB7, 0x44, 0x24, 0x1B, 0x66, 0xC1, 0xC0, 0x08, 0x66,
    0x89, 0x44, 0x24, 0x13, 0x66, 0x89, 0x54, 0x24, 0x1B, 0x0F, 0xB6, 0x44, 0x24, 0x15] ++ bytes_l101998_1

theorem code_l101998 : ∀ x ∈ codeRange 0x101998 bytes_l101998, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1998 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101998_1

@[cfg_block] def b_l101a2a_2 : Block Op Label signature Reg.count 118 :=
  .letOp (n := 118) (.out 0x101ac1 (leaR64Effect 0x101ac1 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 119) (.exec 0x101ac1 (fun s => s.RIP = 0x101ac1) (leaR64Effect 0x101ac1 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.out 0x101ac6 (callEffect (fun _ => 0x1034c0) 0x101acb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 121) (.exec 0x101ac6 (PushPre 0x101ac6 5) (callEffect (fun _ => 0x1034c0) 0x101acb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 122) (.const ⟨64, 0x101acb⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 109), (1, 89), (3, 113), (4, 120), (5, 5), (6, 118), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 123⟩ { target := .l101acb, kept := #v[], arity := rfl, guard := some (Fin.last 122) }))))))

def bytes_l101a2a_2 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8, 0xF5, 0x19, 0x00, 0x00]

theorem code_l101a2a_2 : ∀ x ∈ codeRange 0x101ac1 bytes_l101a2a_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ac1 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101a2a_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x101a6f (movR64R64Effect 0x101a6f 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 88) (.exec 0x101a6f (fun s => s.RIP = 0x101a6f) (movR64R64Effect 0x101a6f 1 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 89) (.out 0x101a72 (shrR64Effect 0x101a72 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 90) (.exec 0x101a72 (fun s => s.RIP = 0x101a72) (shrR64Effect 0x101a72 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.exec 0x101a76 (StorePre 0x101a76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101a76 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a76 4 1 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.exec 0x101a7a (StorePre 0x101a7a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x101a7a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a7a 4 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 93) (.out 0x101a7e (movR64R64Effect 0x101a7e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 94) (.exec 0x101a7e (fun s => s.RIP = 0x101a7e) (movR64R64Effect 0x101a7e 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 95) (.out 0x101a81 (shrR64Effect 0x101a81 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[93]
    (.letOp (n := 96) (.exec 0x101a81 (fun s => s.RIP = 0x101a81) (shrR64Effect 0x101a81 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x101a85 (shrR32Effect 0x101a85 4 15 24) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[59]
    (.letOp (n := 98) (.exec 0x101a85 (fun s => s.RIP = 0x101a85) (shrR32Effect 0x101a85 4 15 24) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 99) (.exec 0x101a89 (StorePre 0x101a89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x101a89 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x101a89 5 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[97, 4]
    (.letOp (n := 100) (.exec 0x101a8e (StorePre 0x101a8e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101a8e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a8e 4 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 101) (.out 0x101a92 (movR64R64Effect 0x101a92 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 102) (.exec 0x101a92 (fun s => s.RIP = 0x101a92) (movR64R64Effect 0x101a92 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 103) (.out 0x101a95 (shrR64Effect 0x101a95 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 104) (.exec 0x101a95 (fun s => s.RIP = 0x101a95) (shrR64Effect 0x101a95 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.exec 0x101a99 (StorePre 0x101a99 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101a99 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x101a99 (.sib 4 none 0 (.d8 0x15)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.exec 0x101a9e (StorePre 0x101a9e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101a9e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a9e 4 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[103, 4]
    (.letOp (n := 107) (.out 0x101aa2 (movR64R64Effect 0x101aa2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 108) (.exec 0x101aa2 (fun s => s.RIP = 0x101aa2) (movR64R64Effect 0x101aa2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 109) (.out 0x101aa5 (shrR64Effect 0x101aa5 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[107]
    (.letOp (n := 110) (.exec 0x101aa5 (fun s => s.RIP = 0x101aa5) (shrR64Effect 0x101aa5 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[107]
    (.letOp (n := 111) (.exec 0x101aa9 (StorePre 0x101aa9 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101aa9 + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x101aa9 (.sib 4 none 0 (.d8 0x16)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.exec 0x101ab0 (StorePre 0x101ab0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101ab0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ab0 4 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[109, 4]
    (.letOp (n := 113) (.out 0x101ab4 (shrR64Effect 0x101ab4 4 3 56) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 114) (.exec 0x101ab4 (fun s => s.RIP = 0x101ab4) (shrR64Effect 0x101ab4 4 3 56) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 115) (.exec 0x101ab8 (StorePre 0x101ab8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101ab8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ab8 4 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x101abc (leaR64Effect 0x101abc 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 117) (.exec 0x101abc (fun s => s.RIP = 0x101abc) (leaR64Effect 0x101abc 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101a2a_2)))))))))))))))))))))))))))))))

def bytes_l101a2a_1 : List UInt8 :=
  [0x4C, 0x89, 0xF9, 0x48, 0xC1, 0xE9, 0x20, 0x88, 0x4C, 0x24, 0x13, 0x88, 0x44, 0x24, 0x1C, 0x48,
    0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x20, 0x41, 0xC1, 0xEF, 0x18, 0x44, 0x88, 0x7C, 0x24, 0x14, 0x88,
    0x44, 0x24, 0x1B, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x28, 0xC6, 0x44, 0x24, 0x15, 0x00, 0x88,
    0x44, 0x24, 0x1A, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x30, 0x66, 0xC7, 0x44, 0x24, 0x16, 0x00,
    0x00, 0x88, 0x44, 0x24, 0x19, 0x48, 0xC1, 0xEB, 0x38, 0x88, 0x5C, 0x24, 0x18, 0x48, 0x8D, 0x7C,
    0x24, 0x50] ++ bytes_l101a2a_2

theorem code_l101a2a_1 : ∀ x ∈ codeRange 0x101a6f bytes_l101a2a_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a6f 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101a2a_2

@[cfg_block] def b_l101a2a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101a2a (shlR64Effect 0x101a2a 4 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 54) (.exec 0x101a2a (fun s => s.RIP = 0x101a2a) (shlR64Effect 0x101a2a 4 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3]
    (.letOp (n := 55) (.out 0x101a2e (shlR64Effect 0x101a2e 4 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 56) (.exec 0x101a2e (fun s => s.RIP = 0x101a2e) (shlR64Effect 0x101a2e 4 15 3) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 57) (.out 0x101a32 (bswapR64Effect 0x101a32 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 58) (.exec 0x101a32 (fun s => s.RIP = 0x101a32) (bswapR64Effect 0x101a32 3 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x101a35 (bswapR64Effect 0x101a35 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 60) (.exec 0x101a35 (fun s => s.RIP = 0x101a35) (bswapR64Effect 0x101a35 3 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 61) (.out 0x101a38 (movR64R64Effect 0x101a38 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x101a38 (fun s => s.RIP = 0x101a38) (movR64R64Effect 0x101a38 0 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 63) (.out 0x101a3b (shrR64Effect 0x101a3b 4 0 56) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x101a3b (fun s => s.RIP = 0x101a3b) (shrR64Effect 0x101a3b 4 0 56) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x101a3f (StorePre 0x101a3f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101a3f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a3f 4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x101a43 (StorePre 0x101a43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101a43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a43 4 3 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 67) (.out 0x101a47 (movR64R64Effect 0x101a47 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 68) (.exec 0x101a47 (fun s => s.RIP = 0x101a47) (movR64R64Effect 0x101a47 0 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 69) (.out 0x101a4a (shrR64Effect 0x101a4a 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x101a4a (fun s => s.RIP = 0x101a4a) (shrR64Effect 0x101a4a 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.exec 0x101a4e (StorePre 0x101a4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101a4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a4e 4 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.exec 0x101a52 (StorePre 0x101a52 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x101a52 + BitVec.ofNat 64 4)) 1) (movM8R8NoRexEffect 0x101a52 4 7 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 73) (.out 0x101a56 (movR32R32Effect 0x101a56 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 74) (.exec 0x101a56 (fun s => s.RIP = 0x101a56) (movR32R32Effect 0x101a56 2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 75) (.out 0x101a58 (shrR32Effect 0x101a58 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x101a58 (fun s => s.RIP = 0x101a58) (shrR32Effect 0x101a58 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x101a5b (movR64R64Effect 0x101a5b 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 78) (.exec 0x101a5b (fun s => s.RIP = 0x101a5b) (movR64R64Effect 0x101a5b 1 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 79) (.out 0x101a5e (shrR64Effect 0x101a5e 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 80) (.exec 0x101a5e (fun s => s.RIP = 0x101a5e) (shrR64Effect 0x101a5e 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x101a62 (StorePre 0x101a62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x101a62 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a62 4 1 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x101a66 (StorePre 0x101a66 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101a66 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a66 4 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 83) (.out 0x101a6a (movR32R32Effect 0x101a6a 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 84) (.exec 0x101a6a (fun s => s.RIP = 0x101a6a) (movR32R32Effect 0x101a6a 2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 85) (.out 0x101a6c (shrR32Effect 0x101a6c 3 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x101a6c (fun s => s.RIP = 0x101a6c) (shrR32Effect 0x101a6c 3 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (b_l101a2a_1))))))))))))))))))))))))))))))))))

def bytes_l101a2a : List UInt8 :=
  [0x48, 0xC1, 0xE3, 0x03, 0x49, 0xC1, 0xE7, 0x03, 0x48, 0x0F, 0xCB, 0x49, 0x0F, 0xCF, 0x4C, 0x89,
    0xF8, 0x48, 0xC1, 0xE8, 0x38, 0x88, 0x44, 0x24, 0x10, 0x88, 0x5C, 0x24, 0x1F, 0x4C, 0x89, 0xF8,
    0x48, 0xC1, 0xE8, 0x30, 0x88, 0x44, 0x24, 0x11, 0x88, 0x7C, 0x24, 0x1E, 0x89, 0xD8, 0xC1, 0xE8,
    0x10, 0x4C, 0x89, 0xF9, 0x48, 0xC1, 0xE9, 0x28, 0x88, 0x4C, 0x24, 0x12, 0x88, 0x44, 0x24, 0x1D,
    0x89, 0xD8, 0xC1, 0xE8, 0x18] ++ bytes_l101a2a_1

theorem code_l101a2a : ∀ x ∈ codeRange 0x101a2a bytes_l101a2a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a2a 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101a2a_1

@[cfg_block] def b_l101acb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101acb (movR64M64Effect 0x101acb 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101acb (LoadPre 0x101acb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101acb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101acb 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x101ad0 (StorePre 0x101ad0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101ad0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ad0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x101ad5 (movR64M64Effect 0x101ad5 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x101ad5 (LoadPre 0x101ad5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101ad5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ad5 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101ada (StorePre 0x101ada 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101ada + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ada 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x101adf (movR64M64Effect 0x101adf 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x101adf (LoadPre 0x101adf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101adf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101adf 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x101ae4 (movR64M64Effect 0x101ae4 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x101ae4 (LoadPre 0x101ae4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101ae4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ae4 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x101ae9 (StorePre 0x101ae9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101ae9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ae9 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x101aee (StorePre 0x101aee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101aee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101aee 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x101af3 (leaR64Effect 0x101af3 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x101af3 (fun s => s.RIP = 0x101af3) (leaR64Effect 0x101af3 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x101af8 (leaR64Effect 0x101af8 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x101af8 (fun s => s.RIP = 0x101af8) (leaR64Effect 0x101af8 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101afd (callEffect (fun _ => 0x1034a0) 0x101b02) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x101afd (PushPre 0x101afd 5) (callEffect (fun _ => 0x1034a0) 0x101b02) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x101b02⟩) #v[]
    (.terminate (.call ⟨.l1034a0, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l101b02, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l101acb : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48,
    0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x48, 0x89,
    0x4C, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8D, 0x7C, 0x24, 0x40, 0x48, 0x8D, 0x74,
    0x24, 0x10, 0xE8, 0x9E, 0x19, 0x00, 0x00]

theorem code_l101acb : ∀ x ∈ codeRange 0x101acb bytes_l101acb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1acb 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b02_3 : Block Op Label signature Reg.count 154 :=
  .letOp (n := 154) (.out 0x101c08 (popR64Effect 0x101c08 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[152]
    (.letOp (n := 155) (.out 0x101c08 (popR64Effect 0x101c08 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[152]
    (.letOp (n := 156) (.exec 0x101c08 (PopPre 0x101c08) (popR64Effect 0x101c08 2 12) (Reg.operands [.gpr 4] [])) #v[152]
    (.letOp (n := 157) (.out 0x101c0a (popR64Effect 0x101c0a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[155]
    (.letOp (n := 158) (.out 0x101c0a (popR64Effect 0x101c0a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[155]
    (.letOp (n := 159) (.exec 0x101c0a (PopPre 0x101c0a) (popR64Effect 0x101c0a 2 13) (Reg.operands [.gpr 4] [])) #v[155]
    (.letOp (n := 160) (.out 0x101c0c (popR64Effect 0x101c0c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[158]
    (.letOp (n := 161) (.out 0x101c0c (popR64Effect 0x101c0c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[158]
    (.letOp (n := 162) (.exec 0x101c0c (PopPre 0x101c0c) (popR64Effect 0x101c0c 2 14) (Reg.operands [.gpr 4] [])) #v[158]
    (.letOp (n := 163) (.out 0x101c0e (popR64Effect 0x101c0e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[161]
    (.letOp (n := 164) (.out 0x101c0e (popR64Effect 0x101c0e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[161]
    (.letOp (n := 165) (.exec 0x101c0e (PopPre 0x101c0e) (popR64Effect 0x101c0e 2 15) (Reg.operands [.gpr 4] [])) #v[161]
    (.letOp (n := 166) (.out 0x101c10 (popR64Effect 0x101c10 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[164]
    (.letOp (n := 167) (.out 0x101c10 (popR64Effect 0x101c10 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[164]
    (.letOp (n := 168) (.exec 0x101c10 (PopPre 0x101c10) (popR64Effect 0x101c10 1 5) (Reg.operands [.gpr 4] [])) #v[164]
    (.letOp (n := 169) (.out 0x101c11 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[167]
    (.letOp (n := 170) (.out 0x101c11 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[167]
    (.letOp (n := 171) (.exec 0x101c11 (RetPre 0x101c11) (retEffect) (Reg.operands [.gpr 4] [])) #v[167]
    (.terminate (.ret (RegMap.args [(0, 127), (1, 125), (2, 145), (3, 151), (4, 170), (5, 166), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)] 172) (some ⟨169, by decide⟩))))))))))))))))))))

def bytes_l101b02_3 : List UInt8 :=
  [0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l101b02_3 : ∀ x ∈ codeRange 0x101c08 bytes_l101b02_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c08 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b02_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.exec 0x101bbb (StorePre 0x101bbb 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101bbb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bbb 3 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[89, 127]
    (.letOp (n := 130) (.exec 0x101bbe (StorePre 0x101bbe 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101bbe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bbe 4 10 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[91, 127]
    (.letOp (n := 131) (.exec 0x101bc2 (StorePre 0x101bc2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101bc2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bc2 4 11 (.base 0 (.d8 0x2))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[93, 127]
    (.letOp (n := 132) (.exec 0x101bc6 (StorePre 0x101bc6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101bc6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bc6 4 15 (.base 0 (.d8 0x3))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[95, 127]
    (.letOp (n := 133) (.exec 0x101bca (StorePre 0x101bca 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101bca + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bca 4 12 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[97, 127]
    (.letOp (n := 134) (.exec 0x101bce (StorePre 0x101bce 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101bce + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bce 4 13 (.base 0 (.d8 0x5))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[99, 127]
    (.letOp (n := 135) (.exec 0x101bd2 (StorePre 0x101bd2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101bd2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bd2 4 5 (.base 0 (.d8 0x6))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[101, 127]
    (.letOp (n := 136) (.exec 0x101bd6 (StorePre 0x101bd6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101bd6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bd6 4 14 (.base 0 (.d8 0x7))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[103, 127]
    (.letOp (n := 137) (.exec 0x101bda (StorePre 0x101bda 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101bda + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bda 4 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[105, 127]
    (.letOp (n := 138) (.exec 0x101bde (StorePre 0x101bde 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101bde + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bde 3 3 (.base 0 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[107, 127]
    (.letOp (n := 139) (.exec 0x101be1 (StorePre 0x101be1 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x101be1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101be1 4 9 (.base 0 (.d8 0xa))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[109, 127]
    (.letOp (n := 140) (.exec 0x101be5 (StorePre 0x101be5 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x101be5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101be5 4 7 (.base 0 (.d8 0xb))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[111, 127]
    (.letOp (n := 141) (.out 0x101be9 (movzxR32M8Effect 0x101be9 5 6 (.sib 4 none 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 142) (.exec 0x101be9 (LoadPre 0x101be9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x101be9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101be9 5 6 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.exec 0x101bee (StorePre 0x101bee 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101bee + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bee 4 6 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[141, 127]
    (.letOp (n := 144) (.exec 0x101bf2 (StorePre 0x101bf2 3 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x101bf2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bf2 3 2 (.base 0 (.d8 0xd))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[118, 127]
    (.letOp (n := 145) (.out 0x101bf5 (movzxR32M8Effect 0x101bf5 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 146) (.exec 0x101bf5 (LoadPre 0x101bf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101bf5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101bf5 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 147) (.exec 0x101bfa (StorePre 0x101bfa 3 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x101bfa + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bfa 3 2 (.base 0 (.d8 0xe))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[145, 127]
    (.letOp (n := 148) (.exec 0x101bfd (StorePre 0x101bfd 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x101bfd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bfd 3 1 (.base 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[125, 127]
    (.letOp (n := 149) (.out 0x101c00 (addR64Imm32Effect 0x101c00 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 150) (.exec 0x101c00 (fun s => s.RIP = 0x101c00) (addR64Imm32Effect 0x101c00 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x101c07 (popR64Effect 0x101c07 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[149]
    (.letOp (n := 152) (.out 0x101c07 (popR64Effect 0x101c07 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[149]
    (.letOp (n := 153) (.exec 0x101c07 (PopPre 0x101c07) (popR64Effect 0x101c07 1 3) (Reg.operands [.gpr 4] [])) #v[149]
    (b_l101b02_3)))))))))))))))))))))))))

def bytes_l101b02_2 : List UInt8 :=
  [0x44, 0x88, 0x00, 0x44, 0x88, 0x50, 0x01, 0x44, 0x88, 0x58, 0x02, 0x44, 0x88, 0x78, 0x03, 0x44,
    0x88, 0x60, 0x04, 0x44, 0x88, 0x68, 0x05, 0x40, 0x88, 0x68, 0x06, 0x44, 0x88, 0x70, 0x07, 0x40,
    0x88, 0x70, 0x08, 0x88, 0x58, 0x09, 0x44, 0x88, 0x48, 0x0A, 0x40, 0x88, 0x78, 0x0B, 0x0F, 0xB6,
    0x74, 0x24, 0x3E, 0x40, 0x88, 0x70, 0x0C, 0x88, 0x50, 0x0D, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x88,
    0x50, 0x0E, 0x88, 0x48, 0x0F, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B] ++ bytes_l101b02_3

theorem code_l101b02_2 : ∀ x ∈ codeRange 0x101bbb bytes_l101b02_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1bbb 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101b02_3

@[cfg_block] def b_l101b02_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x101b6a (xorR8M8Effect 0x101b6a 4 10 (.base 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[60, 87]
    (.letOp (n := 92) (.exec 0x101b6a (LoadPre 0x101b6a (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101b6a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b6a 4 10 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[60, 87]
    (.letOp (n := 93) (.out 0x101b6e (xorR8M8Effect 0x101b6e 4 11 (.base 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[65, 87]
    (.letOp (n := 94) (.exec 0x101b6e (LoadPre 0x101b6e (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101b6e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b6e 4 11 (.base 0 (.d8 0x2))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[65, 87]
    (.letOp (n := 95) (.out 0x101b72 (xorR8M8Effect 0x101b72 4 15 (.base 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[69, 87]
    (.letOp (n := 96) (.exec 0x101b72 (LoadPre 0x101b72 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101b72 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b72 4 15 (.base 0 (.d8 0x3))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[69, 87]
    (.letOp (n := 97) (.out 0x101b76 (xorR8M8Effect 0x101b76 4 12 (.base 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[73, 87]
    (.letOp (n := 98) (.exec 0x101b76 (LoadPre 0x101b76 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101b76 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b76 4 12 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[73, 87]
    (.letOp (n := 99) (.out 0x101b7a (xorR8M8Effect 0x101b7a 4 13 (.base 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[77, 87]
    (.letOp (n := 100) (.exec 0x101b7a (LoadPre 0x101b7a (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101b7a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b7a 4 13 (.base 0 (.d8 0x5))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[77, 87]
    (.letOp (n := 101) (.out 0x101b7e (xorR8M8Effect 0x101b7e 4 5 (.base 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[81, 87]
    (.letOp (n := 102) (.exec 0x101b7e (LoadPre 0x101b7e (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101b7e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b7e 4 5 (.base 0 (.d8 0x6))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[81, 87]
    (.letOp (n := 103) (.out 0x101b82 (xorR8M8Effect 0x101b82 4 14 (.base 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[85, 87]
    (.letOp (n := 104) (.exec 0x101b82 (LoadPre 0x101b82 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101b82 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b82 4 14 (.base 0 (.d8 0x7))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[85, 87]
    (.letOp (n := 105) (.out 0x101b86 (xorR8M8Effect 0x101b86 4 6 (.base 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[83, 87]
    (.letOp (n := 106) (.exec 0x101b86 (LoadPre 0x101b86 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101b86 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b86 4 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[83, 87]
    (.letOp (n := 107) (.out 0x101b8a (xorR8M8Effect 0x101b8a 3 3 (.base 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[79, 87]
    (.letOp (n := 108) (.exec 0x101b8a (LoadPre 0x101b8a (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101b8a + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101b8a 3 3 (.base 0 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[79, 87]
    (.letOp (n := 109) (.out 0x101b8d (xorR8M8Effect 0x101b8d 4 9 (.base 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[75, 87]
    (.letOp (n := 110) (.exec 0x101b8d (LoadPre 0x101b8d (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x101b8d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b8d 4 9 (.base 0 (.d8 0xa))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[75, 87]
    (.letOp (n := 111) (.out 0x101b91 (xorR8M8Effect 0x101b91 4 7 (.base 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[71, 87]
    (.letOp (n := 112) (.exec 0x101b91 (LoadPre 0x101b91 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x101b91 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b91 4 7 (.base 0 (.d8 0xb))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[71, 87]
    (.letOp (n := 113) (.out 0x101b95 (xorR8M8Effect 0x101b95 3 2 (.base 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[67, 87]
    (.letOp (n := 114) (.exec 0x101b95 (LoadPre 0x101b95 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101b95 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101b95 3 2 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[67, 87]
    (.letOp (n := 115) (.exec 0x101b98 (StorePre 0x101b98 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x101b98 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101b98 4 2 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x101b9c (movzxR32M8Effect 0x101b9c 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 117) (.exec 0x101b9c (LoadPre 0x101b9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101b9c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b9c 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x101ba1 (xorR8M8Effect 0x101ba1 3 2 (.base 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[116, 87]
    (.letOp (n := 119) (.exec 0x101ba1 (LoadPre 0x101ba1 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x101ba1 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101ba1 3 2 (.base 0 (.d8 0xd))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[116, 87]
    (.letOp (n := 120) (.out 0x101ba4 (xorR8M8Effect 0x101ba4 3 1 (.base 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[58, 87]
    (.letOp (n := 121) (.exec 0x101ba4 (LoadPre 0x101ba4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x101ba4 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101ba4 3 1 (.base 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[58, 87]
    (.letOp (n := 122) (.exec 0x101ba7 (StorePre 0x101ba7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101ba7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ba7 4 1 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[120, 4]
    (.letOp (n := 123) (.out 0x101bab (movzxR32M8Effect 0x101bab 5 1 (.sib 4 none 0 (.d8 0x3f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 124) (.exec 0x101bab (LoadPre 0x101bab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101bab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101bab 5 1 (.sib 4 none 0 (.d8 0x3f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 125) (.out 0x101bb0 (xorR8M8Effect 0x101bb0 3 1 (.base 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[123, 87]
    (.letOp (n := 126) (.exec 0x101bb0 (LoadPre 0x101bb0 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x101bb0 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101bb0 3 1 (.base 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[123, 87]
    (.letOp (n := 127) (.out 0x101bb3 (movR64M64Effect 0x101bb3 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 128) (.exec 0x101bb3 (LoadPre 0x101bb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101bb3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101bb3 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101b02_2))))))))))))))))))))))))))))))))))))))

def bytes_l101b02_1 : List UInt8 :=
  [0x44, 0x32, 0x50, 0x01, 0x44, 0x32, 0x58, 0x02, 0x44, 0x32, 0x78, 0x03, 0x44, 0x32, 0x60, 0x04,
    0x44, 0x32, 0x68, 0x05, 0x40, 0x32, 0x68, 0x06, 0x44, 0x32, 0x70, 0x07, 0x40, 0x32, 0x70, 0x08,
    0x32, 0x58, 0x09, 0x44, 0x32, 0x48, 0x0A, 0x40, 0x32, 0x78, 0x0B, 0x32, 0x50, 0x0C, 0x88, 0x54,
    0x24, 0x3E, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x32, 0x50, 0x0D, 0x32, 0x48, 0x0E, 0x88, 0x4C, 0x24,
    0x0F, 0x0F, 0xB6, 0x4C, 0x24, 0x3F, 0x32, 0x48, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00,
    0x00] ++ bytes_l101b02_2

theorem code_l101b02_1 : ∀ x ∈ codeRange 0x101b6a bytes_l101b02_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b6a 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101b02_2

@[cfg_block] def b_l101b02 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101b02 (movzxR32M8Effect 0x101b02 6 8 (.sib 4 none 0 (.d8 0x4f))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 54) (.exec 0x101b02 (LoadPre 0x101b02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x101b02 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b02 6 8 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101b08 (movzxR32M8Effect 0x101b08 5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x101b08 (LoadPre 0x101b08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101b08 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b08 5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101b0d (StorePre 0x101b0d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101b0d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101b0d 4 0 (.sib 4 none 0 (.d8 0x3f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x101b11 (movzxR32M8Effect 0x101b11 5 1 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x101b11 (LoadPre 0x101b11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x101b11 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b11 5 1 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x101b16 (movzxR32M8Effect 0x101b16 6 10 (.sib 4 none 0 (.d8 0x4e))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x101b16 (LoadPre 0x101b16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x101b16 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b16 6 10 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x101b1c (movzxR32M8Effect 0x101b1c 5 0 (.sib 4 none 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x101b1c (LoadPre 0x101b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x101b1c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b1c 5 0 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x101b21 (StorePre 0x101b21 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101b21 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101b21 4 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x101b25 (movzxR32M8Effect 0x101b25 6 11 (.sib 4 none 0 (.d8 0x4d))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 66) (.exec 0x101b25 (LoadPre 0x101b25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x101b25 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b25 6 11 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x101b2b (movzxR32M8Effect 0x101b2b 5 2 (.sib 4 none 0 (.d8 0x43))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x101b2b (LoadPre 0x101b2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x101b2b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b2b 5 2 (.sib 4 none 0 (.d8 0x43))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101b30 (movzxR32M8Effect 0x101b30 6 15 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 70) (.exec 0x101b30 (LoadPre 0x101b30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x101b30 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b30 6 15 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x101b36 (movzxR32M8Effect 0x101b36 5 7 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x101b36 (LoadPre 0x101b36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x101b36 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b36 5 7 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x101b3b (movzxR32M8Effect 0x101b3b 6 12 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x101b3b (LoadPre 0x101b3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x101b3b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b3b 6 12 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x101b41 (movzxR32M8Effect 0x101b41 6 9 (.sib 4 none 0 (.d8 0x45))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 76) (.exec 0x101b41 (LoadPre 0x101b41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x101b41 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b41 6 9 (.sib 4 none 0 (.d8 0x45))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x101b47 (movzxR32M8Effect 0x101b47 6 13 (.sib 4 none 0 (.d8 0x4a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 78) (.exec 0x101b47 (LoadPre 0x101b47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x101b47 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b47 6 13 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x101b4d (movzxR32M8Effect 0x101b4d 5 3 (.sib 4 none 0 (.d8 0x46))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 80) (.exec 0x101b4d (LoadPre 0x101b4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x101b4d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b4d 5 3 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x101b52 (movzxR32M8Effect 0x101b52 5 5 (.sib 4 none 0 (.d8 0x49))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 82) (.exec 0x101b52 (LoadPre 0x101b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x101b52 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b52 5 5 (.sib 4 none 0 (.d8 0x49))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x101b57 (movzxR32M8Effect 0x101b57 5 6 (.sib 4 none 0 (.d8 0x47))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x101b57 (LoadPre 0x101b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x101b57 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b57 5 6 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x101b5c (movzxR32M8Effect 0x101b5c 6 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 86) (.exec 0x101b5c (LoadPre 0x101b5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101b5c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b5c 6 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x101b62 (movR64M64Effect 0x101b62 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x101b62 (LoadPre 0x101b62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101b62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101b62 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x101b67 (xorR8M8Effect 0x101b67 3 8 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[53, 87]
    (.letOp (n := 90) (.exec 0x101b67 (LoadPre 0x101b67 (fun s => AddrMode.addr (.base 0 .none) s (0x101b67 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101b67 3 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[53, 87]
    (b_l101b02_1))))))))))))))))))))))))))))))))))))))

def bytes_l101b02 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x4F, 0x0F, 0xB6, 0x44, 0x24, 0x40, 0x88, 0x44, 0x24, 0x3F, 0x0F,
    0xB6, 0x4C, 0x24, 0x41, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x4E, 0x0F, 0xB6, 0x44, 0x24, 0x42, 0x88,
    0x44, 0x24, 0x0F, 0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x4D, 0x0F, 0xB6, 0x54, 0x24, 0x43, 0x44, 0x0F,
    0xB6, 0x7C, 0x24, 0x4C, 0x0F, 0xB6, 0x7C, 0x24, 0x44, 0x44, 0x0F, 0xB6, 0x64, 0x24, 0x4B, 0x44,
    0x0F, 0xB6, 0x4C, 0x24, 0x45, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4A, 0x0F, 0xB6, 0x5C, 0x24, 0x46,
    0x0F, 0xB6, 0x6C, 0x24, 0x49, 0x0F, 0xB6, 0x74, 0x24, 0x47, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x48,
    0x48, 0x8B, 0x44, 0x24, 0x78, 0x44, 0x32, 0x00] ++ bytes_l101b02_1

theorem code_l101b02 : ∀ x ∈ codeRange 0x101b02 bytes_l101b02, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b02 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101b02_1

end AesGcm.Proofs.Machine.LIR
