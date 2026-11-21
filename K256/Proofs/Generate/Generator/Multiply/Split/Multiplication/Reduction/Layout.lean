import K256.Proofs.Common.Tactic.Replay
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Finish

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Common.Tactic.Replay K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

def v53 (w : Vector (BitVec 64) 8) : BitVec 64 := w[4]

def v55 (w : Vector (BitVec 64) 8) : BitVec 64 := w[5]

def v57 (w : Vector (BitVec 64) 8) : BitVec 64 := (v53 w)

def v59 (w : Vector (BitVec 64) 8) : BitVec 64 := (v57 w) * 0x402da1732fc9bebf

def v60 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v57 w) 0x402da1732fc9bebf).2

def v62 (w : Vector (BitVec 64) 8) : BitVec 64 := (v60 w)

def v64 (w : Vector (BitVec 64) 8) : BitVec 64 := (v59 w)

def v66 (w : Vector (BitVec 64) 8) : BitVec 64 := (v55 w)

def v68 (w : Vector (BitVec 64) 8) : BitVec 64 := (v66 w) * 0x402da1732fc9bebf

def v69 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v66 w) 0x402da1732fc9bebf).2

def v71 (w : Vector (BitVec 64) 8) : BitVec 64 := (v68 w)

def v73 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x402da1732fc9bebf

def v75 (w : Vector (BitVec 64) 8) : BitVec 64 := (v69 w)

def v77 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x4551231950b75fc4

def v79 (w : Vector (BitVec 64) 8) : BitVec 64 := (v53 w)

def v81 (w : Vector (BitVec 64) 8) : BitVec 64 := (v79 w) * (v77 w)

def v82 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v79 w) (v77 w)).2

def v84 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v64 w) w[0]).1

def v85 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v64 w) w[0]).2.CF

def v88 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v85 w) (v62 w) w[1]).1

def v89 (w : Vector (BitVec 64) 8) : Bool := (adcSpec (v85 w) (v62 w) w[1]).2.CF

def v91 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v89 w) (v82 w) (v75 w)).1

def v93 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v95 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v88 w) (v71 w)).1

def v96 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v88 w) (v71 w)).2.CF

def v98 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v96 w) then 1 else 0) (v93 w)

def v100 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v95 w) (v81 w)).1

def v101 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v95 w) (v81 w)).2.CF

def v103 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v101 w) (v98 w) (v91 w)).1

def v105 (w : Vector (BitVec 64) 8) : BitVec 64 := w[6]

def v107 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v109 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v103 w) w[2]).1

def v110 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v103 w) w[2]).2.CF

def v112 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v110 w) then 1 else 0) (v107 w)

def v114 (w : Vector (BitVec 64) 8) : BitVec 64 := (v105 w)

def v116 (w : Vector (BitVec 64) 8) : BitVec 64 := (v114 w) * (v73 w)

def v117 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v114 w) (v73 w)).2

def v119 (w : Vector (BitVec 64) 8) : BitVec 64 := (v117 w)

def v121 (w : Vector (BitVec 64) 8) : BitVec 64 := (v116 w)

def v123 (w : Vector (BitVec 64) 8) : BitVec 64 := (v55 w)

def v125 (w : Vector (BitVec 64) 8) : BitVec 64 := (v123 w) * (v77 w)

def v126 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v123 w) (v77 w)).2

def v128 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v126 w) (v119 w)).1

def v130 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v121 w) (v109 w)).1

def v131 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v121 w) (v109 w)).2.CF

def v133 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v131 w) (v128 w) (v112 w)).1

def v135 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v137 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v130 w) (v125 w)).1

def v138 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v130 w) (v125 w)).2.CF

def v140 (w : Vector (BitVec 64) 8) : BitVec 64 := w[7]

def v142 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v138 w) then 1 else 0) (v135 w)

def v144 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v137 w) (v53 w)).1

def v145 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v137 w) (v53 w)).2.CF

def v147 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v145 w) (v142 w) (v133 w)).1

def v149 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v151 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v147 w) w[3]).1

def v152 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v147 w) w[3]).2.CF

def v154 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v152 w) then 1 else 0) (v149 w)

def v156 (w : Vector (BitVec 64) 8) : BitVec 64 := (v140 w)

def v158 (w : Vector (BitVec 64) 8) : BitVec 64 := (v156 w) * (v73 w)

def v159 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v156 w) (v73 w)).2

def v161 (w : Vector (BitVec 64) 8) : BitVec 64 := (v159 w)

def v163 (w : Vector (BitVec 64) 8) : BitVec 64 := (v158 w)

def v165 (w : Vector (BitVec 64) 8) : BitVec 64 := (v105 w)

def v167 (w : Vector (BitVec 64) 8) : BitVec 64 := (v165 w) * (v77 w)

def v168 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v165 w) (v77 w)).2

def v170 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v168 w) (v161 w)).1

def v172 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v163 w) (v151 w)).1

def v173 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v163 w) (v151 w)).2.CF

def v175 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v173 w) (v170 w) (v154 w)).1

def v177 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v179 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v172 w) (v167 w)).1

def v180 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v172 w) (v167 w)).2.CF

def v182 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v180 w) then 1 else 0) (v177 w)

def v184 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v179 w) (v55 w)).1

def v185 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v179 w) (v55 w)).2.CF

def v187 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v185 w) (v182 w) (v175 w)).1

def v189 (w : Vector (BitVec 64) 8) : BitVec 64 := (v140 w)

def v191 (w : Vector (BitVec 64) 8) : BitVec 64 := (v189 w) * (v77 w)

def v192 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v189 w) (v77 w)).2

def v194 (w : Vector (BitVec 64) 8) : BitVec 64 := (v191 w)

def v196 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v198 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v194 w) (v187 w)).1

def v199 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v194 w) (v187 w)).2.CF

def v201 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v199 w) then 1 else 0) (v196 w)

def v203 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v198 w) (v105 w)).1

def v204 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v198 w) (v105 w)).2.CF

def v206 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v204 w) (v201 w) (v192 w)).1

def v208 (w : Vector (BitVec 64) 8) : BitVec 64 := (v203 w)

def v210 (w : Vector (BitVec 64) 8) : BitVec 64 := (v73 w)

def v213 (w : Vector (BitVec 64) 8) : BitVec 64 := (v208 w) * (v73 w)

def v214 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v208 w) (v73 w)).2

def v216 (w : Vector (BitVec 64) 8) : BitVec 64 := (v213 w)

def v218 (w : Vector (BitVec 64) 8) : BitVec 64 := (v214 w)

def v220 (w : Vector (BitVec 64) 8) : BitVec 64 := (v206 w)

def v222 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v220 w) (v140 w)).1

def v223 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v220 w) (v140 w)).2.CF

def v225 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x0

def v227 (w : Vector (BitVec 64) 8) : BitVec 64 := if (v223 w) then (v210 w) else (v225 w)

def v229 (w : Vector (BitVec 64) 8) : BitVec 64 := (v222 w)

def v231 (w : Vector (BitVec 64) 8) : BitVec 64 := (v229 w) * (v210 w)

def v232 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v229 w) (v210 w)).2

def v234 (w : Vector (BitVec 64) 8) : BitVec 64 := (v232 w)

def v236 (w : Vector (BitVec 64) 8) : BitVec 64 := (v231 w)

def v238 (w : Vector (BitVec 64) 8) : BitVec 64 := (v203 w)

def v240 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x4551231950b75fc4

def v242 (w : Vector (BitVec 64) 8) : BitVec 64 := (v238 w) * (v240 w)

def v243 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v238 w) (v240 w)).2

def v245 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v216 w) (v84 w)).1

def v246 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v216 w) (v84 w)).2.CF

def v249 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v246 w) (v218 w) (v100 w)).1

def v250 (w : Vector (BitVec 64) 8) : Bool := (adcSpec (v246 w) (v218 w) (v100 w)).2.CF

def v252 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v250 w) (v243 w) (v234 w)).1

def v254 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v256 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v249 w) (v236 w)).1

def v257 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v249 w) (v236 w)).2.CF

def v259 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v257 w) then 1 else 0) (v254 w)

def v261 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v256 w) (v242 w)).1

def v262 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v256 w) (v242 w)).2.CF

def v264 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v262 w) (v259 w) (v252 w)).1

def v266 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v268 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v264 w) (v144 w)).1

def v269 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v264 w) (v144 w)).2.CF

def v271 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v269 w) then 1 else 0) (v266 w)

def v273 (w : Vector (BitVec 64) 8) : BitVec 64 := (v222 w)

def v275 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x4551231950b75fc4

def v277 (w : Vector (BitVec 64) 8) : BitVec 64 := (v273 w) * (v275 w)

def v278 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v273 w) (v275 w)).2

def v280 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v268 w) (v227 w)).1

def v281 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v268 w) (v227 w)).2.CF

def v283 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v281 w) (v278 w) (v271 w)).1

def v285 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v287 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v280 w) (v277 w)).1

def v288 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v280 w) (v277 w)).2.CF

def v290 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v288 w) then 1 else 0) (v285 w)

def v292 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v287 w) (v203 w)).1

def v293 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v287 w) (v203 w)).2.CF

def v295 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v293 w) (v290 w) (v283 w)).1

def v297 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v299 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v295 w) (v184 w)).1

def v300 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v295 w) (v184 w)).2.CF

def v302 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v300 w) then 1 else 0) (v297 w)

def v304 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v206 w) (v140 w)).1

def v305 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v206 w) (v140 w)).2.CF

def v307 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x0

def v309 (w : Vector (BitVec 64) 8) : BitVec 64 := if (v305 w) then (v275 w) else (v307 w)

def v311 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v305 w) (v302 w) 0).1

def v313 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v315 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v309 w) (v299 w)).1

def v316 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v309 w) (v299 w)).2.CF

def v318 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v316 w) then 1 else 0) (v313 w)

def v320 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v315 w) (v304 w)).1

def v321 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v315 w) (v304 w)).2.CF

def v323 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v321 w) (v318 w) (v311 w)).1

def v325 (w : Vector (BitVec 64) 8) : BitVec 64 := (v323 w)

def v327 (w : Vector (BitVec 64) 8) : BitVec 64 := (v73 w)

def v329 (w : Vector (BitVec 64) 8) : BitVec 64 := (v325 w) * (v327 w)

def v330 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v325 w) (v327 w)).2

def v332 (w : Vector (BitVec 64) 8) : BitVec 64 := (v330 w)

def v334 (w : Vector (BitVec 64) 8) : BitVec 64 := (v329 w)

def v336 (w : Vector (BitVec 64) 8) : BitVec 64 := (v323 w)

def v338 (w : Vector (BitVec 64) 8) : BitVec 64 := (v336 w) * (v275 w)

def v339 (w : Vector (BitVec 64) 8) : BitVec 64 := (mulResult (v336 w) (v275 w)).2

def v341 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v338 w) (v261 w)).1

def v342 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v338 w) (v261 w)).2.CF

def v344 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v342 w) (v339 w) 0).1

def v346 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v348 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v323 w) (v292 w)).1

def v349 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v323 w) (v292 w)).2.CF

def v351 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v349 w) then 1 else 0) (v346 w)

def v353 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v334 w) (v245 w)).1

def v354 (w : Vector (BitVec 64) 8) : Bool := (addSpec (v334 w) (v245 w)).2.CF

def v356 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v354 w) (v341 w) (v332 w)).1

def v357 (w : Vector (BitVec 64) 8) : Bool := (adcSpec (v354 w) (v341 w) (v332 w)).2.CF

def v359 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v357 w) (v348 w) (v344 w)).1

def v360 (w : Vector (BitVec 64) 8) : Bool := (adcSpec (v357 w) (v348 w) (v344 w)).2.CF

def v362 (w : Vector (BitVec 64) 8) : BitVec 64 := (adcSpec (v360 w) (v351 w) (v320 w)).1

def v363 (w : Vector (BitVec 64) 8) : Bool := (adcSpec (v360 w) (v351 w) (v320 w)).2.CF

def v365 (w : Vector (BitVec 64) 8) : BitVec 64 := mergeGPR 8 (if (v363 w) then 1 else 0) (v292 w)

def v368 (w : Vector (BitVec 64) 8) : BitVec 64 := (v327 w) + (v353 w)

def v371 (w : Vector (BitVec 64) 8) : BitVec 64 := ~~~(v353 w)

def v373 (w : Vector (BitVec 64) 8) : BitVec 64 := (v371 w) ||| (v368 w)

def v375 (w : Vector (BitVec 64) 8) : BitVec 64 := (v373 w) >>> 63

def v380 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v382 (w : Vector (BitVec 64) 8) : BitVec 64 := (v380 w) - (v375 w)

def v385 (w : Vector (BitVec 64) 8) : BitVec 64 := (v356 w)

def v387 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0xbaaedce6af48a03b

def v389 (w : Vector (BitVec 64) 8) : BitVec 64 := (v385 w) - (v387 w)

def v391 (w : Vector (BitVec 64) 8) : BitVec 64 := BitVec.sshiftRight (v382 w) 63

def v393 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v391 w) (v389 w)).1

def v395 (w : Vector (BitVec 64) 8) : BitVec 64 := (v356 w)

def v397 (w : Vector (BitVec 64) 8) : BitVec 64 := ~~~(v395 w)

def v399 (w : Vector (BitVec 64) 8) : BitVec 64 := (v387 w)

def v401 (w : Vector (BitVec 64) 8) : BitVec 64 := (v399 w) &&& (v397 w)

def v403 (w : Vector (BitVec 64) 8) : BitVec 64 := (v397 w) ||| (v387 w)

def v405 (w : Vector (BitVec 64) 8) : BitVec 64 := (v403 w) &&& (v393 w)

def v407 (w : Vector (BitVec 64) 8) : BitVec 64 := (v405 w) ||| (v401 w)

def v409 (w : Vector (BitVec 64) 8) : BitVec 64 := (v407 w) >>> 63

def v412 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v414 (w : Vector (BitVec 64) 8) : BitVec 64 := (v412 w) - (v409 w)

def v416 (w : Vector (BitVec 64) 8) : BitVec 64 := (v359 w)

def v418 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0xfffffffffffffffe

def v420 (w : Vector (BitVec 64) 8) : BitVec 64 := (v416 w) - (v418 w)

def v422 (w : Vector (BitVec 64) 8) : BitVec 64 := BitVec.sshiftRight (v414 w) 63

def v424 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v422 w) (v420 w)).1

def v426 (w : Vector (BitVec 64) 8) : BitVec 64 := (v359 w)

def v428 (w : Vector (BitVec 64) 8) : BitVec 64 := ~~~(v426 w)

def v430 (w : Vector (BitVec 64) 8) : BitVec 64 := (v418 w)

def v432 (w : Vector (BitVec 64) 8) : BitVec 64 := (v430 w) &&& (v428 w)

def v434 (w : Vector (BitVec 64) 8) : BitVec 64 := (v428 w) ||| (v418 w)

def v436 (w : Vector (BitVec 64) 8) : BitVec 64 := (v434 w) &&& (v424 w)

def v438 (w : Vector (BitVec 64) 8) : BitVec 64 := (v436 w) ||| (v432 w)

def v440 (w : Vector (BitVec 64) 8) : BitVec 64 := (v438 w) >>> 63

def v443 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v445 (w : Vector (BitVec 64) 8) : BitVec 64 := (v443 w) - (v440 w)

def v447 (w : Vector (BitVec 64) 8) : BitVec 64 := (v362 w)

def v449 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0xffffffffffffffff

def v451 (w : Vector (BitVec 64) 8) : BitVec 64 := (v447 w) - (v449 w)

def v453 (w : Vector (BitVec 64) 8) : BitVec 64 := BitVec.sshiftRight (v445 w) 63

def v455 (w : Vector (BitVec 64) 8) : BitVec 64 := (addSpec (v453 w) (v451 w)).1

def v457 (w : Vector (BitVec 64) 8) : BitVec 64 := (v362 w)

def v459 (w : Vector (BitVec 64) 8) : BitVec 64 := ~~~(v457 w)

def v461 (w : Vector (BitVec 64) 8) : BitVec 64 := (v449 w)

def v463 (w : Vector (BitVec 64) 8) : BitVec 64 := (v461 w) &&& (v459 w)

def v465 (w : Vector (BitVec 64) 8) : BitVec 64 := (v459 w) ||| (v449 w)

def v467 (w : Vector (BitVec 64) 8) : BitVec 64 := (v465 w) &&& (v455 w)

def v469 (w : Vector (BitVec 64) 8) : BitVec 64 := (v467 w) ||| (v463 w)

def v471 (w : Vector (BitVec 64) 8) : BitVec 64 := (v469 w) >>> 63

def v474 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0

def v476 (w : Vector (BitVec 64) 8) : BitVec 64 := (v474 w) - (v471 w)

def v478 (w : Vector (BitVec 64) 8) : BitVec 64 := ((((v365 w)).setWidth 8).setWidth 32).setWidth 64

def v482 (_w : Vector (BitVec 64) 8) : BitVec 64 := 0x11b864

private def graph0 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 53 => ⟨64, (v53 w)⟩
  | 55 => ⟨64, (v55 w)⟩
  | 57 => ⟨64, (v57 w)⟩
  | 59 => ⟨64, (v59 w)⟩
  | 60 => ⟨64, (v60 w)⟩
  | 62 => ⟨64, (v62 w)⟩
  | 64 => ⟨64, (v64 w)⟩
  | 66 => ⟨64, (v66 w)⟩
  | 68 => ⟨64, (v68 w)⟩
  | 69 => ⟨64, (v69 w)⟩
  | 71 => ⟨64, (v71 w)⟩
  | 73 => ⟨64, (v73 w)⟩
  | 75 => ⟨64, (v75 w)⟩
  | 77 => ⟨64, (v77 w)⟩
  | 79 => ⟨64, (v79 w)⟩
  | 81 => ⟨64, (v81 w)⟩
  | 82 => ⟨64, (v82 w)⟩
  | 84 => ⟨64, (v84 w)⟩
  | 85 => Value.ofBool (v85 w)
  | 88 => ⟨64, (v88 w)⟩
  | 89 => Value.ofBool (v89 w)
  | 91 => ⟨64, (v91 w)⟩
  | 93 => ⟨64, (v93 w)⟩
  | 95 => ⟨64, (v95 w)⟩
  | 96 => Value.ofBool (v96 w)
  | _ => ⟨1, 0⟩

private def graph1 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 98 => ⟨64, (v98 w)⟩
  | 100 => ⟨64, (v100 w)⟩
  | 101 => Value.ofBool (v101 w)
  | 103 => ⟨64, (v103 w)⟩
  | 105 => ⟨64, (v105 w)⟩
  | 107 => ⟨64, (v107 w)⟩
  | 109 => ⟨64, (v109 w)⟩
  | 110 => Value.ofBool (v110 w)
  | 112 => ⟨64, (v112 w)⟩
  | 114 => ⟨64, (v114 w)⟩
  | 116 => ⟨64, (v116 w)⟩
  | 117 => ⟨64, (v117 w)⟩
  | 119 => ⟨64, (v119 w)⟩
  | 121 => ⟨64, (v121 w)⟩
  | 123 => ⟨64, (v123 w)⟩
  | 125 => ⟨64, (v125 w)⟩
  | 126 => ⟨64, (v126 w)⟩
  | 128 => ⟨64, (v128 w)⟩
  | 130 => ⟨64, (v130 w)⟩
  | 131 => Value.ofBool (v131 w)
  | 133 => ⟨64, (v133 w)⟩
  | 135 => ⟨64, (v135 w)⟩
  | 137 => ⟨64, (v137 w)⟩
  | 138 => Value.ofBool (v138 w)
  | 140 => ⟨64, (v140 w)⟩
  | 142 => ⟨64, (v142 w)⟩
  | _ => ⟨1, 0⟩

private def graph2 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 144 => ⟨64, (v144 w)⟩
  | 145 => Value.ofBool (v145 w)
  | 147 => ⟨64, (v147 w)⟩
  | 149 => ⟨64, (v149 w)⟩
  | 151 => ⟨64, (v151 w)⟩
  | 152 => Value.ofBool (v152 w)
  | 154 => ⟨64, (v154 w)⟩
  | 156 => ⟨64, (v156 w)⟩
  | 158 => ⟨64, (v158 w)⟩
  | 159 => ⟨64, (v159 w)⟩
  | 161 => ⟨64, (v161 w)⟩
  | 163 => ⟨64, (v163 w)⟩
  | 165 => ⟨64, (v165 w)⟩
  | 167 => ⟨64, (v167 w)⟩
  | 168 => ⟨64, (v168 w)⟩
  | 170 => ⟨64, (v170 w)⟩
  | 172 => ⟨64, (v172 w)⟩
  | 173 => Value.ofBool (v173 w)
  | 175 => ⟨64, (v175 w)⟩
  | 177 => ⟨64, (v177 w)⟩
  | 179 => ⟨64, (v179 w)⟩
  | 180 => Value.ofBool (v180 w)
  | 182 => ⟨64, (v182 w)⟩
  | 184 => ⟨64, (v184 w)⟩
  | 185 => Value.ofBool (v185 w)
  | 187 => ⟨64, (v187 w)⟩
  | 189 => ⟨64, (v189 w)⟩
  | _ => ⟨1, 0⟩

private def graph3 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 191 => ⟨64, (v191 w)⟩
  | 192 => ⟨64, (v192 w)⟩
  | 194 => ⟨64, (v194 w)⟩
  | 196 => ⟨64, (v196 w)⟩
  | 198 => ⟨64, (v198 w)⟩
  | 199 => Value.ofBool (v199 w)
  | 201 => ⟨64, (v201 w)⟩
  | 203 => ⟨64, (v203 w)⟩
  | 204 => Value.ofBool (v204 w)
  | 206 => ⟨64, (v206 w)⟩
  | 208 => ⟨64, (v208 w)⟩
  | 210 => ⟨64, (v210 w)⟩
  | 213 => ⟨64, (v213 w)⟩
  | 214 => ⟨64, (v214 w)⟩
  | 216 => ⟨64, (v216 w)⟩
  | 218 => ⟨64, (v218 w)⟩
  | 220 => ⟨64, (v220 w)⟩
  | 222 => ⟨64, (v222 w)⟩
  | 223 => Value.ofBool (v223 w)
  | 225 => ⟨64, (v225 w)⟩
  | 227 => ⟨64, (v227 w)⟩
  | 229 => ⟨64, (v229 w)⟩
  | 231 => ⟨64, (v231 w)⟩
  | 232 => ⟨64, (v232 w)⟩
  | 234 => ⟨64, (v234 w)⟩
  | _ => ⟨1, 0⟩

private def graph4 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 236 => ⟨64, (v236 w)⟩
  | 238 => ⟨64, (v238 w)⟩
  | 240 => ⟨64, (v240 w)⟩
  | 242 => ⟨64, (v242 w)⟩
  | 243 => ⟨64, (v243 w)⟩
  | 245 => ⟨64, (v245 w)⟩
  | 246 => Value.ofBool (v246 w)
  | 249 => ⟨64, (v249 w)⟩
  | 250 => Value.ofBool (v250 w)
  | 252 => ⟨64, (v252 w)⟩
  | 254 => ⟨64, (v254 w)⟩
  | 256 => ⟨64, (v256 w)⟩
  | 257 => Value.ofBool (v257 w)
  | 259 => ⟨64, (v259 w)⟩
  | 261 => ⟨64, (v261 w)⟩
  | 262 => Value.ofBool (v262 w)
  | 264 => ⟨64, (v264 w)⟩
  | 266 => ⟨64, (v266 w)⟩
  | 268 => ⟨64, (v268 w)⟩
  | 269 => Value.ofBool (v269 w)
  | 271 => ⟨64, (v271 w)⟩
  | 273 => ⟨64, (v273 w)⟩
  | 275 => ⟨64, (v275 w)⟩
  | 277 => ⟨64, (v277 w)⟩
  | 278 => ⟨64, (v278 w)⟩
  | 280 => ⟨64, (v280 w)⟩
  | 281 => Value.ofBool (v281 w)
  | _ => ⟨1, 0⟩

private def graph5 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 283 => ⟨64, (v283 w)⟩
  | 285 => ⟨64, (v285 w)⟩
  | 287 => ⟨64, (v287 w)⟩
  | 288 => Value.ofBool (v288 w)
  | 290 => ⟨64, (v290 w)⟩
  | 292 => ⟨64, (v292 w)⟩
  | 293 => Value.ofBool (v293 w)
  | 295 => ⟨64, (v295 w)⟩
  | 297 => ⟨64, (v297 w)⟩
  | 299 => ⟨64, (v299 w)⟩
  | 300 => Value.ofBool (v300 w)
  | 302 => ⟨64, (v302 w)⟩
  | 304 => ⟨64, (v304 w)⟩
  | 305 => Value.ofBool (v305 w)
  | 307 => ⟨64, (v307 w)⟩
  | 309 => ⟨64, (v309 w)⟩
  | 311 => ⟨64, (v311 w)⟩
  | 313 => ⟨64, (v313 w)⟩
  | 315 => ⟨64, (v315 w)⟩
  | 316 => Value.ofBool (v316 w)
  | 318 => ⟨64, (v318 w)⟩
  | 320 => ⟨64, (v320 w)⟩
  | 321 => Value.ofBool (v321 w)
  | 323 => ⟨64, (v323 w)⟩
  | 325 => ⟨64, (v325 w)⟩
  | 327 => ⟨64, (v327 w)⟩
  | _ => ⟨1, 0⟩

private def graph6 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 329 => ⟨64, (v329 w)⟩
  | 330 => ⟨64, (v330 w)⟩
  | 332 => ⟨64, (v332 w)⟩
  | 334 => ⟨64, (v334 w)⟩
  | 336 => ⟨64, (v336 w)⟩
  | 338 => ⟨64, (v338 w)⟩
  | 339 => ⟨64, (v339 w)⟩
  | 341 => ⟨64, (v341 w)⟩
  | 342 => Value.ofBool (v342 w)
  | 344 => ⟨64, (v344 w)⟩
  | 346 => ⟨64, (v346 w)⟩
  | 348 => ⟨64, (v348 w)⟩
  | 349 => Value.ofBool (v349 w)
  | 351 => ⟨64, (v351 w)⟩
  | 353 => ⟨64, (v353 w)⟩
  | 354 => Value.ofBool (v354 w)
  | 356 => ⟨64, (v356 w)⟩
  | 357 => Value.ofBool (v357 w)
  | 359 => ⟨64, (v359 w)⟩
  | 360 => Value.ofBool (v360 w)
  | 362 => ⟨64, (v362 w)⟩
  | 363 => Value.ofBool (v363 w)
  | 365 => ⟨64, (v365 w)⟩
  | 368 => ⟨64, (v368 w)⟩
  | 371 => ⟨64, (v371 w)⟩
  | 373 => ⟨64, (v373 w)⟩
  | _ => ⟨1, 0⟩

private def graph7 (fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 375 => ⟨64, (v375 w)⟩
  | 378 => ⟨64, (fr.rsp - 112)⟩
  | 380 => ⟨64, (v380 w)⟩
  | 382 => ⟨64, (v382 w)⟩
  | 385 => ⟨64, (v385 w)⟩
  | 387 => ⟨64, (v387 w)⟩
  | 389 => ⟨64, (v389 w)⟩
  | 391 => ⟨64, (v391 w)⟩
  | 393 => ⟨64, (v393 w)⟩
  | 395 => ⟨64, (v395 w)⟩
  | 397 => ⟨64, (v397 w)⟩
  | 399 => ⟨64, (v399 w)⟩
  | 401 => ⟨64, (v401 w)⟩
  | 403 => ⟨64, (v403 w)⟩
  | 405 => ⟨64, (v405 w)⟩
  | 407 => ⟨64, (v407 w)⟩
  | 409 => ⟨64, (v409 w)⟩
  | _ => ⟨1, 0⟩

private def graph8 (_fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 412 => ⟨64, (v412 w)⟩
  | 414 => ⟨64, (v414 w)⟩
  | 416 => ⟨64, (v416 w)⟩
  | 418 => ⟨64, (v418 w)⟩
  | 420 => ⟨64, (v420 w)⟩
  | 422 => ⟨64, (v422 w)⟩
  | 424 => ⟨64, (v424 w)⟩
  | 426 => ⟨64, (v426 w)⟩
  | 428 => ⟨64, (v428 w)⟩
  | 430 => ⟨64, (v430 w)⟩
  | 432 => ⟨64, (v432 w)⟩
  | 434 => ⟨64, (v434 w)⟩
  | 436 => ⟨64, (v436 w)⟩
  | 438 => ⟨64, (v438 w)⟩
  | 440 => ⟨64, (v440 w)⟩
  | 443 => ⟨64, (v443 w)⟩
  | 445 => ⟨64, (v445 w)⟩
  | 447 => ⟨64, (v447 w)⟩
  | 449 => ⟨64, (v449 w)⟩
  | _ => ⟨1, 0⟩

private def graph9 (fr : Activation) (w : Vector (BitVec 64) 8) : Nat → Value
  | 451 => ⟨64, (v451 w)⟩
  | 453 => ⟨64, (v453 w)⟩
  | 455 => ⟨64, (v455 w)⟩
  | 457 => ⟨64, (v457 w)⟩
  | 459 => ⟨64, (v459 w)⟩
  | 461 => ⟨64, (v461 w)⟩
  | 463 => ⟨64, (v463 w)⟩
  | 465 => ⟨64, (v465 w)⟩
  | 467 => ⟨64, (v467 w)⟩
  | 469 => ⟨64, (v469 w)⟩
  | 471 => ⟨64, (v471 w)⟩
  | 474 => ⟨64, (v474 w)⟩
  | 476 => ⟨64, (v476 w)⟩
  | 478 => ⟨64, (v478 w)⟩
  | 480 => ⟨64, (fr.rsp - 128)⟩
  | 482 => ⟨64, (v482 w)⟩
  | _ => ⟨1, 0⟩

def values (a : Registers) (fr : Activation) (w : Vector (BitVec 64) 8) (i : Nat) : Value :=
  if h : i < 53 then a[i]'h else
  if i < 98 then graph0 fr w i else
  if i < 144 then graph1 fr w i else
  if i < 191 then graph2 fr w i else
  if i < 236 then graph3 fr w i else
  if i < 283 then graph4 fr w i else
  if i < 329 then graph5 fr w i else
  if i < 375 then graph6 fr w i else
  if i < 412 then graph7 fr w i else
  if i < 451 then graph8 fr w i else
  graph9 fr w i

def memoryAtoms (fr : Activation) (w : Vector (BitVec 64) 8) : Nat → List Atom
  | 53 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 98 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v84 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 144 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v84 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 191 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v84 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 236 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v84 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v73 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 283 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v245 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v73 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 329 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v245 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v73 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 375 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 104) 64 ((v353 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v368 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe)]
  | 412 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 112) 64 ((v409 w)),
      .mem (fr.rsp - 104) 64 ((v353 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v368 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe),
      .mem (fr.rsp - 64) 64 ((v356 w))]
  | 451 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 112) 64 ((v440 w)),
      .mem (fr.rsp - 104) 64 ((v353 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v368 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe),
      .mem (fr.rsp - 64) 64 ((v356 w))]
  | 483 => [.writable (fr.rsp - 129) 129,
      .readable fr.rsi 64,
      .mem fr.rsi 64 w[0],
      .mem (fr.rsi + 8) 64 w[1],
      .mem (fr.rsi + 16) 64 w[2],
      .mem (fr.rsi + 24) 64 w[3],
      .mem (fr.rsi + 32) 64 w[4],
      .mem (fr.rsi + 40) 64 w[5],
      .mem (fr.rsi + 48) 64 w[6],
      .mem (fr.rsi + 56) 64 w[7],
      .mem (fr.rsp - 128) 64 (0x11b864),
      .mem (fr.rsp - 112) 64 ((v471 w)),
      .mem (fr.rsp - 104) 64 ((v353 w)),
      .mem (fr.rsp - 96) 64 (0xffffffffffffffff),
      .mem (fr.rsp - 88) 64 ((v368 w)),
      .mem (fr.rsp - 80) 64 (0xbaaedce6af48a03b),
      .mem (fr.rsp - 72) 64 (0xfffffffffffffffe),
      .mem (fr.rsp - 64) 64 ((v356 w))]
  | _ => []

def writeRegions (fr : Activation) : List MemoryRegion := [⟨fr.rsp.toNat - 128, 72⟩]

def Segment {j k : Nat} (a : Registers) (fr : Activation) (w : Vector (BitVec 64) 8)
    (b : Block Op Label signature Reg.count j) (t : Block Op Label signature Reg.count k) : Prop :=
  BodySegment Extracted.programImage (values a fr w)
    (fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n)) (writeRegions fr) b t

def barrier : Block Op Label signature Reg.count 483 :=
  .terminate (.call ⟨.l127d50, RegMap.args [(0, 356), (1, 378), (2, 471), (3, 362), (4, 480), (5, 455), (6, 463), (7, 478), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 476), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)] 483⟩ { target := .l11b864, kept := #v[], arity := rfl, guard := some (Fin.last 482) })

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
