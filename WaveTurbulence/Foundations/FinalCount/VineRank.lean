/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDev
/-! Vine removal, part 5 (FINALCOUNT-G2): the characteristic change of removing a VC (DH23 L1799: `Δχ = -m`).
`χ(M) - χ(post) = χ(VC) + 2 - ΔF - F(VC)`, `ΔF = F(post) - F(M)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace VineCut
variable {M : Molecule V D} (K : VineCut M)

theorem circuitRank_diff :
    M.circuitRank - K.post.circuitRank =
      K.vc.circuitRank + 2 - (((K.post.numComponents : ℤ) - M.numComponents)) - K.vc.numComponents := by
  have h1 := circuitRank_cut_eq M K.cut_a
  have h2 := circuitRank_cut_eq K.m1 K.cut_b
  have h3 := circuitRank_restrictP_add K.cutMol (fun a => a ∉ K.C.atoms) K.closed
  have h4 := numComponents_restrictP_add K.cutMol (fun a => a ∉ K.C.atoms) K.closed
  change K.post.circuitRank + K.vc.circuitRank = K.cutMol.circuitRank at h3
  change K.post.numComponents + K.vc.numComponents = K.cutMol.numComponents at h4
  change K.m1.circuitRank = M.circuitRank - 1 + ((K.m1.numComponents : ℤ) - M.numComponents) at h1
  change K.cutMol.circuitRank = K.m1.circuitRank - 1 + ((K.cutMol.numComponents : ℤ) - K.m1.numComponents) at h2
  have h4' : (K.post.numComponents : ℤ) + K.vc.numComponents = K.cutMol.numComponents := by exact_mod_cast h4
  linarith

end VineCut
end WaveTurbulence.FinalCount
