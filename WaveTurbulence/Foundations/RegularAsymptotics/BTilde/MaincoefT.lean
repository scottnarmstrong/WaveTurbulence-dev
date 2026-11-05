/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.BridgeTree
public import WaveTurbulence.Foundations.ClassJR.MCProp51T

/-!
# DH21 Proposition 5.1 for regular trees, through gardens (DH21 Proposition 6.10)

The code-defined `Ã_𝒯` of the B̃ bridge (`chainAtilde`) is ClassJR's `RegChain.At` at the root
`rootT ζ` (`chainAtilde_eq_At`), so DH21 Proposition 5.1 for regular trees (`RegChain.maincoefT_DH23`,
with the identity for `0 ≤ s < t ≤ 1`) holds for it (`maincoefT_DH23_B2`). Through gardens
(`maincoefT_garden_DH23`): every regular tree has a unique well-formed code, its garden coefficient
`𝒜*_𝒯` (DH21 (varat)) is `Ã_𝒯` for `s < t` under the link relation, and `Ã_𝒯` has the expansion
(maincoef3) for `t > s` with the DH23 weights. `hstructT` is the named obligation
`existsUnique_regChain_decodesTree` (REG-STRUCT, statement verbatim), discharged in
`check/RegStructDischarge.lean`.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

theorem chainAtilde_eq_At (X : RegChain) (ζ : ℤˣ) :
    chainAtilde X ζ = (toJRc X).At ζ (rootT ζ) := rfl

/-- **DH21 Proposition 5.1 for a regular tree code** (B2 code, DH23 weights, for `t > s`). -/
theorem maincoefT_DH23_B2 {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) :
    ClassJR.MCExpT (1 - η / 8) (η / 4) (1 - η / 2) A (ClassJR.CTη η ^ (2 * X.size + 1))
      ClassJR.nodeSgn (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))) (chainAtilde X ζ) := by
  have h := ClassJR.RegChain.maincoefT_DH23 hη hη2 hA (toJRc X) (by rw [wf_toJRc]; exact hX) ζ
    (rootT ζ)
  rw [size_toJRc] at h
  exact h

/-- **DH21 Proposition 5.1 for regular trees through gardens** (DH23 weights). `hstructT` is the
named obligation `existsUnique_regChain_decodesTree` (REG-STRUCT, statement verbatim). -/
theorem maincoefT_garden_DH23
    (hstructT : ∀ G : Garden 1, IsRegularTree G → ∃! X : RegChain, X.wf = true ∧ X.DecodesTree G)
    {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A) (G : Garden 1)
    (hG : IsRegularTree G) :
    ∃! X : RegChain, (X.wf = true ∧ X.DecodesTree G) ∧
      (∀ α : Fin 1 × TTree.Path → ℝ,
        (∀ l ∈ (toJRc X).linksAt (G.sig 0) (rootT (G.sig 0)), LinkRel (liftT α) l) →
        ∀ t s : ℝ, 0 ≤ t → s < t → treeAstar G t s α = chainAtilde X (G.sig 0) (liftT α) t s) ∧
      ClassJR.MCExpT (1 - η / 8) (η / 4) (1 - η / 2) A (ClassJR.CTη η ^ (2 * X.size + 1))
        ClassJR.nodeSgn (ClassJR.chosenSet ((toJRc X).linksAt (G.sig 0) (rootT (G.sig 0))))
        (chainAtilde X (G.sig 0)) := by
  obtain ⟨X, hX, huniq⟩ := hstructT G hG
  exact ⟨X, ⟨hX, fun α hα t s ht hst => treeAstar_eq_Atilde hX.2 hα ht hst,
    maincoefT_DH23_B2 hη hη2 hA X hX.1 (G.sig 0)⟩, fun X' hX' => huniq X' hX'.1⟩

end WaveTurbulence.MainCoef
