/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a supplement to the port of main `WaveTurbulence.Foundations.Vine.A.VineGroupCandidateMap` (by hand): DV′.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupCandidateMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.MolIso
import Mathlib.Tactic
/-! # Transport of DV′ candidates along molecule isomorphisms (main's `dvCandidate_map(_iff)`, `dvCandidateEquiv`)

Over `𝒱_γ` a DV′ candidate also carries `σ(a, b) = 1`, which transports by `sigma_molIso`; the two constituents are
members of `𝒱_γ`, which transport by `isSomeVine_molIso`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G H : Garden w} {γ : ℝ} [Fact (γ ≤ 1 / 2)]

/-- Every valid DV′ constituent is carried to a valid whole constituent. -/
theorem dvCandidate_map (F : MolIso G.molecule H.molecule) {S : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (h : DVCandidate γ G S t) :
    DVCandidate γ H (F.img S) (dvTripleEquiv F t) := by
  obtain ⟨hσ, B, hA, hB, hI, hS⟩ := h
  have hAB := Src.isBlock_of_isSomeVine hA
  refine ⟨?_, F.img B, isSomeVine_molIso F hA, isSomeVine_molIso F hB, ?_, ?_⟩
  · change H.molecule.sigma (F.e t.2.1) (F.e t.2.2) = 1
    rw [sigma_molIso F (hAB.1 hAB.2.1) (hAB.1 hAB.2.2.1)]
    exact hσ
  · change F.img t.1 ∩ F.img B = {F.e t.2.1, F.e t.2.2}
    rw [← F.img_inter, hI]
    simp only [MolIso.img, Finset.image_insert, Finset.image_singleton]
  · change F.img S = F.img t.1 ∪ F.img B
    rw [hS, F.img_union]

/-- Validity is also reflected for every DV′ triple. -/
theorem dvCandidate_map_iff (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree))
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) :
    DVCandidate γ H (F.img S) (dvTripleEquiv F t) ↔ DVCandidate γ G S t := by
  refine ⟨fun h => ?_, dvCandidate_map F⟩
  have hh := dvCandidate_map F.symm h
  change DVCandidate γ G (F.symm.img (F.img S))
    (F.symm.img (F.img t.1), F.e.symm (F.e t.2.1), F.e.symm (F.e t.2.2)) at hh
  rw [F.img_img_symm, F.img_img_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hh
  exact hh

/-- The complete DV′ candidate carriers are bijective. -/
def dvCandidateEquiv (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree)) :
    {t // DVCandidate γ G S t} ≃ {t // DVCandidate γ H (F.img S) t} :=
  (dvTripleEquiv F).subtypeEquiv (fun t => (dvCandidate_map_iff F S t).symm)

end WaveTurbulence.GammaLow.Fama.VineA
