/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FiltLink.Lemma141
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
/-! # D5a FILT-LINK: `ProtDefs.filtWeight` factors into link multipliers

The two filter layers of the D5 exports, `filtWeight F ann M κ * filtWeight Fu false Mu κ`, factor over any family
of pairwise disjoint link blocks covering `F ∪ Fu`, each block contributing `linkFiltWeight` at its own bilinear
frequency, as soon as every branch of block `j` has `|Ω| = |2 u_j|` (on a decoration: `omegaNode_eq` and
`abs_omega_eq_of_signed` of the linked partner). This is the per-link form that Lemma 14.1
(`exists_filtLink_decay`, `exists_filtLink_trivial`) consumes. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

variable {w d : ℕ} {G : Garden w}

theorem filtWeight_eq_prod (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    ProtDefs.filtWeight F ann M κ =
      ∏ b ∈ F, (((if ann b then FlShell.chiD else chi0) (|omegaNode G κ b| / M b) : ℝ) : ℂ) := rfl

/-- **`filtWeight` on a link block** with `|Ω| = |2u|`: the two layers restricted to the block are `linkFiltWeight`. -/
theorem filtWeight_block_eq (κ : GNode G.tree → Mom d)
    (E F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) (u : ℝ)
    (hE : ∀ b ∈ E, |omegaNode G κ b| = |2 * u|) :
    ProtDefs.filtWeight (F ∩ E) ann M κ * ProtDefs.filtWeight (Fu ∩ E) (fun _ => false) Mu κ =
      linkFiltWeight E F Fu ann M Mu u := by
  rw [filtWeight_eq_prod, filtWeight_eq_prod]
  exact prod_filtFactor_two_eq E F Fu ann M Mu u hE

/-- **Link factorization of the two filter layers**: over pairwise disjoint link blocks `E j` (`j ∈ J`) covering
`F ∪ Fu`, with `|Ω_b| = |2 u_j|` on block `j`, the D5 multiplier `filtWeight F ann M * filtWeight Fu false Mu` is
`∏_j linkFiltWeight (E j) F Fu ann M Mu (u j)`. -/
theorem filtWeight_two_eq_prod_links {ι : Type*} (κ : GNode G.tree → Mom d)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ)
    (J : Finset ι) (E : ι → Finset (GBranch G.tree)) (u : ι → ℝ)
    (hdisj : (J : Set ι).PairwiseDisjoint E) (hF : F ⊆ J.biUnion E) (hFu : Fu ⊆ J.biUnion E)
    (hΩ : ∀ j ∈ J, ∀ b ∈ E j, |omegaNode G κ b| = |2 * u j|) :
    ProtDefs.filtWeight F ann M κ * ProtDefs.filtWeight Fu (fun _ => false) Mu κ =
      ∏ j ∈ J, linkFiltWeight (E j) F Fu ann M Mu (u j) := by
  rw [filtWeight_eq_prod, filtWeight_eq_prod, prod_filtFactor_eq_prod_blocks κ F ann M J E hdisj hF,
    prod_filtFactor_eq_prod_blocks κ Fu (fun _ => false) Mu J E hdisj hFu, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  exact prod_filtFactor_two_eq (E j) F Fu ann M Mu (u j) (hΩ j hj)

end WaveTurbulence.Flower.FiltLink
