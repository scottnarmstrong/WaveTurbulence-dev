/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.SigmaBridge
public import WaveTurbulence.Foundations.Flower.MkMark.SigmaCrown

/-! # B2b-3 MK-MARK (c): zero weight for stem-unclean pairs under main's σ-restriction

`weight_zero_of_unclean` (StemZero) needs, on the selection, a crown gap `‖k(u₂₁) − k(u₂₂)‖ < ‖k_root‖/2` at the
lower joint `u₂` of the core vine. Here it is derived from main's σ-restriction on the collapsed skeleton decoration:

* `weight_zero_of_unclean_vinesV0`: the selection carries a skeleton integer decoration `z` with
  `selOf (ofPrescription σ) L γ η base z` and `skDec A k = k₀ + z/L`; the core vine `u` is (the atom set of) a vine of
  `vinesV0 A.skeleton σ`; the root is high, `L^{-γ+η} < ‖k_root‖/2`.
* `weight_zero_of_unclean_collapsed`: the same with `z` the collapse (`collapseGenDecoration`) of an integer
  decoration `κ` of the decoded garden and `k = k₀ + κ/L` — the form in which main's Stage-1 selections are stated. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- **σ-bridge, ingredient form.** The gap of a CL vine ingredient on the atoms of a `𝒱₀(σ)` vine is SG. -/
theorem ingredient_gap_SG_of_vinesV0 {G : Garden w} (hp : G.IsPlain) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) (σ : Prescription G)
    (hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z)
    {V : Stage1.CLVine G} (hV : V ∈ vinesV0 G σ) (B : CLVineIngredient G) (hVB : V.atoms = B.atoms) (k₀ : Mom d) :
    B.gap (cosetDecoration G L k₀ z) ≠ 0 ∧ ‖B.gap (cosetDecoration G L k₀ z)‖ ≤ L ^ (-γ + η) :=
  crown_gap_le_of_vinesV0 hp hL γ η base z hz σ hsel hV hVB B.vine.1 B.region k₀

/-- **σ-bridge, chain form.** Along a CL vine chain one of whose ingredients lies on a `𝒱₀(σ)` vine, every ingredient
has an SG gap. -/
theorem chain_gap_SG_of_vinesV0 {G : Garden w} (hp : G.IsPlain) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) (σ : Prescription G)
    (hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z)
    (A₀ : CLVineIngredient G) (rest : List (CLVineIngredient G)) (hc : (A₀ :: rest).IsChain CLVineIngredient.Follows)
    {V : Stage1.CLVine G} (hV : V ∈ vinesV0 G σ) {B₀ : CLVineIngredient G} (hB₀ : B₀ ∈ A₀ :: rest)
    (hVB : V.atoms = B₀.atoms) (k₀ : Mom d) (B : CLVineIngredient G) (hB : B ∈ A₀ :: rest) :
    B.gap (cosetDecoration G L k₀ z) ≠ 0 ∧ ‖B.gap (cosetDecoration G L k₀ z)‖ ≤ L ^ (-γ + η) := by
  have hdec := LGSpine.isDecoration_cosetDecoration G L k₀ z hz
  obtain ⟨h0, h1⟩ := ingredient_gap_SG_of_vinesV0 hp hL γ η base z hz σ hsel hV B₀ hVB k₀
  rw [clVineChain_gap_eq A₀ rest hc _ hdec B hB, ← clVineChain_gap_eq A₀ rest hc _ hdec B₀ hB₀]
  exact ⟨h0, h1⟩

/-- **Zero weight for stem-unclean pairs under the σ-restriction.** -/
theorem weight_zero_of_unclean_vinesV0 {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 → (∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (σ : Prescription A.skeleton)
    (hu : ∃ V ∈ vinesV0 A.skeleton σ, V.atoms = u.atoms)
    (hSel : ∀ k, Sel k → ∃ (z : GNode A.skeleton.tree → (Fin d → ℤ)) (k₀ : Mom d), IsDecoration A.skeleton z ∧
      VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z ∧
      skDec A k = cosetDecoration A.skeleton L k₀ z)
    (hθ : ∀ k, Sel k → L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean A J u hun p N r hr0 hU hlay hfl hN W Sel hW ?_
  intro k hk
  obtain ⟨z, k₀, hz, hsel, he⟩ := hSel k hk
  obtain ⟨V, hV, hVU⟩ := hu
  rw [crown_gap_skDec, he]
  exact lt_of_le_of_lt (crown_gap_le_of_vinesV0 A.prime.1 hL γ η base z hz σ hsel hV hVU u.isBlock
    (VineB.regionOf u) k₀).2 (hθ k hk)

/-- The skeleton reading of a coset decoration of the decoded garden is the coset decoration of the collapse. -/
theorem skDec_coset_collapse {LG : LayeredGarden w} (A : VineA.PrimeData LG) {d : ℕ} {n : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration (A.data.garden A.prime.1) d n nfl) (L : ℝ) (k₀ : Mom d)
    (k : GNode LG.garden.tree → Mom d) (hk : ∀ x, k x = k₀ + latticePoint L (ofForest A κ.1 x)) :
    skDec A k = cosetDecoration A.skeleton L k₀ (collapseGenDecoration A.data A.prime.1 κ).1 := by
  funext a
  have h1 := collapseGenDecoration_skDec A κ a
  show k _ = k₀ + latticePoint L _
  rw [h1]
  exact hk _

/-- **Zero weight for stem-unclean pairs, collapsed form.** The selection is main's Stage-1 σ-restriction on the
collapse of an integer decoration `κ` of the decoded garden, with momenta `k = k₀ + κ/L`. -/
theorem weight_zero_of_unclean_collapsed {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 → (∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (σ : Prescription A.skeleton)
    (hu : ∃ V ∈ vinesV0 A.skeleton σ, V.atoms = u.atoms) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (hSel : ∀ k, Sel k → ∃ (κ : GenDecoration (A.data.garden A.prime.1) d n nfl) (k₀ : Mom d),
      VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base
        (collapseGenDecoration A.data A.prime.1 κ).1 ∧
      ∀ x, k x = k₀ + latticePoint L (ofForest A κ.1 x))
    (hθ : ∀ k, Sel k → L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean_vinesV0 A J u hun p N r hr0 hU hlay hfl hN W Sel hW hL γ η base σ hu ?_ hθ
  intro k hk
  obtain ⟨κ, k₀, hsel, he⟩ := hSel k hk
  exact ⟨(collapseGenDecoration A.data A.prime.1 κ).1, k₀, (collapseGenDecoration A.data A.prime.1 κ).2.1, hsel,
    skDec_coset_collapse A κ L k₀ k he⟩

end WaveTurbulence.Flower.MkMark
