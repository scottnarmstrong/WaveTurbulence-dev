/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeTimeExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeMain
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.BtRecB
public import WaveTurbulence.Foundations.IncohInst.Links.Param

/-! # The actual tree pair coefficient families have the landed regularized limits -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ClassJR Cancel MainCoef Links

/-- Tree chosen nodes are distinct at their literal sign root. -/
theorem tree_chosen_nodup_at_root (X : RegChain) (ζ : ℤˣ) :
    ((X.linksAt ζ (rootT ζ)).map Prod.fst).Nodup := by
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · simpa [rootT, RegCpl.links, RegCpl.linksAt, RegChain.linksAt] using
      Links.chosen_nodup (RegCpl.type2 X RegChain.nil RegCpl.triv)
  · simpa [rootT, RegCpl.links, RegCpl.linksAt, RegChain.linksAt] using
      Links.chosen_nodup (RegCpl.type2 RegChain.nil X RegCpl.triv)

/-- Original source pair data, placed at the exact sign root of the tree. -/
def treePairData (X : RegChain) (ζ : ℤˣ) : List PairDatum := chainData X ζ (rootT ζ)

/-- The actual chosen pair coefficients, including their source time swaps. -/
def treePairCoefficient (X : RegChain) (ζ : ℤˣ) (j : ℕ) : TCoef :=
  pairF BtJR ((treePairData X ζ).getD j dfltP) (swAt X ζ 0 j)

/-- Their original independent source energy variables. -/
def treePairVariables (X : RegChain) (ζ : ℤˣ) (j : ℕ) : Finset Cancel.Addr :=
  pairVars ((treePairData X ζ).getD j dfltP)

/-- The limits already proved for the two actual constituent couple coefficients. -/
def treePairLimit (Z : Finset Cancel.Addr) (X : RegChain) (ζ : ℤˣ) (j : ℕ) : ℝ → ℝ → ℂ :=
  pairJsw Z ((treePairData X ζ).getD j dfltP) (swAt X ζ 0 j)

/-- Every actual pair coefficient, including the harmless default outside the finite
chain, consumes the landed couple regularization theorem with no added hypothesis. -/
theorem regCoef_treePair (Z : Finset Cancel.Addr) (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ)
    (j : ℕ) : RegCoef zetaA Z (treePairVariables X ζ j) (treePairCoefficient X ζ j)
      (treePairLimit Z X ζ j) := by
  unfold treePairVariables treePairCoefficient treePairLimit treePairData
  by_cases hj : j < (chainData X ζ (rootT ζ)).length
  · rw [List.getD_eq_getElem _ _ hj]
    exact regCoef_chain btRec_BtJR Z X ζ (rootT ζ) hwf (tree_chosen_nodup_at_root X ζ) _
      (List.getElem_mem hj) (swAt X ζ 0 j)
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    exact regCoef_dflt btRec_BtJR Z (swAt X ζ 0 j)

/-- The original finite family supplies a uniform square bound before any Gaussian parameter. -/
theorem exists_treePairCoefficient_bound (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j α, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖treePairCoefficient X ζ j α t s‖ ≤ B := by
  choose B hB using fun j => (regCoef_treePair ∅ X hwf ζ j).nice.bdd
  let M := (∑ j ∈ Finset.range (treePairData X ζ).length, max (B j) 0)+1
  have hm : 0 ≤ ∑ j ∈ Finset.range (treePairData X ζ).length, max (B j) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨M,by dsimp only [M]; positivity,?_⟩
  intro j α t ht s hs
  by_cases hj : j < (treePairData X ζ).length
  · have hsingle := Finset.single_le_sum (f := fun j => max (B j) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_range.mpr hj)
    exact (hB j α t ht s hs).trans ((le_max_left _ _).trans
      (hsingle.trans (le_add_of_nonneg_right zero_le_one)))
  · unfold treePairCoefficient
    rw [List.getD_eq_default _ _ (not_lt.mp hj), pairF_dflt btRec_BtJR]
    simp only [norm_one]
    change 1 ≤ (∑ j ∈ Finset.range (treePairData X ζ).length, max (B j) 0)+1
    linarith only [hm]

end WaveTurbulence.RegAsymp
