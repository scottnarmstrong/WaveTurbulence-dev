/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafGardenDecoration
public import WaveTurbulence.Foundations.XChain.UnmarkedPhaseIntegral
/-! The exact kernel of a plain zero-order garden, including its pairing indicator. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped Classical

theorem leafGarden_phaseIntegral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (ht : ∀ j, LG.garden.tree j = TTree.leaf) (hplain : LG.garden.IsPlain)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : GNode LG.garden.tree → Mom d) :
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s k = 1 := by
  haveI := leafForest_no_branch LG.garden.tree ht
  have hD : kDomain LG up s = Set.univ := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro b
    exact isEmptyElim b
  rw [phaseIntegral_of_plain L γ δ LG.garden hplain, hD, Set.indicator_univ]
  have hv : (volume : Measure (GBranch LG.garden.tree → ℝ)).real Set.univ = 1 := by
    change (Measure.pi (fun _ : GBranch LG.garden.tree => (volume : Measure ℝ))).real Set.univ = 1
    simp only [measureReal_def, Measure.pi_univ, Finset.univ_eq_empty, prod_empty, ENNReal.toReal_one]
  simp only [phaseProd, Finset.univ_eq_empty, prod_empty, integral_const, hv, one_smul]

theorem kernelK_leafGarden {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (ht : ∀ j, LG.garden.tree j = TTree.leaf) (hplain : LG.garden.IsPlain)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F LG up s k₀ n nfl =
      if LeafRootMatched LG.garden n then ∏ l ∈ inputLeaves LG.garden,
        (F (LG.layer l.toNode) (k₀ + latticePoint L (n l.1.1)) : ℂ) else 0 := by
  classical
  haveI := leafForest_no_branch LG.garden.tree ht
  haveI := leafGenDecoration_subsingleton LG.garden ht n nfl
  have hz : LG.garden.zeta = 1 := by simp [Garden.zeta]
  have heps (κ : GenDecoration LG.garden d n nfl) : epsDec LG.garden κ.1 = 1 := by simp [epsDec]
  have hp (κ : GenDecoration LG.garden d n nfl) :=
    leafGarden_phaseIntegral L γ δ LG ht hplain up s (cosetDecoration LG.garden L k₀ κ.1)
  rw [kernelK, leafForest_garden_order LG.garden ht, pow_zero, hz, one_mul]
  simp_rw [heps, Complex.ofReal_one, hp, one_mul]
  by_cases hm : LeafRootMatched LG.garden n
  · rw [ite_eq_left hm]
    let κ := leafGenDecoration LG.garden ht hplain n nfl hm
    rw [tsum_eq_single κ (fun b hb => False.elim (hb (Subsingleton.elim _ _)))]
    rfl
  · haveI : IsEmpty (GenDecoration LG.garden d n nfl) :=
      ⟨fun κ => hm (leafRootMatched_of_decoration LG.garden ht n nfl κ)⟩
    rw [tsum_empty, ite_eq_right hm]

end WaveTurbulence.Induct
