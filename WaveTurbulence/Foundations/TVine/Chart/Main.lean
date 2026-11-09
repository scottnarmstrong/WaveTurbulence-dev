/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.GlueChart
public import WaveTurbulence.Foundations.TVine.Chart.Family

/-!
# The generic chart theorem (M4 Theorem C)

`tvineChart_of_decomp`: if every T-vine has a cell decomposition whose cells are its pieces, then every T-vine has a
de-indexed full chart with groups = pieces (`TVineChartStatement`), and the whole `𝒱_γ` family has charts
(`VineGammaChartStatement`). The existence of the decomposition (`DecompExists`) is derived from the piece structure
(N3 Theorem 6, N2 Prop 1.17(b), M4 Lemma A) in `Chart.Derive*`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Chart

/-- Every T-vine (with either joint as the upper joint `a`) has a cell decomposition whose cells are its pieces. -/
def DecompExists : Prop :=
  ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    ∀ (S : Finset V) (a b : V), M.IsTVine S a b →
      ∃ Dc : Decomp M S a b, Dc.cellGroups = M.tvineGroups S a b

/-- **M4 Theorem C from the cell decompositions.** -/
theorem tvineChart_of_decomp (h : DecompExists) : TVineChartStatement := by
  intro V D _ _ _ M hM S a b hT
  obtain ⟨Dc, hg⟩ := h V D M hM S a b hT
  exact ⟨Dc.toFullChart hM hT.1, by rw [Dc.chartGroups_toFullChart hM hT.1, hg]⟩

/-- **The `𝒱_γ` chart contract from the cell decompositions.** -/
theorem vineGammaChart_of_decomp (h : DecompExists) : VineGammaChartStatement :=
  vineGammaChart_of_tvine (tvineChart_of_decomp h).exists

end WaveTurbulence.TVine.Chart
