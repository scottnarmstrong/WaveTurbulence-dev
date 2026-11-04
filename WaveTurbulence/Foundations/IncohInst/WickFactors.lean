/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleLinkCoordinates
public import WaveTurbulence.Foundations.IncohInst.TreeLinkCoordinates
public import WaveTurbulence.Foundations.Incoh.LinkFactor

/-! # Exact squared source Wick factors, including paired trees (F62) -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The literal source coefficient at any branching node, for any forest width. -/
@[expose] def sourceNodeWick {w d : ℕ} {G : Garden w}
    (κ : GNode G.tree → Fin d → ℤ) (b : GBranch G.tree) : ℝ :=
  epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))

/-- The analytic single-node Wick coefficient is exactly C2's source coefficient. -/
theorem epsXY_eq_linkEpsilon {d : ℕ} (x y : Fin d → ℤ) : epsXY x y = linkEpsilon x y := by
  rw [epsXY_eq_cases, linkEpsilon_eq_source]

/-- Multiplying each link coordinate by a unit sign preserves the source Wick coefficient. -/
theorem epsXY_units {d : ℕ} (x y : Fin d → ℤ) (s t : ℤˣ) :
    epsXY ((s : ℤ) • x) ((t : ℤ) • y) = epsXY x y := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [epsXY_eq_cases]

/-- Interchanging the two link coordinates preserves the source Wick coefficient. -/
theorem epsXY_swap {d : ℕ} (x y : Fin d → ℤ) : epsXY x y = epsXY y x := by
  simp only [epsXY_eq_cases, and_comm, or_comm]

/-- The exact couple Wick product uses the square required by F62. -/
theorem couple_epsDec_eq_linkWickFactor {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {d : ℕ} {κ : GNode G.tree → Fin d → ℤ} (hκ : IsDecoration G κ) :
    epsDec G κ = ∏ j, linkWickFactor (xNode κ (chosenBranch hQ j)) (yNode κ (chosenBranch hQ j)) := by
  rw [epsDec_eq_prod_links hQ hQ.1 hκ]
  apply Finset.prod_congr rfl
  intro j _
  rw [show chosenNode Q j = (chosenBranch hQ j).1 from rfl, xv_extend, yv_extend,
    epsXY_eq_linkEpsilon]
  rfl

/-- The two endpoints of every actual tree link have the same source Wick coefficient. -/
theorem tree_sourceNodeWick_link {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {d : ℕ} {κ : GNode G.tree → Fin d → ℤ} (hκ : IsDecoration G κ)
    (j : Fin (X.treeLinks (G.sig 0)).length) :
    sourceNodeWick κ (treeLinkBranch hX j 1) = sourceNodeWick κ (treeLinkBranch hX j 0) := by
  obtain ⟨s, t, hxy, _⟩ := tree_xy_link hX hκ (List.get_mem (X.treeLinks (G.sig 0)) j)
    (treeLinkBranch hX j 0) (treeLinkBranch hX j 1) rfl rfl
  have he (b : GBranch G.tree) : sourceNodeWick κ b = epsXY (xNode κ b) (yNode κ b) :=
    epsCoef_eq_epsXY _ _ _ _ (hκ.1 b)
  rw [he, he]
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy, epsXY_units]
  · rw [hx, hy, epsXY_units, epsXY_swap]

/-- The paired-tree source also contributes exactly one squared Wick factor per link. -/
theorem tree_epsDec_eq_linkWickFactor {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {d : ℕ} {κ : GNode G.tree → Fin d → ℤ} (hκ : IsDecoration G κ) :
    epsDec G κ = ∏ j, linkWickFactor (xNode κ (treeChosenBranch hX j))
      (yNode κ (treeChosenBranch hX j)) := by
  change (∏ b : GBranch G.tree, sourceNodeWick κ b) = _
  rw [← (treeLinkEquiv hX).prod_comp (sourceNodeWick κ), Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.prod_univ_two]
  change sourceNodeWick κ (treeLinkBranch hX j 0) * sourceNodeWick κ (treeLinkBranch hX j 1) = _
  rw [tree_sourceNodeWick_link hX hκ]
  have he : sourceNodeWick κ (treeLinkBranch hX j 0) =
      epsXY (xNode κ (treeChosenBranch hX j)) (yNode κ (treeChosenBranch hX j)) :=
    epsCoef_eq_epsXY _ _ _ _ (hκ.1 (treeLinkBranch hX j 0))
  rw [he, epsXY_eq_linkEpsilon]
  exact (pow_two _).symm

end WaveTurbulence.IncohInst
