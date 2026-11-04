/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeLocalization

/-!
# Momentum-uniform finite localization for actual couples

Every couple leaf is a source input, including the leaf of a trivial tree.
There is no root-valued lone leaf. Hence the finite center cover depends
only on the input-cell indices and can be fixed before all root momenta.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- When every leaf is an input, the source leaf centers are independent of root momentum. -/
theorem MomentumTreeData.leafCenters_eq_zero_of_all_inputs {d n m w : ℕ}
    (P : MomentumTreeData n m w)
    (h : ∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none)
    (k : Mom d) (c : Fin m → Fin d → ℤ) (i : Fin w) (p : LocalizationTree.Path)
    (hp : p ∈ (P.tree i).leaves) : P.leafCenters k c i p = P.leafCenters 0 c i p := by
  unfold leafCenters
  cases he : P.leafInput i p with
  | none => exact False.elim (h i p hp he)
  | some a => rfl

/-- The actual couple center cover is fixed before the root momentum and all input functions. -/
theorem exists_uniform_couple_link_localization (d : ℕ) (hd : 0 < d) : ∃ C : ℕ,
    ∀ n m w : ℕ, ∀ P : MomentumTreeData n m w,
      (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
      ∀ c : Fin m → Fin d → ℤ,
      ∃ S : Finset (Fin n → Fin 2 → Mom d), S.card ≤ C ^ (2 * n) ∧
        ∀ k : Mom d, ∀ x : Fin n → Fin 2 → Mom d, P.inputCellWeight c k x ≠ 0 →
          ∃ a ∈ S, ∀ i j, ‖x i j - a i j‖ ≤ 2 * Real.sqrt d := by
  classical
  obtain ⟨C, hb⟩ := LocalizationTree.exists_finite_forest_localization d
  refine ⟨C, ?_⟩
  intro n m w P hinputs c
  obtain ⟨S, hS, hs⟩ := hb (Real.sqrt d) (Real.sqrt_pos.mpr (by exact_mod_cast hd))
    w P.tree (P.leafCenters (0 : Mom d) c)
  refine ⟨S.image P.linkCenters, Finset.card_image_le.trans (by simpa only [P.order_eq] using hS), ?_⟩
  intro k x hx
  have hleaf (i : Fin w) (p : LocalizationTree.Path) (hp : p ∈ (P.tree i).leaves) :
      ‖P.nodeMomentum (rootLinkMomenta k x) i p - P.leafCenters 0 c i p‖ ≤ Real.sqrt d := by
    rw [← P.leafCenters_eq_zero_of_all_inputs hinputs k c i p hp]
    exact P.leaf_bound_of_inputCellWeight_ne_zero c k x hx i p hp
  obtain ⟨a, ha, hclose⟩ := hs (P.nodeMomentum (rootLinkMomenta k x))
    (P.isDecoration_nodeMomentum _) hleaf
  exact ⟨P.linkCenters a, Finset.mem_image_of_mem _ ha, P.link_close_of_nodes_close k x a hclose⟩

end WaveTurbulence.Incoh
