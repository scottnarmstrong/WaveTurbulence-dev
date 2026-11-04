/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeInputs

/-!
# Tree localization gives computed link-momentum centers

TARGET Step (2), audit P-2. The chosen link coordinates are actual node
differences. A radius-R node localization therefore gives radius-2R link
localization, without assuming a separate link-coordinate bound.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Link centers computed from a family of actual vertex centers. -/
@[expose] def MomentumTreeData.linkCenters {d n m w : ℕ} (P : MomentumTreeData n m w)
    (c : Fin w → LocalizationTree.Path → Mom d) (i : Fin n) : Fin 2 → Mom d :=
  ![c (P.chosenTree i) (P.chosenPath i ++ [0]) - c (P.chosenTree i) (P.chosenPath i),
    c (P.chosenTree i) (P.chosenPath i) - c (P.chosenTree i) (P.chosenPath i ++ [2])]

/-- Both literal link differences are localized by the proved node-difference relation. -/
theorem MomentumTreeData.link_close_of_nodes_close {d n m w : ℕ} (P : MomentumTreeData n m w)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) (c : Fin w → LocalizationTree.Path → Mom d)
    {R : ℝ} (hc : ∀ i p, p ∈ (P.tree i).nodes →
      ‖P.nodeMomentum (rootLinkMomenta k x) i p - c i p‖ ≤ R) :
    ∀ i j, ‖x i j - P.linkCenters c i j‖ ≤ 2 * R := by
  intro i j
  have hp := hc (P.chosenTree i) (P.chosenPath i) (P.chosen_mem_nodes i)
  have h0 := hc (P.chosenTree i) (P.chosenPath i ++ [0]) (P.child0_mem_nodes i)
  have h2 := hc (P.chosenTree i) (P.chosenPath i ++ [2]) (P.child2_mem_nodes i)
  fin_cases j
  · change ‖x i 0 - (c (P.chosenTree i) (P.chosenPath i ++ [0]) - c (P.chosenTree i) (P.chosenPath i))‖ ≤ _
    have hx := P.nodeMomentum_link_x (rootLinkMomenta k x) i
    change _ = x i 0 at hx
    rw [← hx]
    have he : P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i ++ [0]) -
        P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i) -
        (c (P.chosenTree i) (P.chosenPath i ++ [0]) - c (P.chosenTree i) (P.chosenPath i)) =
        (P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i ++ [0]) -
          c (P.chosenTree i) (P.chosenPath i ++ [0])) -
        (P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i) - c (P.chosenTree i) (P.chosenPath i)) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add h0 hp).trans_eq (by ring))
  · change ‖x i 1 - (c (P.chosenTree i) (P.chosenPath i) - c (P.chosenTree i) (P.chosenPath i ++ [2]))‖ ≤ _
    have hy := P.nodeMomentum_link_y (rootLinkMomenta k x) i
    change _ = x i 1 at hy
    rw [← hy]
    have he : P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i) -
        P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i ++ [2]) -
        (c (P.chosenTree i) (P.chosenPath i) - c (P.chosenTree i) (P.chosenPath i ++ [2])) =
        (P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i) - c (P.chosenTree i) (P.chosenPath i)) -
        (P.nodeMomentum (rootLinkMomenta k x) (P.chosenTree i) (P.chosenPath i ++ [2]) -
          c (P.chosenTree i) (P.chosenPath i ++ [2])) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hp h2).trans_eq (by ring))

/-- The computed source link centers form a dimensional exponential-size finite family. -/
theorem exists_finite_link_localization (d : ℕ) (hd : 0 < d) : ∃ C : ℕ,
    ∀ n m w : ℕ, ∀ P : MomentumTreeData n m w,
      ∀ k : Mom d, ∀ c : Fin m → Fin d → ℤ,
      ∃ S : Finset (Fin n → Fin 2 → Mom d), S.card ≤ C ^ (2 * n) ∧
        ∀ x : Fin n → Fin 2 → Mom d, P.inputCellWeight c k x ≠ 0 →
          ∃ a ∈ S, ∀ i j, ‖x i j - a i j‖ ≤ 2 * Real.sqrt d := by
  classical
  obtain ⟨C, hb⟩ := LocalizationTree.exists_finite_forest_localization d
  refine ⟨C, ?_⟩
  intro n m w P k c
  obtain ⟨S, hS, hs⟩ := hb (Real.sqrt d) (Real.sqrt_pos.mpr (by exact_mod_cast hd))
    w P.tree (P.leafCenters k c)
  refine ⟨S.image P.linkCenters, Finset.card_image_le.trans (by simpa only [P.order_eq] using hS), ?_⟩
  intro x hx
  obtain ⟨a, ha, hclose⟩ := hs (P.nodeMomentum (rootLinkMomenta k x))
    (P.isDecoration_nodeMomentum _) (P.leaf_bound_of_inputCellWeight_ne_zero c k x hx)
  exact ⟨P.linkCenters a, Finset.mem_image_of_mem _ ha, P.link_close_of_nodes_close k x a hclose⟩

end WaveTurbulence.Incoh
