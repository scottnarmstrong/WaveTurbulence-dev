/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeCarrier
public import WaveTurbulence.Foundations.Incoh.MomentumTreeRootInput
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization

/-! # A single actual finite tree link-cell cover, before all root momenta -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh IncohInst

/-- The temporary root input supplies the omitted lone leaf, so the landed structural
localization theorem constructs a finite cover independent of the root momentum. -/
theorem actual_tree_augmented_uniform_cell_cover (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 1) (X : RegChain) (hX : X.DecodesTree G),
      ∀ c : Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ,
      ∃ S : Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ),
        (S.card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length ∧
        ∀ k : Mom d, ∀ x : Fin (X.treeLinks (G.sig 0)).length → Fin 2 → Mom d,
          (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
          ∀ z : (Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ,
            halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S := by
  obtain ⟨C,hC,h⟩ := exists_uniform_couple_link_cell_localization d hd
  exact ⟨C,hC,fun G X hX => h _ _ _ (treeCarrier hX).withRootInput
    (treeCarrier hX).withRootInput_all_leaves⟩

end WaveTurbulence.RegAsymp
