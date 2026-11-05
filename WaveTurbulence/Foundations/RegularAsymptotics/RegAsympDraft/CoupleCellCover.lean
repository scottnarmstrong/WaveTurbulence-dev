/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleMomentumData
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization

/-! # Actual regular-couple link cells, uniformly in root momentum -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- A plain couple has an actual input at every leaf. -/
theorem coupleMomentumData_all_inputs {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (i : Fin 2) (p : LocalizationTree.Path)
    (hp : p ∈ ((coupleMomentumData hQ hG).tree i).leaves) :
    (coupleMomentumData hQ hG).leafInput i p ≠ none := by
  have hh : p ∈ (G.tree i).leaves := by simpa only [coupleMomentumData,localizationTree_leaves] using hp
  simp only [coupleMomentumData,dite_eq_left hh,ne_eq,reduceCtorEq,not_false_eq_true]

/-- The geometric cover is constructed for the actual regular-couple rows.
Its finite index set is selected before all root momenta. -/
theorem actual_couple_uniform_cell_cover (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      ∀ c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∃ S : Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (S.card : ℝ) ≤ C ^ Q.links.length ∧
        ∀ k : Mom d, ∀ x : Fin Q.links.length → Fin 2 → Mom d,
          (coupleMomentumData hQ hG).inputCellWeight c k x ≠ 0 →
          ∀ z : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
            halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S := by
  obtain ⟨C,hC,h⟩ := exists_uniform_couple_link_cell_localization d hd
  exact ⟨C,hC,fun G Q hQ hG => h _ _ _ (coupleMomentumData hQ hG)
    (coupleMomentumData_all_inputs hQ hG)⟩

end WaveTurbulence.RegAsymp
