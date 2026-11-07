/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleSmallGap
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameReindex
import Mathlib.Tactic

/-! # Small internal gap in slots zero and two -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

/-- The same estimate with the distinguished pair in slots zero and two,
as in the split single-bond figure. Reindexing costs no multiplicity. -/
theorem uniform_tripleFrame_small_gap_02_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
      ∀ v ∈ r.removedAtoms,∀ t : AppbTripleFrame r v,
      appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 2)).val →
      ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,κ ∈ p.decorations L γ δ w Adm → ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
        Molecule.kvec L w κ (r.edge (t.index 2)).val‖ ≤ L^(-γ+2*min γ (1-γ)/3)) →
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨C,hC,hbase⟩ := uniform_tripleFrame_small_gap_projection_bound d hd γ hγ
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M P r v hv t h02 p w Adm hsmall
  let π : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have h0 : π 0 = 0 := by decide
  have h1 : π 1 = 2 := by decide
  have hs : appbIncidenceSign M v (r.edge ((t.reindex π).index 0)).val ≠
      appbIncidenceSign M v (r.edge ((t.reindex π).index 1)).val := by
    change appbIncidenceSign M v (r.edge (t.index (π 0))).val ≠
      appbIncidenceSign M v (r.edge (t.index (π 1))).val
    simpa only [h0,h1] using h02
  have hb := hL₀ V D L hL hLp M P r v hv (t.reindex π) hs p w Adm (by
    intro κ hk
    change ‖Molecule.kvec L w κ (r.edge (t.index (π 0))).val-
      Molecule.kvec L w κ (r.edge (t.index (π 1))).val‖ ≤ _
    simpa only [h0,h1] using hsmall κ hk)
  rw [t.reindex_project_card π] at hb
  exact hb

end WaveTurbulence.Mole.AppbAlgorithm
