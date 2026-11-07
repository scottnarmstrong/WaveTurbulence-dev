/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleSmallGapChoices
import Mathlib.Tactic

/-! # Carrier-uniform local projection estimate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v
theorem uniform_tripleFrame_small_gap_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
      ∀ v ∈ r.removedAtoms,∀ t : AppbTripleFrame r v,
      appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 1)).val →
      ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,κ ∈ p.decorations L γ δ w Adm → ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
        Molecule.kvec L w κ (r.edge (t.index 1)).val‖ ≤ L^(-γ+2*min γ (1-γ)/3)) →
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨C,hC,hbase⟩ := appb_physical_triple_small_gap_bound d hd γ hγ 0
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M P r v hv t h01 p w Adm hsmall
  obtain ⟨π,hsame,hopp,hπ⟩ := appb_internal_pair_order
    (fun j => appbIncidenceSign M v (r.edge (t.index j)).val) h01
  let Q := r.localChoices p hLp γ δ w Adm
  let s0 := Q.image t.project
  let encode := fun q : Fin 3 → (Fin d → ℤ) => (q (π 0),q (π 1),q (π 2))
  let s := s0.image encode
  let σ := appbIncidenceSign M v (r.edge (t.index (π 0))).val
  have hb := hL₀ L hL w (p.center (r.edge (t.index (π 0))).val)
    (p.center (r.edge (t.index (π 1))).val) (p.center (r.edge (t.index (π 2))).val)
    (((σ⁻¹ : ℤˣ) : ℤ) • p.momentum v) (((σ⁻¹ : ℤˣ) : ℤ)*p.energy v) s (by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
      obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
      refine ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 0)),
        r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 1)),
        r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 2)),
        t.momentum π hsame hopp hv L w p.momentum κ hκ.1,
        by
          rw [show appbWidth δ γ 0 L = δ⁻¹*L^(-2*γ) by simp [appbWidth]]
          exact t.energy π hsame hopp hv L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1,
        ?_⟩
      change ‖Molecule.kvec L w (r.localLabels κ) (t.index (π 0))-
        Molecule.kvec L w (r.localLabels κ) (t.index (π 1))‖ ≤ _
      rw [appb_internal_pair_norm π hπ
        (fun j => Molecule.kvec L w (r.localLabels κ) (t.index j))]
      exact hsmall κ hκ)
  have hc : s.card = s0.card := card_image_of_injective s0 (appb_triple_permutation_encoding_injective π)
  rw [hc] at hb
  exact hb

end WaveTurbulence.Mole.AppbAlgorithm
