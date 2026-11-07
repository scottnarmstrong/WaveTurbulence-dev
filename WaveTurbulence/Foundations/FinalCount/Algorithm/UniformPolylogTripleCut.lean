/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleCutGoodChoices
public import WaveTurbulence.Foundations.FinalCount.AppBPolylogCutStrip
import Mathlib.Tactic

/-! # Good triple gain from a two-bond cut with a polylogarithmic side -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_triple_cut_polylog_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀,
    ∀ hLp : 0 < L, ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
      M.IsMolecule → ∀ v ∈ r.removedAtoms,∀ t : AppbTripleFrame r v,
    ∀ (S : Finset V) (cut : AppbCutPair r S),
      appbCutSign M S (r.edge cut.first).val ≠ appbCutSign M S (r.edge cut.second).val →
      (S.card : ℝ) ≤ 2*(1+Real.log L)^m → ∀ j0 : Fin 3,cut.first = t.index j0 →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,κ ∈ p.decorations L γ δ w Adm → c⁻¹*L^(-γ) ≤
        ‖Molecule.kvec L w κ (r.edge cut.first).val-Molecule.kvec L w κ (r.edge cut.second).val‖) →
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤
        C*L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  classical
  obtain ⟨C,hC,hbase⟩ := appb_physical_triple_strip_good_bound d hd γ hγ c (zero_lt_one.trans_le hc) m
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL hLp M P r hM v hv t S cut hcutOpp hcard j0 hfirst p w Adm hgap
  have hL1 : 1 ≤ L := (le_max_right L₀ 1).trans hL
  let Q := r.localChoices p hLp γ δ w Adm
  let R := (((appbCutSign M S (r.edge cut.first).val)⁻¹ : ℤˣ) : ℤ) • (∑ a ∈ S,p.momentum a)
  let βs := ((((appbCutSign M S (r.edge cut.first).val)⁻¹ : ℤˣ) : ℤ)*(∑ a ∈ S,p.energy a)+‖R‖^2)/2
  by_cases hnon : Q.Nonempty
  · obtain ⟨q0,hq0⟩ := hnon
    obtain ⟨κ0,hκ0,hκq⟩ := (r.mem_localChoices p hLp γ δ w Adm q0).mp hq0
    have hR : Molecule.kvec L w (r.localLabels κ0) cut.first-
        Molecule.kvec L w (r.localLabels κ0) cut.second = R :=
      cut.momentum_difference hcutOpp L w p.momentum κ0 hκ0.1
    have hr : c⁻¹*L^(-γ) ≤ ‖R‖ := by
      rw [← hR]
      exact hgap κ0 hκ0
    obtain ⟨π,hsame,hopp⟩ := t.exists_order hM (r.removedAtoms_subset hv)
    let s0 := Q.image t.project
    let encode := fun q : Fin 3 → (Fin d → ℤ) => (q (π 0),q (π 1),q (π 2))
    let s := s0.image encode
    let σ := appbIncidenceSign M v (r.edge (t.index (π 0))).val
    have hb := hL₀ L ((le_max_left L₀ 1).trans hL) w (p.center (r.edge (t.index (π 0))).val)
      (p.center (r.edge (t.index (π 1))).val) (p.center (r.edge (t.index (π 2))).val)
      (((σ⁻¹ : ℤˣ) : ℤ) • p.momentum v) R (((σ⁻¹ : ℤˣ) : ℤ)*p.energy v) βs
      (π.symm j0) hr s (by
        intro q hq
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
        obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
        obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
        refine ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 0)),
          r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 1)),
          r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 2)),
          t.momentum π hsame hopp hv L w p.momentum κ hκ.1,
          by
            exact (t.energy π hsame hopp hv L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1).trans
              (appb_atomic_window_le_width hL1 hδ.le m),?_⟩
        change |inner ℝ R (![Molecule.kvec L w (r.localLabels κ) (t.index (π 0)),
          Molecule.kvec L w (r.localLabels κ) (t.index (π 1)),
          Molecule.kvec L w (r.localLabels κ) (t.index (π 2))] (π.symm j0))-βs| ≤ appbWidth δ γ m L
        rw [appb_triple_permutation_encoding_apply_good π (fun j => Molecule.kvec L w (r.localLabels κ) (t.index j)),
          π.apply_symm_apply,← hfirst]
        exact cut.strip_bound_polylog hcutOpp hL1 γ δ hδ m hcard w p.momentum p.energy p.center κ hκ.1 hκ.2.1)
    have he : s.card = s0.card := card_image_of_injective s0 (appb_triple_permutation_encoding_injective π)
    rw [he] at hb
    exact hb
  · have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hnon
    change ((Q.image t.project).card : ℝ) ≤ _
    rw [he,Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    positivity


end WaveTurbulence.Mole.AppbAlgorithm
