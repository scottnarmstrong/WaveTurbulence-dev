/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSignedStarPhysical
public import WaveTurbulence.Foundations.FinalCount.AppBCutTriple
public import WaveTurbulence.Foundations.FinalCount.AppBCutPairLogWindow
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Overlap of a source triple with an actual three-bond cut -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_star_cut_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P), M.IsMolecule →
    ∀ v ∈ r.removedAtoms, ∀ t : AppbTripleFrame r v,
    ∀ S : Finset V, ∀ cut : AppbCutTriple r S,
      (S.card : ℝ) ≤ (1+Real.log L)^m →
      (∀ a : ℤˣ,¬∀ j,appbCutSign M S (r.edge (cut.index j)).val = a) →
    ∀ e : Fin 5 ↪ Fin P.edges.length,
      (∀ j,t.index j = e (![0,1,2] j)) → (∀ j,cut.index j = e (![0,3,4] j)) →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (((r.localChoices p hLp γ δ w Adm).image (fun q j => q (e j))).card : ℝ) ≤
        L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_signed_star_physical_bound d hd γ hγ δ hδ m
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL hLp M P r hM v hv t S cut hsize hcap e ht hc p w Adm
  have hL1 : 1 ≤ L := (le_max_right L₀ 1).trans hL
  let signs : Bool → Fin 3 → ℤˣ := fun b j => if b then
    appbCutSign M S (r.edge (cut.index j)).val else appbIncidenceSign M v (r.edge (t.index j)).val
  let K : Bool → Mom d := fun b => if b then ∑ a ∈ S,p.momentum a else p.momentum v
  let β : Bool → ℝ := fun b => if b then ∑ a ∈ S,p.energy a else p.energy v
  have hplus : ∀ b,¬∀ j,signs b j = 1 := by
    intro b
    cases b
    · exact r.not_all_positive_frame_signs hM t.index (r.removedAtoms_subset hv)
    · exact hcap 1
  have hminus : ∀ b,¬∀ j,signs b j = -1 := by
    intro b
    cases b
    · exact r.not_all_negative_frame_signs hM t.index (r.removedAtoms_subset hv) t.incidence
    · exact hcap (-1)
  apply hL₀ L ((le_max_left _ _).trans hL) hLp w signs hplus hminus K β (fun j => p.center (r.edge (e j)).val)
  intro q hq
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
  refine ⟨fun j => r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (e j),?_⟩
  intro b
  cases b
  · have hm := r.local_momentum L w p.momentum κ hκ.1 hv
    rw [t.sum_incidence] at hm
    have he := r.local_energy L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1 hv
    rw [t.sum_incidence] at he
    simp only [zsmul_eq_mul] at he
    refine ⟨?_,?_⟩
    · change (∑ j : Fin 3,(appbIncidenceSign M v (r.edge (t.index j)).val : ℤ) •
        Molecule.kvec L w (r.localLabels κ) (e (![0,1,2] j))) = p.momentum v
      simpa only [ht] using hm
    · change |(∑ j : Fin 3,((appbIncidenceSign M v (r.edge (t.index j)).val : ℤ) : ℝ)*
        ‖Molecule.kvec L w (r.localLabels κ) (e (![0,1,2] j))‖^2)-p.energy v| ≤ _
      have hh := he.trans (AppbCutPair.atomic_window_le_log hL1 hδ.1 m)
      simpa only [ht] using hh
  · have hm := cut.momentum L w p.momentum κ hκ.1
    have he := cut.energy L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1
    have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := by have hδp := hδ.1; positivity
    have hw : (S.card : ℝ)*(δ⁻¹*L^(-2*γ)) ≤ appbWidth δ γ m L :=
      (mul_le_mul_of_nonneg_right hsize hτ).trans_eq (by unfold appbWidth; ring)
    refine ⟨?_,?_⟩
    · change (∑ j : Fin 3,(appbCutSign M S (r.edge (cut.index j)).val : ℤ) •
        Molecule.kvec L w (r.localLabels κ) (e (![0,3,4] j))) = ∑ a ∈ S,p.momentum a
      simpa only [hc] using hm
    · change |(∑ j : Fin 3,((appbCutSign M S (r.edge (cut.index j)).val : ℤ) : ℝ)*
        ‖Molecule.kvec L w (r.localLabels κ) (e (![0,3,4] j))‖^2)-(∑ a ∈ S,p.energy a)| ≤ _
      simpa only [hc] using he.trans hw

end WaveTurbulence.Mole.AppbAlgorithm
