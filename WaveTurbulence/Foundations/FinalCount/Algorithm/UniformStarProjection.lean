/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStarFrame
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # The overlapping-triple gain on actual local decoration choices -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_star_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
    ∀ v1 ∈ r.removedAtoms, ∀ v2 ∈ r.removedAtoms, ∀ t : AppbStarFrame r v1 v2,
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤
        L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_star_physical_count_bound d hd γ hγ δ hδ 0
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M P r v1 hv1 v2 hv2 t p w Adm
  let σ1 := appbIncidenceSign M v1 (r.edge (t.first.index 0)).val
  let σ2 := appbIncidenceSign M v2 (r.edge (t.second.index 0)).val
  apply hL₀ L hL hLp t.profile w (((σ1⁻¹ : ℤˣ) : ℤ) • p.momentum v1)
    (((σ2⁻¹ : ℤˣ) : ℤ) • p.momentum v2) (fun j => p.center (r.edge (t.index j)).val)
    (((σ1⁻¹ : ℤˣ) : ℤ)*p.energy v1) (((σ2⁻¹ : ℤˣ) : ℤ)*p.energy v2)
  intro q hq
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
  have hm1 := t.first.momentum (Equiv.refl _) t.first_same t.first_opposite hv1 L w p.momentum κ hκ.1
  have hm2 := t.second.momentum (Equiv.refl _) t.second_same t.second_opposite hv2 L w p.momentum κ hκ.1
  have he1 := t.first.energy (Equiv.refl _) t.first_same t.first_opposite hv1 L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1
  have he2 := t.second.energy (Equiv.refl _) t.second_same t.second_opposite hv2 L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1
  have hf0 : t.first.index 0 = t.index 0 := t.first_indices 0
  have hf1 : t.first.index 1 = t.index 1 := t.first_indices 1
  have hf2 : t.first.index 2 = t.index 2 := t.first_indices 2
  simp only [Equiv.refl_apply,hf0,hf1,hf2] at hm1 he1
  have hsecond := t.second_encoding (r.localLabels κ)
  refine ⟨fun j => r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index j),?_,?_,?_,?_⟩
  · change Molecule.kvec L w (r.localLabels κ) (t.index 0)-
      Molecule.kvec L w (r.localLabels κ) (t.index 1)+Molecule.kvec L w (r.localLabels κ) (t.index 2) = _
    simpa only [σ1,hf0] using hm1
  · rw [hsecond]
    exact hm2
  · rw [show appbWidth δ γ 0 L = δ⁻¹*L^(-2*γ) by simp [appbWidth]]
    simpa only [σ1,hf0,Molecule.kvec,AppbStarFrame.project] using he1
  · rw [hsecond]
    rw [show appbWidth δ γ 0 L = δ⁻¹*L^(-2*γ) by simp [appbWidth]]
    exact he2

end WaveTurbulence.Mole.AppbAlgorithm
