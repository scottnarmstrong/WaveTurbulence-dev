/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPairEnergy
public import WaveTurbulence.Foundations.FinalCount.AppBLocalConservation
public import WaveTurbulence.Foundations.FinalCount.AppBSignedPairNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPairGood
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Good gain from two same-direction bonds in an actual cut -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_cut_same_sign_projection_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P)
      (S : Finset V) (cut : AppbCutPair r S),
      appbCutSign M S (r.edge cut.first).val = appbCutSign M S (r.edge cut.second).val →
      (S.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (((r.localChoices p hLp γ δ w Adm).image (fun q => (q cut.first,q cut.second))).card : ℝ) ≤
        L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_physical_pair_good_bound d hd δ γ hδ hγ m
  refine ⟨L₀,?_⟩
  intro L hL hLp M P r S cut hsame hcard p w Adm
  let σ := appbCutSign M S (r.edge cut.first).val
  apply hL₀ L hL w (p.center (r.edge cut.first).val) (p.center (r.edge cut.second).val)
    (((σ⁻¹ : ℤˣ) : ℤ) • (∑ a ∈ S,p.momentum a))
    (((σ⁻¹ : ℤˣ) : ℤ)*(∑ a ∈ S,p.energy a)) 1
  · intro q hq
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
    obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
    refine ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 cut.first,
      r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 cut.second,?_,?_⟩
    · have hm := cut.momentum L w p.momentum κ hκ.1
      rw [← hsame] at hm
      simpa only [inv_mul_cancel,one_smul,Molecule.kvec] using appb_signed_pair_momentum σ σ _ _ _ hm
    · have he := cut.energy L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1
      rw [← hsame] at he
      have hh := appb_signed_pair_energy σ σ _ _ _ _ he
      have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := by have hδp := hδ.1; positivity
      have hb : (S.card : ℝ)*(δ⁻¹*L^(-2*γ)) ≤ appbWidth δ γ m L :=
        (mul_le_mul_of_nonneg_right hcard hτ).trans_eq (by unfold appbWidth; ring)
      simpa only [inv_mul_cancel,Int.cast_one,one_mul,Molecule.kvec] using hh.trans hb
  · norm_num

end WaveTurbulence.Mole
