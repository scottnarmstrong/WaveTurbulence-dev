/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33GlobalNormal
public import WaveTurbulence.Foundations.FinalCount.AppBD33ScaleValidity
import Mathlib.Tactic

/-! # DH23 3D3-1N consumes the inherited physical link-scale invariant -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_d33_global_normal_of_valid_scales_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀, ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      M.IsMolecule →
      (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      AppbValidLinkScales M L w Adm c scales →
      (∀ κ,Adm κ → ∀ x,κ (M.mate x) = κ x) →
      ∃ q : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales) 1 := by
  obtain ⟨C₀,hC₀,hbase⟩ := uniform_d33_global_normal_bound d hd γ hγ c hc
  refine ⟨C₀,hC₀,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hbridge hOpp w Adm scales hvalid hmate
  exact hL₀ V D C1 hC1 L hL M r hM hbridge hOpp w Adm scales
    (appb_d33_lostScale_range r hvalid)
    (fun κ hκ hp => appb_d33_lostScale_gap hM r hvalid κ hκ (hmate κ hκ) hp)

end WaveTurbulence.Mole.AppbAlgorithm
