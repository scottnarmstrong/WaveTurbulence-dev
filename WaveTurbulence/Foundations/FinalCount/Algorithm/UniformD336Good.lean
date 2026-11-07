/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD336SplitGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD336LiteralRankFiveGood
public import WaveTurbulence.Foundations.FinalCount.AppBD33CombinedEffects
import Mathlib.Tactic

/-! # DH23 3D3-6G on the actual nine-bond atomic group -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- Both possible component outcomes use literal four-atom deletion,
actual conditioned post data, and the original scales. -/
theorem uniform_d336_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33new.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) → (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin AppbPatternKind.d33new.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  obtain ⟨L4,h4⟩ := uniform_d336_split_good_bound d hd γ hγ δ η hδ hη hηγ m
  obtain ⟨L5,h5⟩ := uniform_d336_literal_rank_five_good_bound d hd γ hγ δ hδ
  refine ⟨max L4 L5,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hc hb hsize w Adm scales hscale hLG
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hc
  rcases appb_d336_graph_effect M r hc hb with h | h
  · have hF : r.post.numComponents = 1 := h.1.trans hm
    exact h5 V D C1 hC1 L ((le_max_right _ _).trans hL) M r hM hc hF w Adm scales hscale
  · have hF : r.post.numComponents = 2 := by omega
    exact h4 V D C1 hC1 L ((le_max_left _ _).trans hL) M r hM hc hF hsize w Adm scales hscale hLG

end WaveTurbulence.Mole.AppbAlgorithm
