/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTB1GlobalNormal
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTB2GlobalNormal
import Mathlib.Tactic

/-! # One carrier-uniform normal threshold for both actual TB layouts -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

theorem uniform_tb_normal_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ,1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (k : AppbPatternKind),k ∈ ([AppbPatternKind.tb1,.tb2] : List _) →
    ∀ r : AppbRealization M k.pattern,M.IsMolecule →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w A P)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A q) P) 1 := by
  obtain ⟨C₁,L₁,hC₁,h1⟩ := uniform_tb1_global_normal_bound d hd γ hγ
  obtain ⟨C₂,L₂,hC₂,h2⟩ := uniform_tb2_global_normal_bound d hd γ hγ
  refine ⟨max C₁ C₂,max L₁ L₂,hC₁.trans (le_max_left _ _),?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M k hk r hM w A P
  have hk' : k = .tb1 ∨ k = .tb2 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hk
  rcases hk' with rfl | rfl
  · exact h1 V D C1 ((le_max_left C₁ C₂).trans hC1) L ((le_max_left L₁ L₂).trans hL) δ hδ M r hM w A P
  · exact h2 V D C1 ((le_max_right C₁ C₂).trans hC1) L ((le_max_right L₁ L₂).trans hL) δ hδ M r hM w A P

end WaveTurbulence.Mole.AppbAlgorithm
