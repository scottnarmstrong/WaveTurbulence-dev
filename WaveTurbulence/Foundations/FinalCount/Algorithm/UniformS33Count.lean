/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFullStarCount
import Mathlib.Tactic

/-! # Raw rank-three counting for all seven 3S3 figure groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- The gain on all five actual local labels uses only the two degree-three
source equations. The appropriate graph theorem determines which groups
lose three circuits and therefore consume this bound. -/
theorem uniform_s33_five_bond_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (k : AppbPatternKind) (hk : k ∈ appbS33Kinds)
      (r : AppbRealization M k.pattern), M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  obtain ⟨L₀,hL₀⟩ := uniform_full_star_countE_bound d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M k hk r hM w Adm
  let hlen := appb_s33_kind_length k hk
  let e := appbFiveEmbedding hlen
  have htable : ∀ k ∈ appbS33Kinds,1 ∈ k.pattern.removed ∧ 2 ∈ k.pattern.removed := by decide
  have hv1 : r.vertex 1 ∈ r.removedAtoms := Finset.mem_image_of_mem _ (htable k hk).1
  have hv2 : r.vertex 2 ∈ r.removedAtoms := Finset.mem_image_of_mem _ (htable k hk).2
  apply hL₀ V D L hL hLp M _ r hM (r.vertex 1) hv1 (r.vertex 2) hv2 e (finCongr hlen.symm).surjective
    (appbFiveFirst r hlen _ (appb_s33_first_incidence k hk r))
    (appbFiveSecond r hlen _ (appb_s33_second_incidence k hk r))
    (by intro j; fin_cases j <;> rfl) (by intro j; rfl) w Adm

end WaveTurbulence.Mole.AppbAlgorithm
