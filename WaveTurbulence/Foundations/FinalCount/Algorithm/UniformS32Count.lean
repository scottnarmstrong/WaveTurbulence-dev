/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS32Frames
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTriplePairCount
import Mathlib.Tactic

/-! # Raw good count for all four degree-three/two removal figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_s32_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (k : AppbPatternKind) (hk : k ∈ appbS32Kinds)
      (r : AppbRealization M k.pattern), M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  obtain ⟨C,hC,L₀,hL₀⟩ := uniform_triple_pair_countE_of_projection_injective
    d hd γ hγ δ η hδ hη hηγ
  refine ⟨C,hC,L₀,?_⟩
  intro V D instV instF instD L hL hLp M k hk r hM w Adm hLG
  have ht : ∀ k ∈ appbS32Kinds,1 ∈ k.pattern.removed ∧ 2 ∈ k.pattern.removed := by decide
  apply hL₀ V D L hL hLp M _ r hM (r.vertex 1) (Finset.mem_image_of_mem _ (ht k hk).1)
    (r.vertex 2) (Finset.mem_image_of_mem _ (ht k hk).2) (appbS32Frame k hk r) (appbS32Pair k hk r)
    rfl w Adm (fun p => appb_s32_projection_injective k hk r p hLp γ δ w Adm) hLG

end WaveTurbulence.Mole.AppbAlgorithm
