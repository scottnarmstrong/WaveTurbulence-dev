/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTwoBondChoices
import Mathlib.Tactic

/-! # Concrete post-deletion counting problems for two-bond removals -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 basiccount(1), applied to the actual molecule count: there is a
concrete conditioned post problem with the raw fine saving. This remains
an inequality when the post count vanishes. -/
theorem uniform_two_bond_countE_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (P : AppbPattern)
      (r : AppbRealization M P) (hlen : P.edges.length = 2) (v : V),
      v ∈ r.removedAtoms → (∀ i,appbIncidence M v (r.edge i).val = 1) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin P.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  obtain ⟨L₀,hL₀⟩ := uniform_two_bond_localChoices_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M P r hlen v hv hinc w Adm hLG
  have hL1 := (le_max_right L₀ 1).trans hL
  have hLp := zero_lt_one.trans_le hL1
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L ((le_max_left L₀ 1).trans hL) M P r hlen v hv hinc p w Adm hLG hLp
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
