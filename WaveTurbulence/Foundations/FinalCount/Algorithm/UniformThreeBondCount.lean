/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformThreeBondChoices
import Mathlib.Tactic

/-! # Carrier-uniform three-bond estimate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v
/-- The actual three-bond reduction, including a concrete post admissibility
predicate and zero post-count cases. -/
theorem uniform_three_bond_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, 0 < L → ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
      M.IsMolecule → P.edges.length = 3 → ∀ v ∈ r.removedAtoms,
      (∀ i,appbIncidence M v (r.edge i).val = 1) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin P.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_three_bond_localChoices_bound d hd γ hγ
  refine ⟨C,L₀,hC,?_⟩
  intro V D instV instF instD L hL hLp δ hδ M P r hM hlen v hv hinc w Adm
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L hL hLp δ hδ M P r hM hlen v hv hinc p w Adm
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
