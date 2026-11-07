/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformThreeBondCount
public import WaveTurbulence.Foundations.FinalCount.AppBTripleCount
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TBGlobalCircuitRank
public import WaveTurbulence.Foundations.FinalCount.AppBNormalNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBTB1Links
public import WaveTurbulence.Foundations.FinalCount.AppBTripleBondEffects
public import WaveTurbulence.Foundations.FinalCount.AppBNormalEffects
import Mathlib.Tactic

/-! # DH23 TB-1N: actual normal deviation with exact ladder preservation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 tbprop, isolated triple-bond removal. A fixed sufficiently large C1 makes the
refined invariant nonincreasing; in particular this is a normal bound.
All counts and the conditioned post problem are the actual molecule ones. -/
theorem uniform_tb1_global_normal_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ C₀, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.tb1.pattern),
      M.IsMolecule →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      ∃ q : Fin AppbPatternKind.tb1.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales) 1 := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_three_bond_countE_bound d hd γ hγ
  refine ⟨max C 1,max L₀ 1,le_max_right C 1,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M r hM w Adm scales
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (by decide)
  have hinc : ∀ i,appbIncidence M (r.vertex 1) (r.edge i).val = 1 := by
    intro i
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i <;> decide
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) hLp δ hδ M _ r hM rfl (r.vertex 1) hv hinc w Adm
  refine ⟨q,?_⟩
  have hchi := tb1_global_circuitRank M r
  have hprod := appb_tb1_linkProduct M r L γ δ scales
  have ha := appb_normal_normalization_of_raw _ _ r.post.circuitRank L ((d : ℝ)-γ) δ C1 C
    (appbLinkProduct r.post L γ δ scales) hLp hδ.1
    ((le_max_right C 1).trans hC1) ((le_max_left C 1).trans hC1) hC.le hraw
  unfold IsDeviation appbLinkCountA
  rw [one_mul,hchi,← hprod]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
