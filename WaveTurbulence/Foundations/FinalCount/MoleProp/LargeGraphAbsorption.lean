/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleSourceCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.NormalizationConstant
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleGraphRank
public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption
import Mathlib.Tactic

/-! # Internal reduction to logarithmic graph size

The baseline theorem at a smaller exponential normalization constant proves
the large-graph case outright. Thus logarithmic size is proved by an internal
case split, not added to the source proposition as a premise.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.MoleProp

theorem exponential_rank_le_power {L n χ t : ℝ} (hLp : 0 < L)
    (hlog : 0 ≤ Real.log L) (hn : Real.log L ≤ n) (hχ : n ≤ 2*χ) (ht : t ≤ 1) :
    Real.exp (-2*χ) ≤ L^(-t) := by
  rw [Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right ht hlog
  linarith only [hn,hχ,hh]

theorem simple_molecule_exponential_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (Real.exp (-2*(M.circuitRank : ℝ))) := by
  obtain ⟨C,hC,hB⟩ := simple_molecule_count_bound d hd γ hγ η hη hηmax
  have hKp : 0 < Real.exp 2 := Real.exp_pos _
  have hK1 : 1 ≤ Real.exp 2 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨Real.exp 2*C,one_le_mul_of_one_le_of_one_le hK1 hC,?_⟩
  intro C1 hC1 δ hδ
  have hC1p : 0 < C1 := zero_lt_one.trans_le ((one_le_mul_of_one_le_of_one_le hK1 hC).trans hC1)
  have hsmall : C ≤ C1/Real.exp 2 := (le_div_iff₀ hKp).mpr (by simpa only [mul_comm] using hC1)
  obtain ⟨R,hR⟩ := hB (C1/Real.exp 2) hsmall δ hδ
  refine ⟨R,?_⟩
  intro L hL V D _ _ _ M hM hsimp Adm P hAdm
  have hb := hR L hL M hM hsimp Adm P hAdm
  rw [countAFree_change_constant M L γ δ (C1/Real.exp 2) C1 (div_pos hC1p hKp) hC1p (0 : Mom d) Adm P]
  have hratio : (C1/Real.exp 2)/C1 = Real.exp (-2) := by
    rw [Real.exp_neg]
    field_simp [hC1p.ne',hKp.ne']
  rw [hratio,← Real.rpow_intCast,← Real.exp_mul]
  have hh := mul_le_mul_of_nonneg_left hb
    (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp ((-2)*(M.circuitRank : ℝ))) from bot_le)
  simpa only [mul_one] using hh

theorem large_simple_molecule_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, ∀ t ≤ (1 : ℝ),
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → M.atoms.Nonempty →
      (∀ a ∈ M.atoms, 3 ≤ M.deg a) →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      Real.log L ≤ (M.atoms.card : ℝ) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L^(-t)) := by
  obtain ⟨C,hC,hB⟩ := simple_molecule_exponential_bound d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hB C1 hC1 δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL t ht V D _ _ _ M hM hsimp hne hmin hconn hsize Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hhand : (3 : ℝ)*M.atoms.card ≤ 2*M.bonds.card := by
    exact_mod_cast three_mul_card_atoms_le_two_mul_bonds M hmin
  have hF := Mole.numComponents_eq_one M hne hconn
  have hχeq : (M.circuitRank : ℝ) = (M.bonds.card : ℝ)-(M.atoms.card : ℝ)+1 := by
    simp only [Molecule.circuitRank,hF,Int.cast_add,Int.cast_sub,Int.cast_natCast,Nat.cast_one,Int.cast_one]
  have hχ : (M.atoms.card : ℝ) ≤ 2*(M.circuitRank : ℝ) := by linarith only [hhand,hχeq]
  exact (hR L ((le_max_left R 1).trans hL) M hM hsimp Adm P hAdm).trans
    (ENNReal.ofReal_le_ofReal (exponential_rank_le_power hLp (Real.log_nonneg hL1) hsize hχ ht))

/-- Internal small-graph arithmetic: any fixed size polynomial is absorbed
uniformly when n≤logL. The final source theorem proves this case condition. -/
theorem eventually_log_size_polynomial_bound {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (m : ℕ) :
    ∃ R : ℝ, ∀ L ≥ R, ∀ n : ℕ, (n : ℝ) ≤ Real.log L → C*((n : ℝ)+1)^m ≤ L^ε := by
  have he := CountLemmas.eventually_monomial_log_le (a := 0) hε hC m
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1 he
  refine ⟨R,?_⟩
  intro L hL n hn
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)+1)
    (by linarith only [hn] : (n : ℝ)+1 ≤ 1+Real.log L) m
  exact (mul_le_mul_of_nonneg_left hp hC).trans (by simpa only [Real.rpow_zero,mul_one] using hR L hL)

end WaveTurbulence.MoleProp
