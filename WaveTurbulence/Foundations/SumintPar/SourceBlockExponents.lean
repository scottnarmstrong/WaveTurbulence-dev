/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceBlockCounts
public import WaveTurbulence.Foundations.SumintPar.BadBlockPowerMargins

/-!
# Collecting local block exponents at the exact source counts

The definitions here are numerical budgets, not replacement masses.
Their sums use the literal drafted M, M₀, and M₁. The final inequality
pays every case-(d) linear loss from the actual weight multiplicity.
-/

@[expose] public section
set_option autoImplicit false

open Finset
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Pair and normal discrepancy indicators in one literal source block. -/
@[expose] noncomputable def blockDiscrepancy {d : ℕ} (D : SumintDatum d) (i : Fin D.S.I) : ℕ :=
  (∑ j : Fin (D.S.m i), if pairIncoherent D ⟨i,j⟩ then 1 else 0)+
    if hi : D.S.nor i = true then (if normalIncoherent D ⟨i,hi⟩ then 1 else 0) else 0

/-- The local discrepancy counts sum exactly to the drafted M₀. -/
theorem sum_blockDiscrepancy {d : ℕ} (D : SumintDatum d) :
    ∑ i, blockDiscrepancy D i = D.M₀ := by
  unfold blockDiscrepancy
  have he := sum_normal_extension D.S (fun i => if normalIncoherent D i then 1 else 0)
  rw [Finset.sum_add_distrib,he,source_M₀_eq_discrepancy_sum]

/-- The retained bad gain, or the cost of the case-(d) linear branch, in one block. -/
@[expose] noncomputable def badBlockCost {d : ℕ} (D : SumintDatum d) (γ : ℝ) (i : Fin D.S.I) : ℝ :=
  if D.S.nor i = false then (if D.badKind i = 3 then 3*gammaBase γ/2 else -gammaBase γ/4) else 0

/-- The real sum of indicators equals the cardinality of the literal finite filter. -/
theorem sum_real_indicator_eq_card {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (∑ i, if p i then (1:ℝ) else 0) = (Finset.univ.filter p).card := by
  have h : (∑ i, if p i then (1:ℕ) else 0) = (Finset.univ.filter p).card := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact_mod_cast h

/-- The block bad budgets retain exactly the actual bad and case-(d) counts. -/
theorem sum_badBlockCost {d : ℕ} (D : SumintDatum d) (γ : ℝ) :
    (∑ i, badBlockCost D γ i) =
      -(gammaBase γ/4)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)-
        ((Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 3)).card:ℝ))+
      (3*gammaBase γ/2)*((Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 3)).card:ℝ) := by
  have he (i : Fin D.S.I) : badBlockCost D γ i =
      -(gammaBase γ/4)*(if D.S.nor i = false then (1:ℝ) else 0)+
      (7*gammaBase γ/4)*(if D.S.nor i = false ∧ D.badKind i = 3 then (1:ℝ) else 0) := by
    unfold badBlockCost
    by_cases hn : D.S.nor i = false <;> by_cases hk : D.badKind i = 3 <;> simp [hn,hk] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    sum_real_indicator_eq_card,sum_real_indicator_eq_card]
  ring

/-- The exact total input, bad, weight, and incoherence exponents fit the source Step 2 budget. -/
theorem source_total_block_exponent_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (hd : 2 ≤ d) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hs : Real.sqrt η ≤ gammaBase γ/8) (β : ℝ) :
    (∑ i : Fin D.S.I, ((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-
        (β/20)*(blockDiscrepancy D i:ℝ)))-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ) ≤
      (D.S.M:ℝ)*((d:ℝ)-γ)-
        (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
        (β/20)*(D.M₀:ℝ) := by
  have hbudget := source_case_d_weight_reserve D hD hd hγ hs
  have hn : (∑ i : Fin D.S.I, (D.S.n i:ℝ)) = D.S.M := by
    exact_mod_cast (rfl : (∑ i : Fin D.S.I, D.S.n i) = D.S.M)
  have hdisc : (∑ i : Fin D.S.I, (blockDiscrepancy D i:ℝ)) = D.M₀ := by
    exact_mod_cast sum_blockDiscrepancy D
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hn,hdisc,
    sum_badBlockCost]
  dsimp only at hbudget
  linarith only [hbudget]

end WaveTurbulence.SumintPar
