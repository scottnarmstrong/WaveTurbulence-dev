/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryPairBound
public import WaveTurbulence.Foundations.Sumint.SourceNormalBlockBound
public import WaveTurbulence.Foundations.Sumint.ShapeFacts

/-!
# Exact source block and incoherence counts

The drafted M and M₀ are retained literally. These identities express
them as the sums of the local arities and discrepancy indicators used
by the independent source mass bounds.
-/

public section

open Finset
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Extending a normal-block summand by zero preserves its subtype sum. -/
theorem sum_normal_extension (S : SumintShape)
    (f : {i : Fin S.I // S.nor i = true} → ℕ) :
    (∑ i : Fin S.I, if hi : S.nor i = true then f ⟨i,hi⟩ else 0) = ∑ i, f i := by
  let g (i : Fin S.I) := if hi : S.nor i = true then f ⟨i,hi⟩ else 0
  have ht : (∑ i : {i : Fin S.I // S.nor i = true}, g i) = ∑ i, f i := by
    apply Finset.sum_congr rfl
    intro i _
    exact dite_eq_left i.2
  have hf : (∑ i : {i : Fin S.I // ¬ S.nor i = true}, g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact dite_eq_right i.2
  change (∑ i, g i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin S.I => S.nor i = true),ht,hf,add_zero]

/-- The exact total input count is two per pair, one per block, and three per normal block. -/
theorem source_size_eq_pairs_blocks_normals (S : SumintShape) :
    S.M = 2*(∑ i : Fin S.I, S.m i)+S.I+3*Fintype.card {i : Fin S.I // S.nor i = true} := by
  have hn : (∑ i : Fin S.I, if S.nor i = true then 3 else 0) =
      3*Fintype.card {i : Fin S.I // S.nor i = true} := by
    have hh := sum_normal_extension S (fun _ => 3)
    simpa [Nat.mul_comm] using hh
  unfold SumintShape.M SumintShape.n
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  rw [hn]

/-- The ordinary pair/normal delta cost is at most half the exact input arity. -/
theorem source_delta_cost_le_half_size (S : SumintShape) :
    ((∑ i : Fin S.I, S.m i):ℝ)+2*(Fintype.card {i : Fin S.I // S.nor i = true}:ℝ) ≤ (S.M:ℝ)/2 := by
  have hN : Fintype.card {i : Fin S.I // S.nor i = true} ≤ S.I := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin S.I => S.nor i = true)
  have hNR : (Fintype.card {i : Fin S.I // S.nor i = true}:ℝ) ≤ S.I := by exact_mod_cast hN
  have hMR : (S.M:ℝ) = 2*((∑ i : Fin S.I, S.m i):ℝ)+(S.I:ℝ)+
      3*(Fintype.card {i : Fin S.I // S.nor i = true}:ℝ) := by
    exact_mod_cast source_size_eq_pairs_blocks_normals S
  linarith only [hNR,hMR]

/-- The number of pair and normal constants is bounded by the total input arity. -/
theorem source_pair_normal_count_le_size (S : SumintShape) :
    (∑ i : Fin S.I, S.m i)+Fintype.card {i : Fin S.I // S.nor i = true} ≤ S.M := by
  have hM := source_size_eq_pairs_blocks_normals S
  omega

/-- The pair discrepancy count regrouped by the original source block. -/
theorem source_pair_discrepancy_count {d : ℕ} (D : SumintDatum d) :
    (Finset.univ.filter (fun a : Σ i : Fin D.S.I, Fin (D.S.m i) => pairIncoherent D a)).card =
      ∑ i : Fin D.S.I, ∑ j : Fin (D.S.m i), if pairIncoherent D ⟨i,j⟩ then 1 else 0 := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma]

/-- The source M₀ is exactly the sum of local pair and normal discrepancy indicators. -/
theorem source_M₀_eq_discrepancy_sum {d : ℕ} (D : SumintDatum d) :
    D.M₀ = (∑ i : Fin D.S.I, ∑ j : Fin (D.S.m i), if pairIncoherent D ⟨i,j⟩ then 1 else 0)+
      ∑ i : {i : Fin D.S.I // D.S.nor i = true}, if normalIncoherent D i then 1 else 0 := by
  unfold SumintDatum.M₀
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma]
  apply congrArg₂ (fun x y : ℕ => x+y)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · apply Finset.sum_congr rfl
    intro i _
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end WaveTurbulence.Sumint
