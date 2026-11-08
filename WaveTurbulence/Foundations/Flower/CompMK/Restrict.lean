/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Defs

/-! # C5b COMP-MK: sub-families of Stage-1′ pieces, and the selected mass

* `restrictData S q`: the pieces of `S` satisfying `q`; its class counts are inherited (`stage1Counts_restrict`).
* `sum_eq_sum_powerset`: the pieces of nonzero value, grouped by their residual selected trees `U π ⊆ T`.
* `selMass_mul_prod`: the mass of a group times D7's gain over its residual trees is `b^N ∏_{j ∈ T} R_j⁻¹R_j^{-1/18}`,
  the same for every group. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.CompMK

/-- The pieces of `S` satisfying `q`. -/
def restrictData {P : WTParams} {R : ℕ} (S : Stage1DataMK P R) (q : S.Pc → Prop) : Stage1DataMK P R where
  Pc := {π // q π}
  fin := @Subtype.fintype _ q (Classical.decPred q) S.fin
  piece := fun π => S.piece π.1
  val := fun π => S.val π.1

theorem sum_restrictData {P : WTParams} {R : ℕ} (S : Stage1DataMK P R) (q : S.Pc → Prop) :
    @Finset.sum (restrictData S q).Pc ℂ _ (@univ _ (restrictData S q).fin) (restrictData S q).val =
      @Finset.sum S.Pc ℂ _ (@Finset.filter S.Pc q (Classical.decPred q) (@univ S.Pc S.fin)) S.val := by
  letI := S.fin
  change ∑ π : {π // q π}, S.val π.1 = ∑ π ∈ univ.filter q, S.val π
  exact (Finset.sum_subtype (univ.filter q) (fun x => by simp) S.val).symm

/-- The class counts of a sub-family (same classes, `cls ∘ val`). -/
theorem stage1Counts_restrict {C₀ : ℕ} {P : WTParams} {R N : ℕ} (S : Stage1DataMK P R) (q : S.Pc → Prop)
    {Cl : Type} (hCl : Fintype Cl) (cls : S.Pc → Cl) (h : Stage1Counts C₀ P R N S.toData Cl hCl cls) :
    Stage1Counts C₀ P R N (restrictData S q).toData Cl hCl (fun π => cls π.1) := by
  letI := S.fin
  letI : Fintype S.toData.Pc := S.fin
  obtain ⟨hr, hg, hc⟩ := h
  refine ⟨fun π => hr π.1, fun π => hg π.1, fun g r => le_trans ?_ (hc g r)⟩
  have hinj : ((@univ (restrictData S q).Pc (restrictData S q).fin).filter fun π =>
      ((restrictData S q).toData.piece π).gbar = g ∧ ((restrictData S q).toData.piece π).rbar = r).card ≤
      ((@univ S.Pc S.fin).filter fun π => (S.toData.piece π).gbar = g ∧ (S.toData.piece π).rbar = r).card := by
    refine Finset.card_le_card_of_injOn (fun π => π.1) (fun π hπ => ?_) (fun π₁ _ π₂ _ he => Subtype.ext he)
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 (Finset.mem_coe.1 hπ)).2⟩)
  exact_mod_cast hinj

/-- **Grouping by residual selected trees.** If every piece of nonzero value has `U π ⊆ T`, the sum of the values
is the sum over `V ⊆ T` of the sums over the pieces of nonzero value with `U π = V`. -/
theorem sum_eq_sum_powerset {ι : Type*} [Fintype ι] {κ : Type*} [DecidableEq κ] (val : ι → ℂ)
    (U : ι → Finset κ) (T : Finset κ) (hU : ∀ π, val π ≠ 0 → U π ⊆ T) :
    ∑ π, val π = ∑ V ∈ T.powerset, ∑ π ∈ univ.filter (fun π => val π ≠ 0 ∧ U π = V), val π := by
  rw [Finset.sum_comm' (t' := univ.filter fun π => val π ≠ 0) (s' := fun π => {U π})]
  · rw [← Finset.sum_filter_add_sum_filter_not univ (fun π => val π ≠ 0)]
    have h0 : ∑ π ∈ univ.filter (fun π => ¬ val π ≠ 0), val π = 0 :=
      Finset.sum_eq_zero fun π hπ => by simpa using (mem_filter.1 hπ).2
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun π _ => by simp
  · intro V π
    simp only [mem_powerset, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨-, hπ, rfl⟩
      exact ⟨rfl, hπ⟩
    · rintro ⟨rfl, hπ⟩
      exact ⟨hU π hπ, hπ, rfl⟩

/-- **The selected mass times the residual gain** is `b^N ∏_{kSel j ≠ none} R_j⁻¹R_j^{-1/18}`, for any group of
residual selected trees `V ⊆ {kSel ≠ none}`. -/
theorem selMass_mul_prod {R : ℕ} (N : ℕ) (b : ℝ) (Rs : Fin (2 * R) → ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (V : Finset (Fin (2 * R))) (hV : ∀ j ∈ V, (kSel j).isSome) :
    selMass N b Rs kSel V * ∏ j ∈ V, Rs j ^ (-(1 / 18 : ℝ)) =
      b ^ N * ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1) := by
  unfold selMass
  rw [mul_assoc]
  congr 1
  have hg : ∏ j ∈ V, Rs j ^ (-(1 / 18 : ℝ)) = ∏ j : Fin (2 * R), (if j ∈ V then Rs j ^ (-(1 / 18 : ℝ)) else 1) := by
    rw [Finset.prod_ite_mem univ V, Finset.univ_inter]
  rw [hg, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ V
  · have hs := hV j hj
    simp [hj, hs]
  · by_cases hs : (kSel j).isSome
    · simp [hj, hs]
    · simp [hj, hs]

end WaveTurbulence.Flower.CompMK
