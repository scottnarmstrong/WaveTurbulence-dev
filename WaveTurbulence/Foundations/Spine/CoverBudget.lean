/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoverFinite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-! Weight budget of the finite counting cover: one absolute exponential constant `3^16 * 17`
pays for the gap table and the pair table, and the logarithmic scale cost `log L / log 2 + 2`
per ladder and per critical SG atom is paid by the factor `(log L)^(rho + p)` of finalcount1
(TARGET L2088, L2106). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.Cover
open WaveTurbulence.Induct
open SourceVine Set Finset WaveTurbulence.LGSpine
open scoped Classical

variable {d : ℕ}

theorem card_scales_le {w : ℕ} {G : Garden w} (B : CountingChoices G d) {L : ℝ} (hL : 1 ≤ L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) :
    (Nat.card (Scales B L γ η) : ℝ) ≤
      (Real.log L / Real.log 2 + 2) ^ G.molecule.maximalLadders.card *
        (Real.log L / Real.log 2 + 1) ^ B.numCriticalSG := by
  unfold Scales
  rw [Nat.card_prod, Nat.cast_mul]
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  have h1 := card_sourceLadderScaleFamilies_le (V := {S // S ∈ G.molecule.maximalLadders}) hL
  have hV : Nat.card {S // S ∈ G.molecule.maximalLadders} = G.molecule.maximalLadders.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hV] at h1
  have h2 : (Nat.card ({v // B.CriticalSG v} → AtomScale L γ η) : ℝ) ≤
      (Real.log L / Real.log 2 + 1) ^ B.numCriticalSG := by
    rw [Nat.card_fun, Nat.cast_pow]
    have hc : Nat.card {v // B.CriticalSG v} = B.numCriticalSG := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
    rw [hc]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_sourceAtomScales_le hL hb) _
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)

theorem scales_weight_le {R : ℕ} (G : Garden (2 * R)) (B : CountingChoices G d) {L : ℝ}
    (hL : 1 ≤ L) (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) (C₀ : ℝ) (hC₀pos : 0 < C₀)
    [Fintype (Scales B L γ η)] :
    ∑ _x : Scales B L γ η, (C₀ ^ G.order * (Real.log L / Real.log 2 + 2) ^
        (G.molecule.rho + B.numCriticalSG))⁻¹ ≤ (C₀ ^ G.order)⁻¹ := by
  set s : ℝ := Real.log L / Real.log 2 + 2 with hs
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hq : G.molecule.maximalLadders.card ≤ G.molecule.rho := source_numLadders_le_rho G
  have hcard := card_scales_le B hL γ η hb
  have hcard' : (Fintype.card (Scales B L γ η) : ℝ) ≤ s ^ (G.molecule.rho + B.numCriticalSG) := by
    rw [← Nat.card_eq_fintype_card]
    refine hcard.trans ?_
    calc (Real.log L / Real.log 2 + 2) ^ G.molecule.maximalLadders.card *
          (Real.log L / Real.log 2 + 1) ^ B.numCriticalSG
        ≤ s ^ G.molecule.maximalLadders.card * s ^ B.numCriticalSG := by
          apply mul_le_mul le_rfl (pow_le_pow_left₀ (by linarith) (by rw [hs]; linarith) _)
            (by positivity) (by positivity)
      _ = s ^ (G.molecule.maximalLadders.card + B.numCriticalSG) := (pow_add _ _ _).symm
      _ ≤ s ^ (G.molecule.rho + B.numCriticalSG) :=
          pow_le_pow_right₀ hs1 (Nat.add_le_add_right hq _)
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hpos : 0 < C₀ ^ G.order * s ^ (G.molecule.rho + B.numCriticalSG) := by positivity
  calc (Fintype.card (Scales B L γ η) : ℝ) * (C₀ ^ G.order * s ^ (G.molecule.rho + B.numCriticalSG))⁻¹
      ≤ s ^ (G.molecule.rho + B.numCriticalSG) *
          (C₀ ^ G.order * s ^ (G.molecule.rho + B.numCriticalSG))⁻¹ :=
        mul_le_mul_of_nonneg_right hcard' (inv_nonneg.mpr hpos.le)
    _ = (C₀ ^ G.order)⁻¹ := by
        rw [mul_inv, mul_comm (C₀ ^ G.order)⁻¹, ← mul_assoc, mul_inv_cancel₀ (by positivity),
          one_mul]

theorem coverIndex_weight_le_one {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule)
    (D : SplicedKernelData G d) (Cs : SubproChoices G) {L : ℝ} (hL : 1 ≤ L) (γ η : ℝ)
    (hb : L ^ (-γ + η) ≤ 1) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    [Fintype (CoverIndex G hM D Cs L γ η base roots)]
    (C₀ : ℝ) (hC₀ : ((3 ^ 16 * 17 : ℕ) : ℝ) ≤ C₀) :
    ∑ j : CoverIndex G hM D Cs L γ η base roots,
      (C₀ ^ G.order * (Real.log L / Real.log 2 + 2) ^
        (G.molecule.rho + j.choice.numCriticalSG))⁻¹ ≤ 1 := by
  set s : ℝ := Real.log L / Real.log 2 + 2 with hs
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by positivity) hC₀
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hfin : ∀ t : Tag G, Finite (Scales (tagChoice G hM Cs L γ η base roots t) L γ η) :=
    fun t => finite_scales _ hL0 γ η hb
  letI : ∀ t : Tag G, Fintype (Scales (tagChoice G hM Cs L γ η base roots t) L γ η) :=
    fun t => Fintype.ofFinite _
  let F : ((t : Tag G) × Scales (tagChoice G hM Cs L γ η base roots t) L γ η) → ℝ :=
    fun x => (C₀ ^ G.order * s ^ (G.molecule.rho + (tagChoice G hM Cs L γ η base roots x.1).numCriticalSG))⁻¹
  have hF0 : ∀ x, 0 ≤ F x := fun x => by positivity
  have h1 : ∑ j : CoverIndex G hM D Cs L γ η base roots, F j.1 ≤ ∑ x, F x := by
    rw [← Finset.sum_image (s := (univ : Finset (CoverIndex G hM D Cs L γ η base roots)))
      (g := Subtype.val) (f := F) (fun a _ b _ h => Subtype.ext h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hF0 x)
  have e : ∀ j : CoverIndex G hM D Cs L γ η base roots,
      (C₀ ^ G.order * s ^ (G.molecule.rho + j.choice.numCriticalSG))⁻¹ = F j.1 := by
    intro j
    simp only [F, CoverIndex.choice, fullChoice_numCritical]
  rw [Finset.sum_congr rfl (fun j _ => e j)]
  refine h1.trans ?_
  rw [Fintype.sum_sigma]
  have hper : ∀ t : Tag G, ∑ x : Scales (tagChoice G hM Cs L γ η base roots t) L γ η,
      F ⟨t, x⟩ ≤ (C₀ ^ G.order)⁻¹ := fun t =>
    scales_weight_le G (tagChoice G hM Cs L γ η base roots t) hL γ η hb C₀ hC₀pos
  calc ∑ t : Tag G, ∑ x : Scales (tagChoice G hM Cs L γ η base roots t) L γ η, F ⟨t, x⟩
      ≤ ∑ _t : Tag G, (C₀ ^ G.order)⁻¹ := sum_le_sum (fun t _ => hper t)
    _ = (Fintype.card (Tag G) : ℝ) * (C₀ ^ G.order)⁻¹ := by simp
    _ ≤ 1 := by
        have hT : (Fintype.card (Tag G) : ℝ) ≤ ((3 ^ 16 * 17 : ℕ) : ℝ) ^ G.order := by
          have hT' : Fintype.card (Tag G) ≤ (3 ^ 16 * 17) ^ G.order := by
            unfold Tag
            rw [Fintype.card_prod, mul_pow]
            exact Nat.mul_le_mul (card_sourceGapTables_le G) (card_sourcePairTables_le G)
          exact_mod_cast hT'
        have hpow : ((3 ^ 16 * 17 : ℕ) : ℝ) ^ G.order ≤ C₀ ^ G.order :=
          pow_le_pow_left₀ (by positivity) hC₀ _
        have hcp : 0 < C₀ ^ G.order := by positivity
        calc (Fintype.card (Tag G) : ℝ) * (C₀ ^ G.order)⁻¹ ≤ C₀ ^ G.order * (C₀ ^ G.order)⁻¹ :=
              mul_le_mul_of_nonneg_right (hT.trans hpow) (inv_nonneg.mpr hcp.le)
          _ = 1 := mul_inv_cancel₀ hcp.ne'

end WaveTurbulence.LGSpine.Cover
