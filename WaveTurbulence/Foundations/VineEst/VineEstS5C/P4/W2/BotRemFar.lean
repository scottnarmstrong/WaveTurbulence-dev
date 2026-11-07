/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemFar5
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotObj
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Idx

/-! # P4-W2 (session 9, bottom family): `RemC` for the carrier-side couple and tree of a BOTTOM index on a window

The bottom copy of `RemFar2` (`botRemQ_eq_clamp`, `botRemT_eq_clamp`) and `RemFar5` (`botRemC_cpl_at`, `botRemC_tree_at`): `botRemQ pstar κ (botQfam pstar κ A) b = KQstar - botQfam`,
with `botQfam_eq_clamp`/`botQfam_eq_zero` (W13/BotObj) in place of `zpQfam_eq_clamp`/`zpQfam_eq_zero`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.ZpSurj WaveTurbulence.VineEstS3 MeasureTheory Set WaveTurbulence.VineEstS5C.P4.Bot
open scoped ENNReal

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {d : ℕ} [Fintype ι] [DecidableEq ι]
  (κ : KPar d) (A : FamilyReconstruction w ι) (b : BT w ι)

theorem botRemQ_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    botRemQ pstar κ (botQfam pstar κ A) b t s k =
      KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) (min t (q + 1)) s k -
        SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  unfold botRemQ
  rw [botQfam_eq_clamp κ A b hL2q hqp hcoh ht s k]
  congr 1
  rcases le_total t ((q : ℝ) + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    exact KQstar_const_above _ _ _ _ _ (fun bb _ => coherentCouple_layer_le_q hL2q hqp hcoh bb.toNode) h le_rfl s k

theorem botRemT_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    botRemT pstar κ (botTfam pstar κ A) b t s k =
      KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) (min t (q + 1)) s k -
        SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  unfold botRemT
  rw [botTfam_eq_clamp κ A b hL2q hcoh ht s k]
  congr 1
  rcases le_total t ((q : ℝ) + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    exact KTstar_const_above _ _ _ _ _ (fun bb => (coherentTree_layer_le hL2q hcoh bb.toNode)) h le_rfl s k

end

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]
  {P : WTParams} {Bh : ℕ → ℝ} (A : FamilyReconstruction w ι)

/-- **`RemC` for the carrier-side couple of `b` on a window** (R-SUPPLY, R95). -/
theorem botRemC_cpl_at {κ : KPar P.d} (b : BT w ι) (E : GateEnv P κ p Bh)
    (hd : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hδ0 : 0 < P.δ) (hθ6 : 6 * P.η ^ 6 ≤ P.η) (hκL : κ.L = P.L) (hκγ : κ.γ = P.γ)
    {q : ℕ} (hqq : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (hsize : (zpCodeC b.1 pstar).size = 2 * n)
    {CR : ℝ} (hCR0 : 0 < CR) (hCR : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjC b.1 pstar) < CR)
    {W : ℕ} (hW2 : zpQ2 A pstar ≤ W) (hw : W = q ∨ q + 1 ≤ W ∨ (W + 1 ≤ q ∧ W < botLq pstar b)) :
    ∃ R : RemC P (30 * P.d) (timeBox (W : ℝ) (zpQ2 A pstar)) ![(W : ℝ), (zpQ2 A pstar : ℝ)] (trC (6 * P.η ^ 6) * CR),
      R.Bc = pairBc W (zpQ2 A pstar) ∧
      ∀ ts ∈ pairBc (W : ℝ) (zpQ2 A pstar), ∀ k, botRemQ pstar κ (botQfam pstar κ A) b (ts 0) (ts 1) k = R.f ts k := by
  have hη1 := E.hη
  obtain ⟨sf, hm, hc, R0, hR0⟩ := couple_gate_data E.hg E.hB hd hL1 E.hC hδ0 hη1 hθ6 E.hp hn hqq hqp hsize hcoh hCR
  have hg : ∀ k, Continuous fun ts : Fin 2 → ℝ => R0.f ts k := fun k => by
    rw [hR0]
    exact (continuous_KQstar_of_coherent E.hB hd hL1 hqq hqp hcoh k).sub (continuous_couple_app _ _ _ _ _ _ k)
  have hX := R0.hX
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  have hRf : ∀ (t s : ℝ) (k : Mom P.d), R0.f ![t, s] k =
      KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) t s k -
        SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) t s k := by
    intro t s k
    rw [hR0, hκL, hκγ, E.hδ]
    simp
  rcases hw with hw | hw | ⟨hw1, hw2⟩
  · obtain ⟨R, hRB, hRF⟩ := remC_window (P := P) (Λ₂ := 30 * P.d) hd hθ0 (q := (q : ℝ)) (q2 := (zpQ2 A pstar : ℝ))
      (w := (W : ℝ)) (Bn := timeBox (q : ℝ) (zpQ2 A pstar)) (Bw := timeBox (W : ℝ) (zpQ2 A pstar))
      (Bc := pairBc (W : ℝ) (zpQ2 A pstar)) Subset.rfl (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
      (pairBc_subset _ _) (pairBc_closure _ _)
      (fun s hs => timeBox_subset_closure_interior (q : ℝ) (zpQ2 A pstar) ⟨⟨by simp, by simp⟩, ⟨by simpa using hs.1, by simpa using hs.2⟩⟩)
      R0.f hg hCR0 hX (Or.inl ⟨by exact_mod_cast hw, by rw [hw]⟩)
    refine ⟨R, hRB, fun ts hts k => ?_⟩
    have ht : (q : ℝ) < ts 0 := by
      have := hts.1.1
      have hWq : (q : ℝ) ≤ W := by rw [hw]
      linarith
    rw [hRF ts (hRB ▸ hts) k, hRf, botRemQ_eq_clamp κ A b hqq hqp hcoh ht]
  · obtain ⟨R, hRB, hRF⟩ := remC_window (P := P) (Λ₂ := 30 * P.d) hd hθ0 (q := (q : ℝ)) (q2 := (zpQ2 A pstar : ℝ))
      (w := (W : ℝ)) (Bn := timeBox (q : ℝ) (zpQ2 A pstar)) (Bw := timeBox (W : ℝ) (zpQ2 A pstar))
      (Bc := pairBc (W : ℝ) (zpQ2 A pstar)) Subset.rfl (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
      (pairBc_subset _ _) (pairBc_closure _ _)
      (fun s hs => timeBox_subset_closure_interior (q : ℝ) (zpQ2 A pstar) ⟨⟨by simp, by simp⟩, ⟨by simpa using hs.1, by simpa using hs.2⟩⟩)
      R0.f hg hCR0 hX (Or.inr (by exact_mod_cast hw))
    refine ⟨R, hRB, fun ts hts k => ?_⟩
    have ht : (q : ℝ) < ts 0 := by
      have := hts.1.1
      have hWq : (q : ℝ) + 1 ≤ W := by exact_mod_cast hw
      linarith
    rw [hRF ts (hRB ▸ hts) k, hRf, botRemQ_eq_clamp κ A b hqq hqp hcoh ht]
  · obtain ⟨R, hRB, hRF⟩ := remC_zero (P := P) (Λ₂ := 30 * P.d) (q2 := (zpQ2 A pstar : ℝ)) (w := (W : ℝ))
      (Bw := timeBox (W : ℝ) (zpQ2 A pstar)) (Bc := pairBc (W : ℝ) (zpQ2 A pstar)) (timeBox_subset_cell _ _)
      (timeBox_subset_closure_interior _ _) (pairBc_subset _ _) (pairBc_closure _ _)
      (CR := trC (6 * P.η ^ 6) * CR) (by have := one_le_trC hθ0; positivity)
    refine ⟨R, hRB, fun ts hts k => ?_⟩
    have hgt : zpQ2 A pstar < botLq pstar b := lt_of_le_of_lt hW2 hw2
    have ht : ts 0 ≤ (botLq pstar b : ℝ) := by
      have := hts.1.2
      have : ((W : ℝ) + 1) ≤ botLq pstar b := by exact_mod_cast hw2
      linarith
    rw [hRF ts (hRB ▸ hts) k]
    unfold botRemQ
    rw [KQstar_zero_below_root κ.L κ.γ κ.δ κ.F hqq hqp hcoh hgt ht, botQfam_eq_zero κ A b hqq hqp hcoh hgt ht]
    simp

/-- **`RemC` for the carrier-side tree of `b` on a window** (R-SUPPLY, R95). -/
theorem botRemC_tree_at {κ : KPar P.d} (b : BT w ι) (E : GateEnv P κ p Bh)
    (hd : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hδ0 : 0 < P.δ) (hθ6 : 6 * P.η ^ 6 ≤ P.η) (hκL : κ.L = P.L) (hκγ : κ.γ = P.γ)
    {q : ℕ} (hqq : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (hsize : (zpCodeT b.1 pstar).size = 2 * n)
    {CR : ℝ} (hCR0 : 0 < CR) (hCR : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjT b.1 pstar) < CR)
    {W : ℕ} (hW2 : zpQ2 A pstar ≤ W) (hw : W = q ∨ q + 1 ≤ W ∨ (W + 1 ≤ q ∧ W < botLt pstar b)) :
    ∃ R : RemC P 0 (timeBoxGt (W : ℝ) (zpQ2 A pstar)) ![(W : ℝ), (zpQ2 A pstar : ℝ)] (trC (6 * P.η ^ 6) * CR),
      R.Bc = pairBcGt W (zpQ2 A pstar) ∧
      ∀ ts ∈ pairBcGt (W : ℝ) (zpQ2 A pstar), ∀ k, botRemT pstar κ (botTfam pstar κ A) b (ts 0) (ts 1) k = R.f ts k := by
  have hη1 := E.hη
  obtain ⟨sf, hm, hc, R0, hR0⟩ := tree_gate_data E.hg E.hB hd hL1 E.hC hδ0 hη1 hθ6 E.hp hn hqq hqp hsize hcoh hCR
  have hg : ∀ k, Continuous fun ts : Fin 2 → ℝ => R0.f ts k := fun k => by
    rw [hR0]
    exact (continuous_KTstar_of_coherent E.hB hd hL1 hqq hqp hcoh k).sub (continuous_tree_app _ _ _ _ _ _ k)
  have hX := R0.hX
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  have hRf : ∀ (t s : ℝ) (k : Mom P.d), R0.f ![t, s] k =
      KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) t s k -
        SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) t s k := by
    intro t s k
    rw [hR0, hκL, hκγ, E.hδ]
    simp
  have hq2W : (zpQ2 A pstar : ℝ) ≤ W := by exact_mod_cast hW2
  have hface : ∀ s ∈ Icc (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1), ![(q : ℝ) + 1, s] ∈ closure (interior (timeBoxGt (q : ℝ) (zpQ2 A pstar))) :=
    fun s hs => gt_trace_mem (by exact_mod_cast hqq) hs.1 hs.2
  rcases hw with hw | hw | ⟨hw1, hw2⟩
  · obtain ⟨R, hRB, hRF⟩ := remC_window (P := P) (Λ₂ := 0) hd hθ0 (q := (q : ℝ)) (q2 := (zpQ2 A pstar : ℝ))
      (w := (W : ℝ)) (Bn := timeBoxGt (q : ℝ) (zpQ2 A pstar)) (Bw := timeBoxGt (W : ℝ) (zpQ2 A pstar))
      (Bc := pairBcGt (W : ℝ) (zpQ2 A pstar)) (fun ts h => h.1) (timeBoxGt_subset_cell _ _)
      (timeBoxGt_subset_closure_interior hq2W)
      (pairBcGt_subset _ _) (pairBcGt_closure _ _) hface
      R0.f hg hCR0 hX (Or.inl ⟨by exact_mod_cast hw, by rw [hw]⟩)
    refine ⟨R, hRB, fun ts hts k => ?_⟩
    have ht : (q : ℝ) < ts 0 := by
      have := hts.1.1.1
      have hWq : (q : ℝ) ≤ W := by rw [hw]
      linarith
    rw [hRF ts (hRB ▸ hts) k, hRf, botRemT_eq_clamp κ A b hqq hcoh ht]
  · obtain ⟨R, hRB, hRF⟩ := remC_window (P := P) (Λ₂ := 0) hd hθ0 (q := (q : ℝ)) (q2 := (zpQ2 A pstar : ℝ))
      (w := (W : ℝ)) (Bn := timeBoxGt (q : ℝ) (zpQ2 A pstar)) (Bw := timeBoxGt (W : ℝ) (zpQ2 A pstar))
      (Bc := pairBcGt (W : ℝ) (zpQ2 A pstar)) (fun ts h => h.1) (timeBoxGt_subset_cell _ _)
      (timeBoxGt_subset_closure_interior hq2W)
      (pairBcGt_subset _ _) (pairBcGt_closure _ _) hface
      R0.f hg hCR0 hX (Or.inr (by exact_mod_cast hw))
    refine ⟨R, hRB, fun ts hts k => ?_⟩
    have ht : (q : ℝ) < ts 0 := by
      have := hts.1.1.1
      have hWq : (q : ℝ) + 1 ≤ W := by exact_mod_cast hw
      linarith
    rw [hRF ts (hRB ▸ hts) k, hRf, botRemT_eq_clamp κ A b hqq hcoh ht]
  · obtain ⟨R, hRB, hRF⟩ := remC_zero (P := P) (Λ₂ := 0) (q2 := (zpQ2 A pstar : ℝ)) (w := (W : ℝ))
      (Bw := timeBoxGt (W : ℝ) (zpQ2 A pstar)) (Bc := pairBcGt (W : ℝ) (zpQ2 A pstar)) (timeBoxGt_subset_cell _ _)
      (timeBoxGt_subset_closure_interior hq2W) (pairBcGt_subset _ _) (pairBcGt_closure _ _)
      (CR := trC (6 * P.η ^ 6) * CR) (by have := one_le_trC hθ0; positivity)
    refine ⟨R, hRB, fun ts hts k => ?_⟩
    have hgt : zpQ2 A pstar < botLt pstar b := lt_of_le_of_lt hW2 hw2
    have ht : ts 0 ≤ (botLt pstar b : ℝ) := by
      have := hts.1.1.2
      have : ((W : ℝ) + 1) ≤ botLt pstar b := by exact_mod_cast hw2
      linarith
    rw [hRF ts (hRB ▸ hts) k]
    unfold botRemT
    rw [KTstar_zero_below_root κ.L κ.γ κ.δ κ.F hqq hcoh hgt ht, botTfam_eq_zero κ A b hqq hcoh hgt ht]
    simp

end WaveTurbulence.VineEstS5C.P4.W2
