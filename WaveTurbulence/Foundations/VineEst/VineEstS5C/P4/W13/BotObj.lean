/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ZpObj
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotGeo

/-! # P4-W1 (bottom): the bottom approximant families `botQfam`, `botTfam` against a gate expansion at a gate level `q`

The mirror of `ZpObj` for BOT-DECOMP's families (`Bot.botQfam = mixFam botTrQ botEx botLq botQ0`, the same formulas on the index type
`Bot.BT`): `botQfam_eq_clamp`, `botQfam_eq_zero`, `botQ_expand` and the tree analogues (identity sets `VC`, `VT`, factors `clampJ`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS4c
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.Bot

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {pstar : ι} {d : ℕ} [Fintype ι] [DecidableEq ι] {p : ℕ} {kind : Bool}
  (κ : KPar d) (A : FamilyReconstruction w ι) (b : BT w ι)

/-- **Couple above the gate level**: `botQfam b t = SourceApp(q, L₂)(min t (q+1))` for `t > q`. -/
theorem botQfam_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    botQfam pstar κ A b t s k =
      SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  have hr := cpl_root_bounds hL2q hqp hcoh
  have hrq : (botLq pstar b : ℝ) ≤ q := by exact_mod_cast hr.2
  have hlt : (botLq pstar b : ℝ) < t := lt_of_le_of_lt hrq ht
  have hq : botQfam pstar κ A b t s k = extFam (botLq pstar) (botQ0 pstar κ A) b t s k := by
    unfold botQfam
    exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [botEx, ht]) hlt s k
  rw [hq, couple_eq_ext κ.δ κ.F hL2q hqp hcoh s k (le_min ht.le (by linarith)) (min_le_right _ _)]
  exact extConst_min _ hrq hlt.le

/-- **Tree above the gate level**. -/
theorem botTfam_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    botTfam pstar κ A b t s k =
      SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  obtain ⟨-, hr, -⟩ := tree_root_bounds hL2q hcoh
  have hrq : (botLt pstar b : ℝ) ≤ q := by
    unfold botLt; rw [P1.treeRootLayer_eq]; exact_mod_cast hr
  have hlt : (botLt pstar b : ℝ) < t := lt_of_le_of_lt hrq ht
  have hq : botTfam pstar κ A b t s k = extFam (botLt pstar) (botT0 pstar κ A) b t s k := by
    unfold botTfam
    exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [botEt, ht]) hlt s k
  rw [hq, tree_eq_ext κ.δ κ.F hL2q hcoh s k (le_min ht.le (by linarith)) (min_le_right _ _)]
  exact extConst_min _ hrq hlt.le

/-- **Couple below its root layer**: it vanishes for `t ≤ Lr` when `L₂ < Lr`. -/
theorem botQfam_eq_zero {q : ℕ} (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (hgt : zpQ2 A pstar < botLq pstar b) {t : ℝ} (ht : t ≤ (botLq pstar b : ℝ)) (s : ℝ) (k : Mom d) : botQfam pstar κ A b t s k = 0 := by
  unfold botQfam
  by_cases htr : botTrQ pstar b
  · rw [mixFam_of_tq htr]
    unfold botEx
    rw [if_neg (not_lt.2 ht)]
  · rw [mixFam_of_not htr]
    unfold extFam
    rw [extConst_of_le _ ht]
    exact couple_root_vanish κ.δ κ.F hL2q hqp hcoh hgt s k

/-- **Tree below its root layer**: it vanishes for `t ≤ Lr` when `L₂ < Lr`. -/
theorem botTfam_eq_zero {q : ℕ} (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (hgt : zpQ2 A pstar < botLt pstar b) {t : ℝ} (ht : t ≤ (botLt pstar b : ℝ)) (s : ℝ) (k : Mom d) : botTfam pstar κ A b t s k = 0 := by
  unfold botTfam
  by_cases htr : botTrT pstar b
  · rw [mixFam_of_tq htr]
    unfold botEt
    rw [if_neg (not_lt.2 ht)]
  · rw [mixFam_of_not htr]
    unfold extFam
    rw [extConst_of_le _ ht]
    exact tree_root_vanish κ.δ κ.F hL2q hcoh hgt s k

/-- **The couple expansion on `VC`** from a gate expansion at `(q, L₂)`. -/
theorem botQ_expand {q : ℕ} (L4 : ℕ) (hL24 : zpQ2 A pstar ≤ L4) (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    {m : ℕ} (c : ℝ) (Jg : Fin m → (Fin 2 → ℝ) → ℂ) (Mg : Fin m → Mom d → ℝ)
    (hexp : ∀ ts ∈ timeBox (q : ℝ) (zpQ2 A pstar : ℝ), ∀ k,
      SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) (ts 0) (ts 1) k =
        ∑ i, (c : ℂ) * Jg i ts * (Mg i k : ℂ)) :
    ∀ t s : ℝ, ![t, s] ∈ VC q L4 (botLq pstar b) (zpQ2 A pstar) → ∀ k,
      botQfam pstar κ A b t s k = ∑ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k := by
  intro t s hts k
  obtain ⟨⟨hs1, hs2⟩, hcase⟩ := hts
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hcase
  rcases hcase with ht | ⟨h4, hr, hq⟩
  · rw [botQfam_eq_clamp κ A b hL2q hqp hcoh ht s k]
    have hmem : ![min t (q + 1), s] ∈ timeBox (q : ℝ) (zpQ2 A pstar : ℝ) := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      · exact le_min ht.le (by linarith)
      · exact min_le_right _ _
      · exact hs1
      · exact hs2
    have := hexp _ hmem k
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => (sepTerm_clamp_of_ge ht.le k).symm
  · have hgt : zpQ2 A pstar < botLq pstar b := by
      have : (zpQ2 A pstar : ℝ) < botLq pstar b := lt_of_le_of_lt (by exact_mod_cast hL24) (lt_of_lt_of_le h4 hr)
      exact_mod_cast this
    rw [botQfam_eq_zero κ A b hL2q hqp hcoh hgt hr s k]
    exact (Finset.sum_eq_zero fun i _ => sepTerm_clamp_of_lt hq k).symm

/-- **The tree expansion on `VT`** from a gate expansion at `(q, L₂)` on `timeBoxGt`. -/
theorem botT_expand {q : ℕ} (L4 : ℕ) (hL24 : zpQ2 A pstar ≤ L4) (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    {m : ℕ} (c : ℝ) (Jg : Fin m → (Fin 2 → ℝ) → ℂ) (Mg : Fin m → Mom d → ℝ)
    (hexp : ∀ ts ∈ timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ), ∀ k,
      SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) (ts 0) (ts 1) k =
        ∑ i, (c : ℂ) * Jg i ts * (Mg i k : ℂ)) :
    ∀ t s : ℝ, ![t, s] ∈ VT q L4 (botLt pstar b) (zpQ2 A pstar) → ∀ k,
      botTfam pstar κ A b t s k = ∑ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k := by
  intro t s hts k
  obtain ⟨⟨hs1, hs2⟩, hcase⟩ := hts
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hcase
  rcases hcase with ⟨ht, hst⟩ | ⟨h4, hr, hq⟩
  · rw [botTfam_eq_clamp κ A b hL2q hcoh ht s k]
    have hmem : ![min t (q + 1), s] ∈ timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ) := by
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      · exact le_min ht.le (by linarith)
      · exact min_le_right _ _
      · exact hs1
      · exact hs2.le
      · exact hst
    have := hexp _ hmem k
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => (sepTerm_clamp_of_ge ht.le k).symm
  · have hgt : zpQ2 A pstar < botLt pstar b := by
      have : (zpQ2 A pstar : ℝ) < botLt pstar b := lt_of_le_of_lt (by exact_mod_cast hL24) (lt_of_lt_of_le h4 hr)
      exact_mod_cast this
    rw [botTfam_eq_zero κ A b hL2q hcoh hgt hr s k]
    exact (Finset.sum_eq_zero fun i _ => sepTerm_clamp_of_lt hq k).symm

end


end WaveTurbulence.VineEstS5C.P4.W13
