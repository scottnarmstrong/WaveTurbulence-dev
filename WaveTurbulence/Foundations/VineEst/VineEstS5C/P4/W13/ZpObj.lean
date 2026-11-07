/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ZpGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ObjExp
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Rem

/-! # P4-W1: the approximant families `zpQfam`, `zpTfam` against a gate expansion at a gate level `q` (TARGET L1893-L1925)

For an index `b` whose carrier-side couple (tree) is coherent at `(q, L₂)` with `L₂ ≤ q ≤ p`, and `Lr` its root layer:

* above `q` the approximant is the source approximant at `(q, L₂)` evaluated at the clamped time `min t (q+1)` (P1's extension
  lemma `couple_eq_ext`/`tree_eq_ext` plus the constant extension past `Lr + 1 ≤ q + 1`; R35: for `t > q ≥ Lr` the trivial exact
  kernel `F 1_{t > Lr}` equals the extension): `zpQfam_eq_clamp`, `zpTfam_eq_clamp`;
* between `L₄` and `Lr` (when `L₂ ≤ L₄ < Lr`) it vanishes (`couple_root_vanish`, `tree_root_vanish`): `zpQfam_eq_zero`, `zpTfam_eq_zero`.

`clampJ q J`: the time factor `0` below `q` and `J(min t (q+1), s)` from `q` on.  `VC`, `VT`: the identity sets.  `zpQ_expand`,
`zpT_expand`: a gate expansion `SourceApp = ∑ c Jᵢ Mᵢ` on `timeBox q L₂` (`timeBoxGt` for trees) gives
`zpQfam b t s k = ∑ᵢ sepTerm c (clampJ q Jᵢ) Mᵢ t s k` on `VC` (`VT`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS4c
  WaveTurbulence.VineEstS5C.P2

set_option linter.unusedSectionVars false

/-- The clamped time factor: `0` below `q`, `J(min t (q+1), s)` from `q` on. -/
noncomputable def clampJ (q : ℝ) (J : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ := fun ts =>
  if ts 0 < q then 0 else J ![min (ts 0) (q + 1), ts 1]

/-- The identity set of a couple: `s ∈ [L₂, L₂+1]` and `t > q`, or `L₄ < t ≤ Lr`, `t < q` (vanishing range). -/
def VC (q L4 Lr L2 : ℝ) : Set (Fin 2 → ℝ) :=
  {ts | (L2 ≤ ts 1 ∧ ts 1 ≤ L2 + 1) ∧ (q < ts 0 ∨ (L4 < ts 0 ∧ ts 0 ≤ Lr ∧ ts 0 < q))}

/-- The identity set of a tree: as `VC`, with `s < min t (q+1)` above `q`. -/
def VT (q L4 Lr L2 : ℝ) : Set (Fin 2 → ℝ) :=
  {ts | (L2 ≤ ts 1 ∧ ts 1 < L2 + 1) ∧ ((q < ts 0 ∧ ts 1 < min (ts 0) (q + 1)) ∨ (L4 < ts 0 ∧ ts 0 ≤ Lr ∧ ts 0 < q))}

theorem extConst_min {α : Type*} {L q t : ℝ} (F : ℝ → α) (hLq : L ≤ q) (hLt : L ≤ t) :
    extConst L F t = extConst L F (min t (q + 1)) := by
  unfold extConst
  have h1 : max t L = t := max_eq_left hLt
  have h2 : max (min t (q + 1)) L = min t (q + 1) := max_eq_left (le_min hLt (by linarith))
  rw [h1, h2]
  congr 1
  rw [min_assoc, min_eq_right (by linarith : L + 1 ≤ q + 1)]

section
variable {w : ℕ} {ι : Type*} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι] {p : ℕ} {kind : Bool}
  (κ : KPar d) (A : FamilyReconstruction w ι) (b : ST w ι pstar J)

/-- **Couple above the gate level**: `zpQfam b t = SourceApp(q, L₂)(min t (q+1))` for `t > q`. -/
theorem zpQfam_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    zpQfam κ A b t s k =
      SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  have hr := cpl_root_bounds hL2q hqp hcoh
  have hrq : (zpLq b : ℝ) ≤ q := by exact_mod_cast hr.2
  have hlt : (zpLq b : ℝ) < t := lt_of_le_of_lt hrq ht
  have hq : zpQfam κ A b t s k = extFam zpLq (zpQ0 κ A) b t s k := by
    unfold zpQfam
    exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [zpEx, ht]) hlt s k
  rw [hq, couple_eq_ext κ.δ κ.F hL2q hqp hcoh s k (le_min ht.le (by linarith)) (min_le_right _ _)]
  exact extConst_min _ hrq hlt.le

/-- **Tree above the gate level**. -/
theorem zpTfam_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    zpTfam κ A b t s k =
      SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  obtain ⟨-, hr, -⟩ := tree_root_bounds hL2q hcoh
  have hrq : (zpLt b : ℝ) ≤ q := by
    unfold zpLt; rw [P1.treeRootLayer_eq]; exact_mod_cast hr
  have hlt : (zpLt b : ℝ) < t := lt_of_le_of_lt hrq ht
  have hq : zpTfam κ A b t s k = extFam zpLt (zpT0 κ A) b t s k := by
    unfold zpTfam
    exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [zpEt, ht]) hlt s k
  rw [hq, tree_eq_ext κ.δ κ.F hL2q hcoh s k (le_min ht.le (by linarith)) (min_le_right _ _)]
  exact extConst_min _ hrq hlt.le

/-- **Couple below its root layer**: it vanishes for `t ≤ Lr` when `L₂ < Lr`. -/
theorem zpQfam_eq_zero {q : ℕ} (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (hgt : zpQ2 A pstar < zpLq b) {t : ℝ} (ht : t ≤ (zpLq b : ℝ)) (s : ℝ) (k : Mom d) : zpQfam κ A b t s k = 0 := by
  unfold zpQfam
  by_cases htr : zpTrQ b
  · rw [mixFam_of_tq htr]
    unfold zpEx
    rw [if_neg (not_lt.2 ht)]
  · rw [mixFam_of_not htr]
    unfold extFam
    rw [extConst_of_le _ ht]
    exact couple_root_vanish κ.δ κ.F hL2q hqp hcoh hgt s k

/-- **Tree below its root layer**: it vanishes for `t ≤ Lr` when `L₂ < Lr`. -/
theorem zpTfam_eq_zero {q : ℕ} (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (hgt : zpQ2 A pstar < zpLt b) {t : ℝ} (ht : t ≤ (zpLt b : ℝ)) (s : ℝ) (k : Mom d) : zpTfam κ A b t s k = 0 := by
  unfold zpTfam
  by_cases htr : zpTrT b
  · rw [mixFam_of_tq htr]
    unfold zpEt
    rw [if_neg (not_lt.2 ht)]
  · rw [mixFam_of_not htr]
    unfold extFam
    rw [extConst_of_le _ ht]
    exact tree_root_vanish κ.δ κ.F hL2q hcoh hgt s k

theorem sepTerm_clamp_of_ge {q : ℝ} {c : ℝ} {Jf : (Fin 2 → ℝ) → ℂ} {M : Mom d → ℝ} {t s : ℝ} (ht : q ≤ t) (k : Mom d) :
    sepTerm c (clampJ q Jf) M t s k = (c : ℂ) * Jf ![min t (q + 1), s] * (M k : ℂ) := by
  unfold sepTerm clampJ
  simp [not_lt.2 ht]

theorem sepTerm_clamp_of_lt {q : ℝ} {c : ℝ} {Jf : (Fin 2 → ℝ) → ℂ} {M : Mom d → ℝ} {t s : ℝ} (ht : t < q) (k : Mom d) :
    sepTerm c (clampJ q Jf) M t s k = 0 := by
  unfold sepTerm clampJ
  simp [ht]

/-- **The couple expansion on `VC`** from a gate expansion at `(q, L₂)`. -/
theorem zpQ_expand {q : ℕ} (L4 : ℕ) (hL24 : zpQ2 A pstar ≤ L4) (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    {m : ℕ} (c : ℝ) (Jg : Fin m → (Fin 2 → ℝ) → ℂ) (Mg : Fin m → Mom d → ℝ)
    (hexp : ∀ ts ∈ timeBox (q : ℝ) (zpQ2 A pstar : ℝ), ∀ k,
      SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) (ts 0) (ts 1) k =
        ∑ i, (c : ℂ) * Jg i ts * (Mg i k : ℂ)) :
    ∀ t s : ℝ, ![t, s] ∈ VC q L4 (zpLq b) (zpQ2 A pstar) → ∀ k,
      zpQfam κ A b t s k = ∑ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k := by
  intro t s hts k
  obtain ⟨⟨hs1, hs2⟩, hcase⟩ := hts
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hcase
  rcases hcase with ht | ⟨h4, hr, hq⟩
  · rw [zpQfam_eq_clamp κ A b hL2q hqp hcoh ht s k]
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
  · have hgt : zpQ2 A pstar < zpLq b := by
      have : (zpQ2 A pstar : ℝ) < zpLq b := lt_of_le_of_lt (by exact_mod_cast hL24) (lt_of_lt_of_le h4 hr)
      exact_mod_cast this
    rw [zpQfam_eq_zero κ A b hL2q hqp hcoh hgt hr s k]
    exact (Finset.sum_eq_zero fun i _ => sepTerm_clamp_of_lt hq k).symm

/-- **The tree expansion on `VT`** from a gate expansion at `(q, L₂)` on `timeBoxGt`. -/
theorem zpT_expand {q : ℕ} (L4 : ℕ) (hL24 : zpQ2 A pstar ≤ L4) (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    {m : ℕ} (c : ℝ) (Jg : Fin m → (Fin 2 → ℝ) → ℂ) (Mg : Fin m → Mom d → ℝ)
    (hexp : ∀ ts ∈ timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ), ∀ k,
      SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) (ts 0) (ts 1) k =
        ∑ i, (c : ℂ) * Jg i ts * (Mg i k : ℂ)) :
    ∀ t s : ℝ, ![t, s] ∈ VT q L4 (zpLt b) (zpQ2 A pstar) → ∀ k,
      zpTfam κ A b t s k = ∑ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k := by
  intro t s hts k
  obtain ⟨⟨hs1, hs2⟩, hcase⟩ := hts
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hcase
  rcases hcase with ⟨ht, hst⟩ | ⟨h4, hr, hq⟩
  · rw [zpTfam_eq_clamp κ A b hL2q hcoh ht s k]
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
  · have hgt : zpQ2 A pstar < zpLt b := by
      have : (zpQ2 A pstar : ℝ) < zpLt b := lt_of_le_of_lt (by exact_mod_cast hL24) (lt_of_lt_of_le h4 hr)
      exact_mod_cast this
    rw [zpTfam_eq_zero κ A b hL2q hcoh hgt hr s k]
    exact (Finset.sum_eq_zero fun i _ => sepTerm_clamp_of_lt hq k).symm

end

end WaveTurbulence.VineEstS5C.P4.W13
