/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Gate30d
public import WaveTurbulence.Foundations.VineEst.VineEstS3.IncoherentGate
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SepBound

/-! # Row bounds of `K*_Q`, `K*_T` from the Prop 6.1 (30d) and Prop 5.1 gates (Step 3, gate matching)

`couple_row_le`, `tree_row_le`: for an eligible regular object of order `n` and incoherency index `g`, the restriction
norm `𝔛^{6η⁶,30d,·}(box)` of its starred kernel is at most `rowB P n g = cb C₁² (2C₁²δ)ⁿ L^{-(γ₁-√η)g}`.
For `g ≥ 1` this is B2.2 (`IncoherentGateAt`); for `g = 0` it is the 30d Prop 6.1 gate plus the separated bound.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.PL2330 WaveTurbulence.LGSpine WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

/-- The row constant `1 + (2d)^{30d}`. -/
noncomputable def rowCb (P : WTParams) : ℝ := 1 + cLeib P.d (30 * P.d)

/-- The row bound `cb C₁² (2C₁²δ)ⁿ L^{-(γ₁-√η) g}`. -/
noncomputable def rowB (P : WTParams) (n g : ℕ) : ℝ :=
  rowCb P * P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))

theorem rowB_pos {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (n g : ℕ) : 0 < rowB P n g := by
  have : 0 < rowCb P := by unfold rowCb; have := cLeib_nonneg P.d (30 * P.d); linarith
  unfold rowB
  have : 0 < P.C₁ := by linarith
  positivity

theorem regBound_le_rowB {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) :
    regBound P n g ≤ ENNReal.ofReal (rowB P n g) := by
  unfold regBound
  apply ENNReal.ofReal_le_ofReal
  unfold rowB rowCb
  have hc : 0 < P.C₁ := by linarith
  have hLb := cLeib_nonneg P.d (30 * P.d)
  have h1 : (P.C₁ * P.δ) ^ n ≤ (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (P.C₁ - 1)]
  have h2 : P.C₁ ≤ (1 + cLeib P.d (30 * P.d)) * P.C₁ ^ 2 := by nlinarith
  have h3 : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg hL _
  calc P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
      ≤ ((1 + cLeib P.d (30 * P.d)) * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by
        gcongr
    _ = _ := by ring

/-- The coherent total: `regBound P n 1 + (separated bound) ≤ rowB P n 0`. -/
theorem coherent_total_le {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (n : ℕ) :
    regBound P n 1 + ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n)) *
      (P.C₁ * P.C₁ ^ n))) ≤ ENNReal.ofReal (rowB P n 0) := by
  have hc : 0 < P.C₁ := by linarith
  have hLb := cLeib_nonneg P.d (30 * P.d)
  have hL0 : 0 ≤ P.L := by linarith
  have hreg : regBound P n 1 ≤ ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n) := by
    unfold regBound
    apply ENNReal.ofReal_le_ofReal
    have : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hL
      push_cast; nlinarith
    calc P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ))
        ≤ P.C₁ * (P.C₁ * P.δ) ^ n * 1 := by gcongr
      _ = _ := mul_one _
  refine (add_le_add_left hreg _).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold rowB rowCb
  have h1 : (P.C₁ * P.δ) ^ n ≤ (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (P.C₁ - 1)]
  have h0 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((0 : ℕ) : ℝ)) = 1 := by simp
  rw [h0]
  have e2 : (2 : ℝ) ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n)) * (P.C₁ * P.C₁ ^ n)) =
      cLeib P.d (30 * P.d) * (P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n) := by
    rw [mul_pow, mul_pow]; ring
  rw [e2]
  have : P.C₁ * (P.C₁ * P.δ) ^ n ≤ P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    calc P.C₁ * (P.C₁ * P.δ) ^ n ≤ P.C₁ ^ 2 * (P.C₁ * P.δ) ^ n := by gcongr; nlinarith
      _ ≤ _ := by gcongr
  nlinarith

/-- The coherent case: kernel = (kernel - app) + app, with the Prop 6.1 error bound and the separated app. -/
theorem coherent_case_le {P : WTParams} (hd : 1 ≤ P.d) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {n W : ℕ}
    {B : Set (Fin 2 → ℝ)} {K App : (Fin 2 → ℝ) → Mom P.d → ℂ}
    (hK : XNormRestr P.η (30 * P.d) W B Set.univ (fun ts k => K ts k - App ts k) ≤ regBound P n 1)
    (hsep : LGSpine.SourceSeparated P n W B App) :
    XNormRestr P.η (30 * P.d) W B Set.univ K ≤ ENNReal.ofReal (rowB P n 0) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  rw [XNormRestr_eq_rN]
  have hsplit : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), K ts k = (K ts k - App ts k) + App ts k := by
    intro ts _ k _; ring
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := W) B Set.univ hsplit).trans_le ?_
  refine (restr_add_le hΛ B Set.univ (fun ts k => K ts k - App ts k) App).trans ?_
  have h1 : rN P.η (30 * P.d) W B (fun ts k => K ts k - App ts k) ≤ regBound P n 1 := by
    rw [← XNormRestr_eq_rN]; exact hK
  have h2 : rN P.η (30 * P.d) W B App ≤
      ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n)) * (P.C₁ * P.C₁ ^ n))) :=
    rN_sourceSeparated_le hsep hd (by linarith) (by linarith) hδ
  exact (add_le_add h1 h2).trans (coherent_total_le hC hδ hL hw n)

/-- The non-dominant coherent case: the app vanishes. -/
theorem coherent_case_zero_le {P : WTParams} (hd : 1 ≤ P.d) (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {n W : ℕ}
    {B : Set (Fin 2 → ℝ)} {K App : (Fin 2 → ℝ) → Mom P.d → ℂ}
    (hK : XNormRestr P.η (30 * P.d) W B Set.univ (fun ts k => K ts k - App ts k) ≤ regBound P n 1)
    (h0 : ∀ ts ∈ B, ∀ k, App ts k = 0) :
    XNormRestr P.η (30 * P.d) W B Set.univ K ≤ ENNReal.ofReal (rowB P n 0) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  rw [XNormRestr_eq_rN]
  have hsplit : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), K ts k = (K ts k - App ts k) + 0 := by
    intro ts hts k _; rw [h0 ts hts k]; ring
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := W) B Set.univ hsplit).trans_le ?_
  refine (restr_add_le hΛ B Set.univ (fun ts k => K ts k - App ts k) (fun _ _ => 0)).trans ?_
  have h1 : rN P.η (30 * P.d) W B (fun ts k => K ts k - App ts k) ≤ regBound P n 1 := by
    rw [← XNormRestr_eq_rN]; exact hK
  have h2 : rN P.η (30 * P.d) W B (fun (_ : Fin 2 → ℝ) (_ : Mom P.d) => (0 : ℂ)) = 0 := restr_zero B Set.univ
  refine (add_le_add h1 h2.le).trans ?_
  rw [add_zero]
  have := regBound_le_rowB (P := P) hC hδ (by linarith) n 1
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold rowB
  have hc : 0 < P.C₁ := by linarith
  have h0' : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hL
    push_cast; nlinarith
  have h00 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((0 : ℕ) : ℝ)) = 1 := by simp
  rw [h00]
  have hpos : 0 ≤ rowCb P * P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    have : 0 < rowCb P := by unfold rowCb; have := cLeib_nonneg P.d (30 * P.d); linarith
    positivity
  calc rowCb P * P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ))
      ≤ rowCb P * P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n * 1 := by gcongr
    _ = _ := by ring

/-- **Row bound for a regular couple.** -/
theorem couple_row_le {P : WTParams} (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ → Mom P.d → ℝ} (hR : ∀ r ≤ p, InputRemainder P (R r) r)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqp : q ≤ p) (hq'p : q' ≤ p)
    (hwf : Q.wf = true) (hsize : Q.size = 2 * n) (hdec : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcoh : LG.incoherency Q.links = 0 → q' ≤ q ∧ IsCoherentCoupleAt p q q' Q LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency Q.links)) := by
  have hL0 : 0 ≤ P.L := by linarith
  refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
  by_cases hg : LG.incoherency Q.links = 0
  · obtain ⟨hqq, hcq⟩ := hcoh hg
    obtain ⟨hK, hdom, hsep⟩ := (hgate p hp R hR n hn).1 Q LG q q' hqq hqp hsize hcq
    rw [hg]
    by_cases hD : Q.dominant = true
    · exact coherent_case_le hd hη2 hC hδ hL hw hK hsep
    · exact coherent_case_zero_le hd hC hδ hL hw hK (hdom (by simpa using hD))
  · have hg1 : 1 ≤ LG.incoherency Q.links := Nat.one_le_iff_ne_zero.mpr hg
    exact ((hinc p hp R hR n hn).1 Q hwf hsize LG hdec hlay q q' hqp hq'p hr0 hr1 hg1).trans
      (regBound_le_rowB hC hδ hL0 n _)

/-- **Row bound for a regular tree.** -/
theorem tree_row_le {P : WTParams} (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ → Mom P.d → ℝ} (hR : ∀ r ≤ p, InputRemainder P (R r) r)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {X : RegChain} {LG : LayeredGarden 1} {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hwf : X.wf = true) (hsize : X.size = 2 * n) (hdec : X.DecodesTree LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hlone : ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q')
    (hcoh : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 → IsCoherentTreeAt p q q' X LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0 (timeBoxGt q q') Set.univ
      (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency (X.treeLinks (LG.garden.sig 0)))) := by
  have hL0 : 0 ≤ P.L := by linarith
  refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
  by_cases hg : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0
  · have hcq := hcoh hg
    obtain ⟨hK, hdom, hsep⟩ := (hgate p hp R hR n hn).2 X LG q q' hqq hqp hsize hcq
    rw [hg]
    by_cases hD : X.dominant = true
    · exact coherent_case_le hd hη2 hC hδ hL hw hK hsep
    · exact coherent_case_zero_le hd hC hδ hL hw hK (hdom (by simpa using hD))
  · have hg1 : 1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) := Nat.one_le_iff_ne_zero.mpr hg
    exact ((hinc p hp R hR n hn).2 X hwf hsize LG hdec hlay q q' hqq hqp hr0 hlone hg1).trans
      (regBound_le_rowB hC hδ hL0 n _)

end WaveTurbulence.VineEstS3
