/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GateH
public import WaveTurbulence.Foundations.VineEst.VineEstS3.GateRows
public import WaveTurbulence.Foundations.VineEst.CoupleRowConj

/-! # Row bounds of `K*_Q`, `K*_T` for the layer family `h` with leaf cost (Step 3 port, R45)

Copy-and-edit of `VineEstS3.GateRows`/`SepBound`/`CoupleRowConj` from the common-profile gates to
`CoherentGateH`/`IncoherentGateH`: every bound gains the factor `layerCost Bh LG`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.PL2330 WaveTurbulence.LGSpine WaveTurbulence.Fourier
  WaveTurbulence.NormBridgeScratch WaveTurbulence.VineEstS3 MeasureTheory Set
open scoped ENNReal

theorem rowB_nonneg' {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) : 0 ≤ rowB P n g := by
  have : 0 ≤ rowCb P := by unfold rowCb; have := cLeib_nonneg P.d (30 * P.d); linarith
  unfold rowB
  have : 0 ≤ P.C₁ := by linarith
  positivity

theorem spatialNorm_sepL_le {P : WTParams} (hd : 1 ≤ P.d) {n W : ℕ} {M : Mom P.d → ℝ} {X : ℝ}
    (hM : SNormR (30 * P.d) W M ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * X)) (hδ : 0 ≤ P.δ) (hC : 0 ≤ P.C₁) :
    spatialNorm (30 * P.d) W (fun k => ((P.δ ^ n : ℂ) * (M k : ℂ))) ≤
      ENNReal.ofReal (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  refine (spatialNorm_const_mul_le hΛ _ _).trans ?_
  have h1 : spatialNorm (30 * P.d) W (fun k => (M k : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * X) := by
    unfold SNormR at hM
    rwa [SNorm_eq_spatialNorm] at hM
  have h2 : ‖((P.δ ^ n : ℂ))‖ₑ = ENNReal.ofReal (P.δ ^ n) := by
    rw [← ofReal_norm]; congr 1; simp [abs_of_nonneg hδ]
  rw [h2]
  calc ENNReal.ofReal (P.δ ^ n) * spatialNorm (30 * P.d) W (fun k => (M k : ℂ))
      ≤ ENNReal.ofReal (P.δ ^ n) * ENNReal.ofReal (P.C₁ * P.C₁ ^ n * X) := mul_le_mul_right h1 _
    _ = _ := (ENNReal.ofReal_mul (pow_nonneg hδ n)).symm

theorem rN_sepLTerm_le {P : WTParams} (hd : 1 ≤ P.d) {n W : ℕ} {M : Mom P.d → ℝ} {J : (Fin 2 → ℝ) → ℂ}
    {B : Set (Fin 2 → ℝ)} {θ : ℝ} {X : ℝ} (hX : 0 ≤ X) (hθ : θ ≤ 1 - P.η) (hC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    (hM : SNormR (30 * P.d) W M ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * X))
    (hJ : XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J ts) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) :
    rN θ (30 * P.d) W B (fun t k => ((P.δ ^ n : ℂ) * (M k : ℂ)) * J t) ≤
      ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n)) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hJi : rN θ (30 * P.d) 0 B (fun t (_ : Mom P.d) => J t) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) := by
    refine (rN_const_param_le B J).trans ?_
    have h1 := mixedRestrictionNorm00_mono_time (V := Unit) hθ B Set.univ (fun ts _ => J ts)
    have h2 := (XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) B Set.univ (fun (ts : Fin 2 → ℝ) (_ : Unit) => J ts)).symm.le
    exact h1.trans (h2.trans hJ)
  have hCn : 0 ≤ P.δ ^ n * (P.C₁ * P.C₁ ^ n * X) := by positivity
  exact restr_mul_w_le hΛ hd (θ := θ) W B (c := fun k => ((P.δ ^ n : ℂ) * (M k : ℂ)))
    (fun t _ => J t) hCn (spatialNorm_sepL_le hd hM hδ hC) hJi

theorem rN_leafSeparated_le {P : WTParams} {n W : ℕ} {B : Set (Fin 2 → ℝ)}
    {f : (Fin 2 → ℝ) → Mom P.d → ℂ} {X : ℝ} (hX : 0 ≤ X) (hf : LeafwiseSeparated P n W B f X) (hd : 1 ≤ P.d)
    {θ : ℝ} (hθ : θ ≤ 1 - P.η) (hC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    rN θ (30 * P.d) W B f ≤
      ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n))) := by
  classical
  obtain ⟨m, J, M, hm, hfeq, hJ, hM⟩ := hf
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hsum : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), f ts k =
      ∑ i ∈ (Finset.univ : Finset (Fin m)), ((P.δ ^ n : ℂ) * (M i k : ℂ)) * J i ts := by
    intro ts hts k _
    rw [hfeq ts hts k]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set Fi : Fin m → (Fin 2 → ℝ) → Mom P.d → ℂ := fun i t k => ((P.δ ^ n : ℂ) * (M i k : ℂ)) * J i t with hFi
  have e1 : rN θ (30 * P.d) W B f = rN θ (30 * P.d) W B (fun t k => ∑ i ∈ (Finset.univ : Finset (Fin m)), Fi i t k) :=
    restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := W) B Set.univ hsum
  have e2 : rN θ (30 * P.d) W B (fun t k => ∑ i ∈ (Finset.univ : Finset (Fin m)), Fi i t k) ≤
      ∑ i ∈ (Finset.univ : Finset (Fin m)), rN θ (30 * P.d) W B (Fi i) :=
    restr_finsetSum_le (θ := θ) (Λ := 30 * P.d) (Λ₂ := W) hΛ Finset.univ B Set.univ Fi
  have e3 : ∀ i ∈ (Finset.univ : Finset (Fin m)), rN θ (30 * P.d) W B (Fi i) ≤
      ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n)) :=
    fun i _ => rN_sepLTerm_le hd hX hθ hC hδ (hM i) (hJ i)
  refine e1.trans_le (e2.trans ((Finset.sum_le_sum e3).trans ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnn : 0 ≤ cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n) := by
    have := cLeib_nonneg P.d (30 * P.d)
    positivity
  calc (m : ℝ≥0∞) * ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n))
      ≤ 2 ^ n * ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n)) := by
        gcongr; exact_mod_cast hm
    _ = _ := by
        rw [show (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]

/-- The coherent total with cost: `(regBound n 1 + sep) X ≤ rowB n 0 X`. -/
theorem coherent_total_leaf_le {P : WTParams} {X : ℝ} (hX : 0 ≤ X) (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (n : ℕ) :
    regBound P n 1 * ENNReal.ofReal X + ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) *
      (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n))) ≤ ENNReal.ofReal (rowB P n 0 * X) := by
  have hc : 0 < P.C₁ := by linarith
  have hLb := cLeib_nonneg P.d (30 * P.d)
  have h := coherent_total_le hC hδ hL hw n
  have e : ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n))) =
      ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n)) * (P.C₁ * P.C₁ ^ n))) *
        ENNReal.ofReal X := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  rw [e, ← add_mul, ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) n 0)]
  exact mul_le_mul' h le_rfl

/-- The coherent case with cost: kernel = (kernel - app) + app. -/
theorem coherent_case_leaf_le {P : WTParams} (hd : 1 ≤ P.d) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {n W : ℕ} {X : ℝ}
    (hX : 0 ≤ X) {B : Set (Fin 2 → ℝ)} {K App : (Fin 2 → ℝ) → Mom P.d → ℂ}
    (hK : XNormRestr P.η (30 * P.d) W B Set.univ (fun ts k => K ts k - App ts k) ≤ regBound P n 1 * ENNReal.ofReal X)
    (hsep : LeafwiseSeparated P n W B App X) :
    XNormRestr P.η (30 * P.d) W B Set.univ K ≤ ENNReal.ofReal (rowB P n 0 * X) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  rw [XNormRestr_eq_rN]
  have hsplit : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), K ts k = (K ts k - App ts k) + App ts k := by
    intro ts _ k _; ring
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := W) B Set.univ hsplit).trans_le ?_
  refine (restr_add_le hΛ B Set.univ (fun ts k => K ts k - App ts k) App).trans ?_
  have h1 : rN P.η (30 * P.d) W B (fun ts k => K ts k - App ts k) ≤ regBound P n 1 * ENNReal.ofReal X := by
    rw [← XNormRestr_eq_rN]; exact hK
  have h2 : rN P.η (30 * P.d) W B App ≤
      ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * X)) * (P.C₁ * P.C₁ ^ n))) :=
    rN_leafSeparated_le hX hsep hd (by linarith) (by linarith) hδ
  exact (add_le_add h1 h2).trans (coherent_total_leaf_le hX hC hδ hL hw n)

/-- The non-dominant coherent case with cost: the app vanishes. -/
theorem coherent_case_zero_leaf_le {P : WTParams} (hd : 1 ≤ P.d) (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {n W : ℕ} {X : ℝ} (hX : 0 ≤ X)
    {B : Set (Fin 2 → ℝ)} {K App : (Fin 2 → ℝ) → Mom P.d → ℂ}
    (hK : XNormRestr P.η (30 * P.d) W B Set.univ (fun ts k => K ts k - App ts k) ≤ regBound P n 1 * ENNReal.ofReal X)
    (h0 : ∀ ts ∈ B, ∀ k, App ts k = 0) :
    XNormRestr P.η (30 * P.d) W B Set.univ K ≤ ENNReal.ofReal (rowB P n 0 * X) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  rw [XNormRestr_eq_rN]
  have hsplit : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), K ts k = (K ts k - App ts k) + 0 := by
    intro ts hts k _; rw [h0 ts hts k]; ring
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := W) B Set.univ hsplit).trans_le ?_
  refine (restr_add_le hΛ B Set.univ (fun ts k => K ts k - App ts k) (fun _ _ => 0)).trans ?_
  have h1 : rN P.η (30 * P.d) W B (fun ts k => K ts k - App ts k) ≤ regBound P n 1 * ENNReal.ofReal X := by
    rw [← XNormRestr_eq_rN]; exact hK
  have h2 : rN P.η (30 * P.d) W B (fun (_ : Fin 2 → ℝ) (_ : Mom P.d) => (0 : ℂ)) = 0 := restr_zero B Set.univ
  refine (add_le_add h1 h2.le).trans ?_
  rw [add_zero, ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) n 0)]
  refine mul_le_mul' ((regBound_le_rowB (P := P) hC hδ (by linarith) n 1).trans (ENNReal.ofReal_le_ofReal ?_)) le_rfl
  have hc : 0 < P.C₁ := by linarith
  unfold rowB
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

theorem layerCost_nonneg_of {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    {w : ℕ} (LG : LayeredGarden w) (hlay : ∀ x, LG.layer x ≤ p) : 0 ≤ layerCost Bh LG :=
  layerCost_nonneg LG fun x => (hB _ (hlay x)).1

/-- **Row bound for a regular couple** (layer family, leaf cost). -/
theorem couple_row_leaf_le {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqp : q ≤ p) (hq'p : q' ≤ p)
    (hwf : Q.wf = true) (hsize : Q.size = 2 * n) (hdec : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcoh : LG.incoherency Q.links = 0 → q' ≤ q ∧ IsCoherentCoupleAt p q q' Q LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency Q.links) * layerCost Bh LG) := by
  have hL0 : 0 ≤ P.L := by linarith
  have hX := layerCost_nonneg_of hB LG hlay
  refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
  by_cases hg : LG.incoherency Q.links = 0
  · obtain ⟨hqq, hcq⟩ := hcoh hg
    obtain ⟨hK, hdom, hsep⟩ := (hgate h Bh p hp hB n hn).1 Q LG q q' hqq hqp hsize hcq
    rw [hg]
    by_cases hD : Q.dominant = true
    · exact coherent_case_leaf_le hd hη2 hC hδ hL hw hX hK hsep
    · exact coherent_case_zero_leaf_le hd hC hδ hL hw hX hK (hdom (by simpa using hD))
  · have hg1 : 1 ≤ LG.incoherency Q.links := Nat.one_le_iff_ne_zero.mpr hg
    refine ((hinc h Bh p hp hB n hn).1 Q hwf hsize LG hdec hlay q q' hqp hq'p hr0 hr1 hg1).trans ?_
    rw [ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) n _)]
    exact mul_le_mul' (regBound_le_rowB hC hδ hL0 n _) le_rfl

/-- **Row bound for a regular tree** (layer family, leaf cost). -/
theorem tree_row_leaf_le {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {X : RegChain} {LG : LayeredGarden 1} {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hwf : X.wf = true) (hsize : X.size = 2 * n) (hdec : X.DecodesTree LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hlone : ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q')
    (hcoh : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 → IsCoherentTreeAt p q q' X LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0 (timeBoxGt q q') Set.univ
      (fun ts k => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) * layerCost Bh LG) := by
  have hL0 : 0 ≤ P.L := by linarith
  have hX := layerCost_nonneg_of hB LG hlay
  refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
  by_cases hg : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0
  · have hcq := hcoh hg
    obtain ⟨hK, hdom, hsep⟩ := (hgate h Bh p hp hB n hn).2 X LG q q' hqq hqp hsize hcq
    rw [hg]
    by_cases hD : X.dominant = true
    · exact coherent_case_leaf_le hd hη2 hC hδ hL hw hX hK hsep
    · exact coherent_case_zero_leaf_le hd hC hδ hL hw hX hK (hdom (by simpa using hD))
  · have hg1 : 1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) := Nat.one_le_iff_ne_zero.mpr hg
    refine ((hinc h Bh p hp hB n hn).2 X hwf hsize LG hdec hlay q q' hqq hqp hr0 hlone hg1).trans ?_
    rw [ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) n _)]
    exact mul_le_mul' (regBound_le_rowB hC hδ hL0 n _) le_rfl

end WaveTurbulence.VineEstS5C
