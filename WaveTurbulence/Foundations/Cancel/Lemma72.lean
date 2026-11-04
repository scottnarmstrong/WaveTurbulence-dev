/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Lemma73

/-!
# DH21 Lemma 7.2: the non-dominant regular chain integrates to zero

For a legal partition `𝒫` that is not dominant, DH21 Lemma 7.2 (L1726–L1731) states that each term
`K̃ = Ĩ_Z(e^{πiλ₀s})(t)` of the Lemma 5.10 expansion is in `L¹(α[W])` and has integral `0`.

The proof follows DH21. A non-dominant code has a non-adjacent pair `j` on its top spine
(`exists_regTo_tildeP`). Its variable `α_j` enters `Ĩ_Z` only through the sandwich
`I_{ε_jα_j} Ĩ' I_{μ_j-ε_jα_j}`. The Gaussian regularization in `α_j` of that sandwich tends to `0`
(`regTo_sand`, DH21 Lemma 7.1). Fubini then gives `∫ K̃ dα[W] = 0`.

* `tildeP_congr_vars`: `Ĩ_Z` depends only on the variables `α_j` of its pairs.
* `exists_regTo_tildeP`: the regularization in the variable of a non-adjacent spine pair.
* `regchaincancel2`: **DH21 Lemma 7.2**.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

section Vars

variable {P : Type*} {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem piece58_congr_vars (Z : Finset ℕ) (j : ℕ) (p : P) {α α' : V → ℝ}
    (h : α (σ j) = α' (σ j)) : piece58 σ ε μf Z j p α = piece58 σ ε μf Z j p α' := by
  unfold piece58
  split_ifs
  · rfl
  · funext t s
    simp only [TR58, sw0, phiQ, T0]
    rw [h]

theorem sandw_congr_vars (e : ℤ) (v : V) (m : P → ℝ) {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (p : P)
    {α α' : V → ℝ} (hv : α v = α' v) (hT : T p α = T p α') : sandw e v m T p α = sandw e v m T p α' := by
  simp only [sandw, hv, hT]

/-- **`Ĩ_Z` depends only on the variables of its pairs.** -/
theorem tildeP_congr_vars (Z : Finset ℕ) (p : P) {α α' : V → ℝ} :
    ∀ (c : LegalCode) (q : ℕ), (∀ j, q ≤ j → j < q + c.size → α (σ j) = α' (σ j)) →
      tildeP σ ε μf Z c q p α = tildeP σ ε μf Z c q p α'
  | .nil, _, _ => rfl
  | .node .nil .nil, q, h => piece58_congr_vars Z q p (h q le_rfl (by simp [LegalCode.size]))
  | .node .nil (.node a b), q, h => by
    show kcomp _ _ = kcomp _ _
    have hs : (LegalCode.node LegalCode.nil (LegalCode.node a b)).size = (LegalCode.node a b).size + 1 := by
      simp [LegalCode.size]
    rw [piece58_congr_vars Z q p (h q le_rfl (by omega)),
      tildeP_congr_vars Z p (.node a b) (q + 1) fun j h1 h2 => h j (by omega) (by omega)]
  | .node (.node a b) .nil, q, h => by
    have hs : (LegalCode.node (LegalCode.node a b) LegalCode.nil).size = (LegalCode.node a b).size + 1 := by
      simp [LegalCode.size]
    exact sandw_congr_vars _ _ _ p (h q le_rfl (by omega))
      (tildeP_congr_vars Z p (.node a b) (q + 1) fun j h1 h2 => h j (by omega) (by omega))
  | .node (.node a b) (.node c d), q, h => by
    show kcomp _ _ = kcomp _ _
    have hs : (LegalCode.node (LegalCode.node a b) (LegalCode.node c d)).size =
        (LegalCode.node a b).size + (LegalCode.node c d).size + 1 := rfl
    rw [sandw_congr_vars _ _ _ p (h q le_rfl (by omega))
        (tildeP_congr_vars Z p (.node a b) (q + 1) fun j h1 h2 => h j (by omega) (by omega)),
      tildeP_congr_vars Z p (.node c d) (q + (LegalCode.node a b).size + 1)
        fun j h1 h2 => h j (by omega) (by omega)]

end Vars

/-! ### The regularization in a non-adjacent variable -/

section Spine

variable {P : Type*} {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem domCode_succ (m : ℕ) : domCode (m + 1) = .node .nil (domCode m) := rfl

/-- If `node nil r` is not dominant, neither is `r`. -/
theorem nondom_rest {r : LegalCode} (h : ∀ m, LegalCode.node .nil r ≠ domCode m) :
    ∀ m, r ≠ domCode m := fun m hm => h (m + 1) (by rw [hm, domCode_succ])

theorem not_mem_adjSet_self_of_inner {a b r : LegalCode} {q : ℕ} :
    q ∉ adjSet (.node (.node a b) r) q := by
  intro h
  simp only [adjSet, Finset.mem_union] at h
  rcases h with h | h
  · have := (mem_adjSet _ _ _ h).1; omega
  · have := (mem_adjSet _ _ _ h).1; omega

theorem sandw_keqOn_sandK (e : ℤ) (v : V) (m : P → ℝ) {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (p : P)
    (α : V → ℝ) (x : ℝ) (hT : KCont (T p (update α v x))) (hTα : T p (update α v x) = T p α) :
    KEqOn (sandw e v m T p (update α v x)) (sandK e (m p) (T p α) x) := by
  intro t s _ hst _
  rw [sandw_eq_sandK e v m T p _ hT hst, update_self, hTα]

/-- **A non-dominant code has a non-adjacent spine pair `j`**, and the Gaussian regularization in
`α_j` of `Ĩ_Z(g)` tends to `0` (DH21 Lemmas 7.1–7.2). -/
theorem exists_regTo_tildeP (hε : ∀ j, ε j = 1 ∨ ε j = -1) (Z : Finset ℕ) (p : P) :
    ∀ (c : LegalCode) (q : ℕ), (∀ m, c ≠ domCode m) → Set.InjOn σ (Set.Ico q (q + c.size)) →
      ∃ j, q ≤ j ∧ j < q + c.size ∧ j ∉ adjSet c q ∧
        ∀ (α : V → ℝ) {g : ℝ → ℂ}, Continuous g → ∃ Φ : ℝ → ℝ → ℂ, RegTo Φ (fun _ => 0) ∧
          ∀ x, ∀ z ∈ Icc (0 : ℝ) 1,
            volterra (tildeP σ ε μf Z c q p (update α (σ j) x)) g z = Φ x z
  | .nil, _, hnd, _ => absurd rfl (hnd 0)
  | .node .nil .nil, _, hnd, _ => absurd rfl (hnd 1)
  | .node .nil (.node a b), q, hnd, hinj => by
    have hs : (LegalCode.node LegalCode.nil (LegalCode.node a b)).size =
        (LegalCode.node a b).size + 1 := by simp [LegalCode.size]
    obtain ⟨j, hj1, hj2, hjadj, hreg⟩ := exists_regTo_tildeP hε Z p (.node a b) (q + 1)
      (nondom_rest hnd) (hinj.mono (Set.Ico_subset_Ico (by omega) (by omega)))
    refine ⟨j, by omega, by omega, ?_, ?_⟩
    · simp only [adjSet, Finset.mem_insert, not_or]; exact ⟨by omega, hjadj⟩
    · intro α g hg
      obtain ⟨Φ, hΦ, he⟩ := hreg α hg
      have hσ : σ q ≠ σ j := fun h => by
        have := hinj (by simp; omega) (by simp; omega) h; omega
      have hR := hΦ.volterra_left (continuous_piece58 (σ := σ) (ε := ε) (μf := μf) Z q p α)
      rw [show volterra (piece58 σ ε μf Z q p α) (fun _ => (0 : ℂ)) = fun _ => 0 by
        funext z; simp [volterra]] at hR
      refine ⟨fun x z => volterra (piece58 σ ε μf Z q p α) (Φ x) z, hR, fun x z hz => ?_⟩
      show volterra (kcomp (piece58 σ ε μf Z q p (update α (σ j) x))
        (tildeP σ ε μf Z (.node a b) (q + 1) p (update α (σ j) x))) g z = _
      rw [piece58_congr_vars Z q p (α' := α) (by rw [update_of_ne hσ]),
        volterra_kcomp (continuous_piece58 Z q p α) (continuous_tildeP Z p _ _ _) hg hz.1]
      exact volterra_congr _ (fun s hs => he x s hs) hz
  | .node (.node a b) .nil, q, _, hinj => by
    have hs : (LegalCode.node (LegalCode.node a b) LegalCode.nil).size =
        (LegalCode.node a b).size + 1 := by simp [LegalCode.size]
    refine ⟨q, le_rfl, by omega, not_mem_adjSet_self_of_inner, fun α g hg => ?_⟩
    have hin : ∀ x, tildeP σ ε μf Z (.node a b) (q + 1) p (update α (σ q) x) =
        tildeP σ ε μf Z (.node a b) (q + 1) p α := fun x =>
      tildeP_congr_vars Z p _ _ fun j h1 h2 => by
        have : σ j ≠ σ q := fun h => by
          have := hinj (by simp; omega) (by simp; omega) h; omega
        rw [update_of_ne this]
    have hTc := continuous_tildeP (σ := σ) (ε := ε) (μf := μf) Z p α (.node a b) (q + 1)
    refine ⟨fun x z => volterra (sandK (ε q) (μf q p) (tildeP σ ε μf Z (.node a b) (q + 1) p α) x) g z,
      regTo_sand (hε q) _ hTc hg, fun x z hz => ?_⟩
    show volterra (sandw (ε q) (σ q) (μf q) (tildeP σ ε μf Z (.node a b) (q + 1)) p
      (update α (σ q) x)) g z = _
    exact volterra_congr_tri (sandw_keqOn_sandK _ _ _ p α x (by rw [hin]; exact hTc) (hin x)) g hz
  | .node (.node a b) (.node c d), q, _, hinj => by
    have hs : (LegalCode.node (LegalCode.node a b) (LegalCode.node c d)).size =
        (LegalCode.node a b).size + (LegalCode.node c d).size + 1 := rfl
    refine ⟨q, le_rfl, by omega, not_mem_adjSet_self_of_inner, fun α g hg => ?_⟩
    have hin : ∀ x, tildeP σ ε μf Z (.node a b) (q + 1) p (update α (σ q) x) =
        tildeP σ ε μf Z (.node a b) (q + 1) p α := fun x =>
      tildeP_congr_vars Z p _ _ fun j h1 h2 => by
        have : σ j ≠ σ q := fun h => by
          have := hinj (by simp; omega) (by simp; omega) h; omega
        rw [update_of_ne this]
    have hrest : ∀ x, tildeP σ ε μf Z (.node c d) (q + (LegalCode.node a b).size + 1) p
        (update α (σ q) x) = tildeP σ ε μf Z (.node c d) (q + (LegalCode.node a b).size + 1) p α :=
      fun x => tildeP_congr_vars Z p _ _ fun j h1 h2 => by
        have : σ j ≠ σ q := fun h => by
          have := hinj (by simp; omega) (by simp; omega) h; omega
        rw [update_of_ne this]
    have hTc := continuous_tildeP (σ := σ) (ε := ε) (μf := μf) Z p α (.node a b) (q + 1)
    have hRc := continuous_tildeP (σ := σ) (ε := ε) (μf := μf) Z p α (.node c d)
      (q + (LegalCode.node a b).size + 1)
    refine ⟨fun x z => volterra (sandK (ε q) (μf q p) (tildeP σ ε μf Z (.node a b) (q + 1) p α) x)
      (volterra (tildeP σ ε μf Z (.node c d) (q + (LegalCode.node a b).size + 1) p α) g) z,
      regTo_sand (hε q) _ hTc (continuous_volterra hRc hg), fun x z hz => ?_⟩
    show volterra (kcomp (sandw (ε q) (σ q) (μf q) (tildeP σ ε μf Z (.node a b) (q + 1)) p
      (update α (σ q) x)) (tildeP σ ε μf Z (.node c d) (q + (LegalCode.node a b).size + 1) p
        (update α (σ q) x))) g z = _
    rw [hrest x, volterra_kcomp (continuous_sandw (by rw [hin]; exact hTc)) hRc hg hz.1]
    exact volterra_congr_tri (sandw_keqOn_sandK _ _ _ p α x (by rw [hin]; exact hTc) (hin x)) _ hz

end Spine

/-! ### The statement -/

section Statement

variable {P : Type*} [MeasurableSpace P] {V : Type} [DecidableEq V] {θ A : ℝ}
variable {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem image_Ico_sdiff_adj {c : LegalCode} {q : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ adjSet c q) :
    σ '' (Set.Ico q (q + c.size) \ (↑Z ∩ ↑(adjSet c q))) =
      ↑((Finset.Ico q (q + c.size) \ Z).image σ) := by
  rw [Finset.coe_image, Finset.coe_sdiff, Finset.coe_Ico,
    Set.inter_eq_left.2 (Finset.coe_subset.2 hZ)]

/-- **DH21 Lemma 7.2** (`regchaincancel2`, L1726–L1731). Let `c` be a legal partition (Catalan form,
pairs `q, …, q+m-1`) that is **not dominant**, with signs `ε_j = ±1`, distinct variables
`α_j = α (σ j)` and measurable `μ_j = μf j p`. For `Z` a set of adjacent pairs, let `Ĩ_Z` be the
operator of Lemma 5.10, `K̃ = Ĩ_Z(e^{πiλ₀s})(t)` with `t ∈ [0,1]`, and `W = {α_j : j ∉ Z}`. Then
`K̃ ∈ L¹(α[W])` (the other variables fixed at `α₀`) and `∫ K̃ dα[W] = 0`. -/
theorem regchaincancel2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ : ∀ j, Measurable (μf j)) {c : LegalCode} (hnd : ∀ m, c ≠ domCode m) {q : ℕ}
    (hinj : Set.InjOn σ (Set.Ico q (q + c.size))) {Z : Finset ℕ} (hZ : Z ⊆ adjSet c q) (p : P)
    (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    MInt ((Finset.Ico q (q + c.size) \ Z).image σ)
      (fun α => volterra (tildeP σ ε μf Z c q p α) (expF lam) t) α₀ ∧
    mint ((Finset.Ico q (q + c.size) \ Z).image σ)
      (fun α => volterra (tildeP σ ε μf Z c q p α) (expF lam) t) α₀ = 0 := by
  have hc : c ≠ .nil := hnd 0
  have hint : MInt ((Finset.Ico q (q + c.size) \ Z).image σ)
      (fun α => volterra (tildeP σ ε μf Z c q p α) (expF lam) t) α₀ := by
    have hM := (lemma510 (σ := σ) (ε := ε) (μf := μf) h0 h1 hA hε hμ hc hinj).2.2 Z
    rw [image_Ico_sdiff_adj hZ] at hM
    exact mJR_mInt_volterra hM h0 p lam ht α₀
  refine ⟨hint, ?_⟩
  obtain ⟨j, hj1, hj2, hjadj, hreg⟩ := exists_regTo_tildeP (μf := μf) hε Z p c q hnd hinj
  have hjs : j ∈ Finset.Ico q (q + c.size) \ Z :=
    Finset.mem_sdiff.2 ⟨by simp; omega, fun h => hjadj (hZ h)⟩
  have hinjs : Set.InjOn σ ↑(Finset.Ico q (q + c.size) \ Z) :=
    hinj.mono fun i hi => by
      have := (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1; simpa using this
  obtain ⟨hW, hv⟩ := image_erase_union hjs hinjs
  rw [hW] at hint ⊢
  refine mint_eq_zero_of_peel hv hint fun α hi => ?_
  obtain ⟨Φ, hΦ, he⟩ := hreg α (continuous_expF lam)
  have e : (fun x : ℝ => volterra (tildeP σ ε μf Z c q p (update α (σ j) x)) (expF lam) t) =
      fun x => Φ x t := funext fun x => he x t ht
  rw [e] at hi ⊢
  exact hΦ.integral_eq ht hi

end Statement

end WaveTurbulence.Cancel
