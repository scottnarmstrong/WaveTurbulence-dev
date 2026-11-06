/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Prod3
public import WaveTurbulence.Foundations.Layered.RestrictionCalculus

/-!
# The product estimate for restriction norms with momentum derivatives (PL23-30D)

As at order zero (`Layered.mixedRestrictionNorm00_mul_le`): the second factor of an extension product is replaced
by its continuous representative, which has the same norm and agrees with a continuous `h₂` on `closure (interior ℬ)`.

* `mixedFourierNorm_rep_eq`;
* `restr_mul_le`, `restr_mul_le_real` (for `K = univ`).
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

/-- The continuous representative has the same norm. -/
theorem mixedFourierNorm_rep_eq {θ : ℝ} (hθ : 0 ≤ θ) {Λ Λ₂ : ℕ} {G : (Fin r → ℝ) → Mom d → ℂ}
    (hG : mixedFourierNorm θ Λ Λ₂ G < ⊤) :
    mixedFourierNorm θ Λ Λ₂ (fun t k => rep (fun u => G u k) t) = mixedFourierNorm θ Λ Λ₂ G := by
  have hrep := fun k => rep_props hθ ((timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) G k).trans_lt hG)
  have hFT : ∀ ξ, mixedTimeFourier (fun t k => rep (fun u => G u k) t) ξ = mixedTimeFourier G ξ := by
    intro ξ
    funext k
    unfold mixedTimeFourier
    exact congrFun (hrep k).2.2.2.1 ξ
  have hadm := admissible_of_lt_top hG
  have hadm' : MixedFourierAdmissible Λ (fun t k => rep (fun u => G u k) t) := by
    refine ⟨fun k => (hrep k).2.2.1, ?_⟩
    rcases hadm.2 with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [hFT] using h)
  rw [mixedFourierNorm_eq_iSup hadm', mixedFourierNorm_eq_iSup hadm]
  simp only [hFT]

theorem restr_eq_iInf_finite {θ : ℝ} {Λ Λ₂ : ℕ} (B : Set (Fin r → ℝ)) (K : Set (Mom d))
    (h : (Fin r → ℝ) → Mom d → ℂ) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => h t k) =
      ⨅ G : {G : (Fin r → ℝ) → Mom d → ℂ // (∀ t ∈ B, ∀ k ∈ K, G t k = h t k) ∧
          mixedFourierNorm θ Λ Λ₂ G < ⊤}, mixedFourierNorm θ Λ Λ₂ G.1 := by
  rw [mixedRestrictionNorm_eq_agreement]
  apply le_antisymm
  · exact le_iInf fun G => iInf₂_le G.1 G.2.1
  · refine le_iInf₂ fun G hG => ?_
    by_cases hN : mixedFourierNorm θ Λ Λ₂ G < ⊤
    · exact iInf_le_of_le ⟨G, hG, hN⟩ le_rfl
    · rw [not_lt, top_le_iff] at hN
      rw [hN]
      exact le_top

theorem nonempty_finiteExt {θ : ℝ} {Λ Λ₂ : ℕ} {B : Set (Fin r → ℝ)} {K : Set (Mom d)}
    {h : (Fin r → ℝ) → Mom d → ℂ} (hfin : mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => h t k) < ⊤) :
    Nonempty {G : (Fin r → ℝ) → Mom d → ℂ // (∀ t ∈ B, ∀ k ∈ K, G t k = h t k) ∧
      mixedFourierNorm θ Λ Λ₂ G < ⊤} := by
  rw [mixedRestrictionNorm_eq_agreement] at hfin
  obtain ⟨G, hG⟩ := iInf_lt_iff.mp hfin
  obtain ⟨hGa, hGn⟩ := iInf_lt_iff.mp hG
  exact ⟨⟨G, hGa, hGn⟩⟩

/-- **The product estimate for restriction norms** (`K = univ`). -/
theorem restr_mul_le {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) (a b : ℕ)
    {B : Set (Fin r → ℝ)} (hB : ∀ t ∈ B, t ∈ closure (interior B)) (h₁ h₂ : (Fin r → ℝ) → Mom d → ℂ)
    (hc : ∀ k, Continuous fun t => h₂ t k)
    (hfin₁ : rN θ Λ a B h₁ < ⊤)
    (hfin₂ : rN θ Λ b B h₂ < ⊤) :
    rN θ Λ (a + b) B (fun t k => h₁ t k * h₂ t k) ≤
      ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (cLeib d Λ) *
        rN θ Λ a B h₁ *
        rN θ Λ b B h₂ := by
  have := nonempty_finiteExt hfin₁
  have := nonempty_finiteExt hfin₂
  rw [show rN θ Λ a B h₁ = _ from restr_eq_iInf_finite B Set.univ h₁,
    show rN θ Λ b B h₂ = _ from restr_eq_iInf_finite B Set.univ h₂]
  refine Layered.le_mul_iInf_mul_iInf (fun G => G.2.2.ne) (fun G => G.2.2.ne)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) fun G₁ G₂ => ?_
  have hslice : ∀ k, timeFourierNorm θ (fun u => G₂.1 u k) < ⊤ := fun k =>
    (timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := b) G₂.1 k).trans_lt G₂.2.2
  let G₂' : (Fin r → ℝ) → Mom d → ℂ := fun t k => rep (fun u => G₂.1 u k) t
  have hcont : ∀ k, Continuous fun t => G₂' t k := fun k => (rep_props hθ (hslice k)).1
  have hN : mixedFourierNorm θ Λ b G₂' = mixedFourierNorm θ Λ b G₂.1 := mixedFourierNorm_rep_eq hθ G₂.2.2
  have hagree : ∀ t ∈ B, ∀ k ∈ (Set.univ : Set (Mom d)), G₂' t k = h₂ t k := fun t ht k hk =>
    rep_eq_of_mem_closure_interior hθ (hslice k) (fun u hu => G₂.2.1 u hu k hk) (hc k) (hB t ht)
  refine (rN_eq_agreement B (fun t k => h₁ t k * h₂ t k)).le.trans ?_
  refine (iInf₂_le (fun t k => G₁.1 t k * G₂' t k) fun t ht k hk => by
    show G₁.1 t k * G₂' t k = h₁ t k * h₂ t k
    rw [G₁.2.1 t ht k hk, hagree t ht k hk]).trans ?_
  rw [← hN]
  exact mixedFourierNorm_mul_le hΛ hd hθ a b hcont G₁.2.2 (hN ▸ G₂.2.2)

/-- The product estimate with real bounds. -/
theorem restr_mul_le_real {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) (a b : ℕ)
    {B : Set (Fin r → ℝ)} (hB : ∀ t ∈ B, t ∈ closure (interior B)) (h₁ h₂ : (Fin r → ℝ) → Mom d → ℂ)
    (hc : ∀ k, Continuous fun t => h₂ t k) {e₁ e₂ : ℝ} (he₁ : 0 ≤ e₁) (_he₂ : 0 ≤ e₂)
    (h1 : rN θ Λ a B h₁ ≤ ENNReal.ofReal e₁)
    (h2 : rN θ Λ b B h₂ ≤ ENNReal.ofReal e₂) :
    rN θ Λ (a + b) B (fun t k => h₁ t k * h₂ t k) ≤
      ENNReal.ofReal (2 ^ θ * cLeib d Λ * e₁ * e₂) := by
  refine (restr_mul_le hΛ hd hθ a b hB h₁ h₂ hc (h1.trans_lt ENNReal.ofReal_lt_top)
    (h2.trans_lt ENNReal.ofReal_lt_top)).trans ?_
  have h2θ : (0 : ℝ) ≤ 2 ^ θ := Real.rpow_nonneg (by norm_num) θ
  calc ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (cLeib d Λ) *
        rN θ Λ a B h₁ *
        rN θ Λ b B h₂
      ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (cLeib d Λ) * ENNReal.ofReal e₁ * ENNReal.ofReal e₂ := by
        gcongr
    _ = ENNReal.ofReal (2 ^ θ * cLeib d Λ * e₁ * e₂) := by
        rw [← ENNReal.ofReal_mul h2θ, ← ENNReal.ofReal_mul (mul_nonneg h2θ (cLeib_nonneg d Λ)),
          ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h2θ (cLeib_nonneg d Λ)) he₁)]

end WaveTurbulence.PL2330
