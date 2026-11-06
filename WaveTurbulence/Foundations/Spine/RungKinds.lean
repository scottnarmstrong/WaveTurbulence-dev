/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungBallTime
/-! # Rung weight kinds (S3b LADDER-DECAY): swap, and the trivial kind -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory Set WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d : ℕ}

/-- Exchange of the two rung variables. -/
def swapPt (p : Pt d) : Pt d := (p.2, p.1)

/-- The exchange as an additive map. -/
def swapHom : Pt d →+ Pt d := AddMonoidHom.prod (AddMonoidHom.snd _ _) (AddMonoidHom.fst _ _)

lemma swapPt_injective : Function.Injective (swapPt (d := d)) := fun p q h => by
  have h1 := congrArg swapPt h
  simpa [swapPt] using h1

lemma swapPt_swapPt (p : Pt d) : swapPt (swapPt p) = p := rfl

lemma bil_swap (L : ℝ) (p : Pt d) : bil L (swapPt p) = bil L p := by
  unfold bil swapPt; exact real_inner_comm _ _

/-- The rung sum is invariant under exchanging the variables (with all data exchanged). -/
theorem rungSum_swap (L c : ℝ) (w : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    rungSum L c w S lam ν t =
      rungSum L c (fun q => w (swapPt q)) (S.image swapPt) (lam.comp swapHom) (ν.comp swapHom) t := by
  unfold rungSum
  rw [Finset.sum_image (fun p _ q _ h => swapPt_injective h)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have h1 : swapHom (swapPt p) = p := rfl
  simp only [swapPt_swapPt, AddMonoidHom.comp_apply, h1, bil_swap]

/-- Rung weights with an arbitrary bounded factor in the second variable. -/
noncomputable def ballWY (L : ℝ) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ) (p : Pt d) : ℂ :=
  ι p.2 * cutW L a b p

lemma ballWY_swap (L : ℝ) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ) (q : Pt d) :
    ballWY L a b ι (swapPt q) = ballW L b a ι q := by
  unfold ballWY ballW cutW swapPt
  simp only [Complex.ofReal_mul]
  ring

lemma image_swap_prod (A B : Finset (Fin d → ℤ)) : (A ×ˢ B).image swapPt = B ×ˢ A := by
  ext q
  simp only [Finset.mem_image, Finset.mem_product, swapPt]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨(q.2, q.1), ⟨h2, h1⟩, rfl⟩

theorem rungSum_ballY_eq (L c : ℝ) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ) (I : Fin d → Finset ℤ)
    (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    rungSum L c (ballWY L a b ι) (byBox L a ×ˢ Fintype.piFinset I) lam ν t =
      rungSum L c (ballW L b a ι) (Fintype.piFinset I ×ˢ byBox L a) (lam.comp swapHom)
        (ν.comp swapHom) t := by
  rw [rungSum_swap, image_swap_prod]
  congr 1
  funext q
  exact ballWY_swap L a b ι q

/-- **The second-variable-sharp rung** (same statement as `rung_ball_time`, with `a`, `b` exchanged). -/
theorem rung_ballY_time (hd : 3 ≤ d) : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (a b : Fin d → ℝ)
    (ι : (Fin d → ℤ) → ℂ), (∀ x, ‖ι x‖ ≤ 1) → ∀ (I : Fin d → Finset ℤ),
    (∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I) → ∀ (lam ν : Pt d →+ ℝ) (c l u v w Wd Kc : ℝ),
    0 < c → l ≤ u → v ≤ w → (∀ t ∈ Icc v w, -Wd ≤ 16 * c * (l - t) ∧ 16 * c * (u - t) ≤ Wd) →
    0 ≤ Kc → (∀ i, ((I i).card : ℝ) ≤ Kc ∧ ∀ n ∈ I i, ∀ n' ∈ I i, |(n : ℝ) - n'| ≤ Kc) →
    Kc ≤ 4 * L → 2 * (Wd + 1) * Kc ≤ (4 * L) ^ 2 →
    (∫ t in Icc v w, ∫ s in Icc l u,
        ‖rungSum L c (ballWY L a b ι) (byBox L a ×ˢ Fintype.piFinset I) lam ν (s, t)‖) ≤
      (w - v) * ((u - l) * (C0 * (4 * L)) ^ d * 1 +
        (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1)))) ∧
    (u ≤ v ∨ w ≤ l →
      (∫ t in Icc v w, ∫ s in Icc l u,
        ‖rungSum L c (ballWY L a b ι) (byBox L a ×ˢ Fintype.piFinset I) lam ν (s, t)‖) ≤
      (w - v) * ((u - l) * (C0 * (4 * L)) ^ d * 1) +
        (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1))) * (16 * c)⁻¹) := by
  obtain ⟨C0, hC0, h⟩ := rung_ball_time hd
  refine ⟨C0, hC0, ?_⟩
  intro L hL a b ι hι I hQ lam ν c l u v w Wd Kc hc hlu hvw hwin hKc hI hKL hLs
  have := h hL b a ι hι I hQ (lam.comp swapHom) (ν.comp swapHom) c l u v w Wd Kc hc hlu hvw hwin
    hKc hI hKL hLs
  simp only [rungSum_ballY_eq]
  exact this

/-- **The trivial kind**: a weight supported in a finite set of at most `N` points. -/
theorem rung_trivial (L c : ℝ) (T : Finset (Pt d)) (w : Pt d → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1)
    (lam ν : Pt d →+ ℝ) (l u v w' : ℝ) (hlu : l ≤ u) (hvw : v ≤ w') :
    (∫ t in Icc v w', ∫ s in Icc l u, ‖rungSum L c w T lam ν (s, t)‖) ≤
      (w' - v) * ((u - l) * T.card) := by
  have hpt : ∀ s t : ℝ, ‖rungSum L c w T lam ν (s, t)‖ ≤ T.card := by
    intro s t
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ T, ‖w p * e (c * ((s, t).2 - (s, t).1) * bil L p + ((s, t).2 * lam p + ν p))‖
        ≤ ∑ _p ∈ T, (1 : ℝ) := Finset.sum_le_sum (fun p _ => by rw [norm_mul, norm_e, mul_one]; exact hw p)
      _ = T.card := by simp
  have hin : ∀ t : ℝ, (∫ s in Icc l u, ‖rungSum L c w T lam ν (s, t)‖) ≤ (u - l) * T.card := by
    intro t
    have hB : (∫ _s in Icc l u, (T.card : ℝ)) = (u - l) * T.card := by
      simp [Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hlu)]
    rw [← hB]
    refine integral_mono_of_nonneg (ae_of_all _ (fun s => norm_nonneg _))
      (integrableOn_const (μ := volume) (s := Icc l u) (by simp [Real.volume_Icc])) ?_
    exact ae_of_all _ (fun s => hpt s t)
  exact outer_same hvw (fun t => integral_nonneg (fun s => norm_nonneg _)) (fun t _ => hin t)

end WaveTurbulence.LadderDecay
