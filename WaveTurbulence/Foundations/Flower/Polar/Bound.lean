/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Iterate
/-! # FL-POLAR: the bound for `(1 + |x|^2)^r · Phi` by induction on the rounds. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

variable {w d : ℕ}

theorem triple_sum_norm_le (a : ℕ → ℝ) (R : Finset ℕ) (F : Fin d → ℕ → ℕ → ℂ) (Y T1 : ℝ)
    (hY : 0 ≤ Y) (hT : ∑ m ∈ R, |a m| ≤ T1) (hF : ∀ i, ∀ m ∈ R, ∀ m' ∈ R, ‖F i m m'‖ ≤ Y) :
    ‖∑ i : Fin d, ∑ m ∈ R, ∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ ≤
      d * T1 ^ 2 * Y := by
  have hT0 : 0 ≤ T1 := (Finset.sum_nonneg fun m _ => abs_nonneg _).trans hT
  have h1 : ∀ i : Fin d, ‖∑ m ∈ R, ∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ ≤
      (∑ m ∈ R, |a m|) * (∑ m' ∈ R, |a m'|) * Y := by
    intro i
    calc _ ≤ ∑ m ∈ R, ‖∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ R, ∑ m' ∈ R, ‖((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ :=
          sum_le_sum fun m _ => norm_sum_le _ _
      _ ≤ ∑ m ∈ R, ∑ m' ∈ R, |a m| * |a m'| * Y := by
          refine sum_le_sum fun m hm => sum_le_sum fun m' hm' => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hF i m hm m' hm') (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
  calc _ ≤ ∑ i : Fin d, ‖∑ m ∈ R, ∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (∑ m ∈ R, |a m|) * (∑ m' ∈ R, |a m'|) * Y := sum_le_sum fun i _ => h1 i
    _ = d * ((∑ m ∈ R, |a m|) * (∑ m' ∈ R, |a m'|)) * Y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ d * (T1 * T1) * Y := by
        have hs : 0 ≤ ∑ m ∈ R, |a m| := Finset.sum_nonneg fun m _ => abs_nonneg _
        gcongr
    _ = _ := by ring

variable (P : WTParams) (hL : 1 ≤ P.L) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
  (dagger : Option (Fin w → Fin 3 → Mom P.d))
  (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (hW : ∀ LG k, |W LG k| ≤ 1)
  (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

include hL hW in
theorem round_bound (A B : ℕ) (hB : P.d + 1 ≤ B) (M : ℕ) (hM : 1 ≤ M) (hMw : 2 * N + w ≤ 2 * M)
    (lam : ℝ) (hlam : 0 < lam) (b X T1 : ℝ)
    (hT1 : ∑ m ∈ range (2 * M + 1), |CentralDiff.cw M m / lam| ≤ T1)
    (hcore : ∀ g : TProf P.d w, Adm p A B [] (2 * b) g →
      ‖Phi P p N kind pat dagger W ζ t s n n' g‖ ≤ X) :
    ∀ (js : List (Fin w)) (g : TProf P.d w) (u : ℝ), 0 ≤ u → Adm p A B (apps js) u g →
      u * (1 + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A)) ^ (2 * js.length) ≤ 2 * b →
      ‖(((1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2) ^ js.length : ℝ) : ℂ) *
          Phi P p N kind pat dagger W ζ t s n n' g‖ ≤ (1 + P.d * T1 ^ 2) ^ js.length * X := by
  intro js
  induction js with
  | nil =>
    intro g u hu hA hle
    have hA' : Adm p A B [] (2 * b) g := hA.mono_u (by simpa [apps] using hle)
    simpa using hcore g hA'
  | cons j js' ih =>
    intro g u hu hA hle
    set ε : ℝ := lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A) with hε
    have hε0 : 0 ≤ ε := by positivity
    have hA' : Adm p A B (j :: j :: apps js') u g := hA
    have hu1 : 0 ≤ (1 + ε) * u := by positivity
    have hu2 : 0 ≤ (1 + ε) * ((1 + ε) * u) := by positivity
    have hid := round_identity P hL p N kind pat dagger W hW ζ t s n n' A B hB M hM hMw lam hlam j
      (apps js') u hu g hA'
    set c : ℝ := 1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2 with hc
    have hc0 : 0 ≤ c := by positivity
    set K : ℝ := 1 + P.d * T1 ^ 2 with hK
    have hpow : (1 + ε) ^ (2 * js'.length) ≤ (1 + ε) ^ (2 * (j :: js').length) :=
      pow_le_pow_right₀ (by linarith) (by simp)
    have hleg : u * (1 + ε) ^ (2 * js'.length) ≤ 2 * b := by
      refine le_trans (mul_le_mul_of_nonneg_left hpow hu) hle
    have hAg : Adm p A B (apps js') u g := (hA'.mono_cons hu).mono_cons hu
    have hg0 := ih g u hu hAg hleg
    have hT10 : 0 ≤ T1 := (Finset.sum_nonneg fun m _ => abs_nonneg _).trans hT1
    have hK0 : 0 ≤ K := by positivity
    have hY : 0 ≤ K ^ js'.length * X := (norm_nonneg _).trans hg0
    have hmid : ∀ i : Fin P.d, ∀ m ∈ range (2 * M + 1), Adm p A B (j :: apps js') ((1 + ε) * u)
        (pert j i g lam M m) := fun i m hm => hA'.pert_step hu i lam hlam M m hm
    have hfin : ∀ i : Fin P.d, ∀ m ∈ range (2 * M + 1), ∀ m' ∈ range (2 * M + 1),
        ‖((c ^ js'.length : ℝ) : ℂ) *
          Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m')‖ ≤
        K ^ js'.length * X := by
      intro i m hm m' hm'
      refine ih _ ((1 + ε) * ((1 + ε) * u)) hu2 ((hmid i m hm).pert_step hu1 i lam hlam M m' hm') ?_
      calc (1 + ε) * ((1 + ε) * u) * (1 + ε) ^ (2 * js'.length)
          = u * (1 + ε) ^ (2 * (js'.length + 1)) := by ring
        _ ≤ 2 * b := by simpa using hle
    have hexp : (((c ^ (js'.length + 1) : ℝ)) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' g =
        ((c ^ js'.length : ℝ) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g +
        ∑ i : Fin P.d, ∑ m ∈ range (2 * M + 1), ∑ m' ∈ range (2 * M + 1),
          ((CentralDiff.cw M m / lam : ℝ) : ℂ) * ((CentralDiff.cw M m' / lam : ℝ) : ℂ) *
            (((c ^ js'.length : ℝ) : ℂ) *
              Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m')) := by
      have h1 : (((c ^ (js'.length + 1) : ℝ)) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g =
          ((c ^ js'.length : ℝ) : ℂ) * ((c : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g) := by
        push_cast; ring
      rw [h1, hid, mul_add, Finset.mul_sum]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m' _ => ?_
      ring
    show ‖(((c ^ (js'.length + 1) : ℝ)) : ℂ) * _‖ ≤ K ^ (js'.length + 1) * X
    rw [hexp]
    have hsum := triple_sum_norm_le (d := P.d) (fun m => CentralDiff.cw M m / lam) (range (2 * M + 1))
      (fun i m m' => ((c ^ js'.length : ℝ) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m'))
      (K ^ js'.length * X) T1 hY hT1 hfin
    calc _ ≤ ‖((c ^ js'.length : ℝ) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g‖ + _ := norm_add_le _ _
      _ ≤ K ^ js'.length * X + P.d * T1 ^ 2 * (K ^ js'.length * X) := add_le_add hg0 hsum
      _ = K ^ (js'.length + 1) * X := by rw [hK]; ring

end WaveTurbulence.Flower.Polar
