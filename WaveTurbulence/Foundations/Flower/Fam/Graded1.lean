/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Main
/-! # FL-FAM: the weight-graded polarization step.  Besides `Adm` (the high weight bound `u`, which
degrades by `1 + ε` per step), we track the low weight bound `lo`, which grows only by `ε u` per step. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Finset LGSpine WaveTurbulence.Flower.Polar

variable {w d : ℕ}

/-- The low-weight invariant: weight exponent `B` exactly, bound `lo`. -/
def Lo (p A B : ℕ) (lo : ℝ) (g : TProf d w) : Prop :=
  ∀ q ≤ p, ∀ j1 j2, SNormR A B (g q j1 j2) ≤ ENNReal.ofReal lo

theorem Lo.step {p A B : ℕ} {j : Fin w} {os : List (Fin w)} {u lo : ℝ} {g : TProf d w}
    (h : Adm p A B (j :: os) u g) (hl : Lo p A B lo g) (hu : 0 ≤ u) (hlo : 0 ≤ lo)
    (σ : ℝ) (hσ : |σ| ≤ 1) (i : Fin d) (μ μ0 : ℝ) (hμ : |μ| ≤ μ0) :
    Lo p A B (lo + μ0 * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u))
      (TProf.perturb g (polForm σ j i g) μ) := by
  have hd : 1 ≤ d := Fin.pos i
  have hμ0 : 0 ≤ μ0 := (abs_nonneg _).trans hμ
  have hE : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A * u := by positivity
  intro q hq j1 j2
  obtain ⟨hcd, hn⟩ := h q hq j1 j2
  by_cases hc : typeCoeff σ j j1 j2 = 0
  · have heq : TProf.perturb g (polForm σ j i g) μ q j1 j2 = g q j1 j2 := by
      funext x
      simp [TProf.perturb, polForm, hc]
    rw [heq]
    refine (hl q hq j1 j2).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hμ0 hE]
  · have ht := tch_eq_one_of_coeff_ne σ j j1 j2 hc
    have hw : B + wcnt (j :: os) j1 j2 = (B + wcnt os j1 j2) + 1 := by
      rw [wcnt_cons, ht]; omega
    rw [hw] at hn
    have hn1 : SNormR A (B + 1) (g q j1 j2) ≤ ENNReal.ofReal u :=
      SNormR_mono_bound le_rfl (by omega) _ hcd u hu hn
    have hform := SNormR_coord_mul_le (A := A) (B := B) hd i (typeCoeff σ j j1 j2)
      (abs_typeCoeff_le σ hσ j j1 j2) (g q j1 j2) hcd u hu hn1
    have hfc := contDiff_polForm σ j j1 j2 i A _ hcd
    have hsum := SNormR_add_smul_le (A := A) (B := B) (g q j1 j2)
      (fun x => typeCoeff σ j j1 j2 * x i * g q j1 j2 x) μ hcd hfc lo
      ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) hlo hE (hl q hq j1 j2) hform
    refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    have : |μ| * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) ≤ μ0 * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) :=
      mul_le_mul_of_nonneg_right hμ hE
    linarith

theorem Lo.pert_step {p A B : ℕ} {j : Fin w} {os : List (Fin w)} {u lo : ℝ} {g : TProf d w}
    (h : Adm p A B (j :: os) u g) (hl : Lo p A B lo g) (hu : 0 ≤ u) (hlo : 0 ≤ lo) (i : Fin d)
    (lam : ℝ) (hlam : 0 < lam) (M m : ℕ) (hm : m ∈ range (2 * M + 1)) :
    Lo p A B (lo + lam * M * ((2 : ℝ) ^ A * (d : ℝ) ^ A) * u) (pert j i g lam M m) := by
  have hm' : (m : ℝ) ≤ 2 * M := by
    have := mem_range.mp hm
    have : m ≤ 2 * M := by omega
    exact_mod_cast this
  have habs : |lam * ((m : ℝ) - M)| ≤ lam * M := by
    rw [abs_mul, abs_of_pos hlam]
    refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hlam.le
  have hσ : |((-1 : ℝ) ^ (j : ℕ))| ≤ 1 := by simp
  have := Lo.step h hl hu hlo _ hσ i _ _ habs
  have e : lo + lam * M * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) =
      lo + lam * M * ((2 : ℝ) ^ A * (d : ℝ) ^ A) * u := by ring
  rw [e] at this
  exact this

end WaveTurbulence.Flower.Fam
