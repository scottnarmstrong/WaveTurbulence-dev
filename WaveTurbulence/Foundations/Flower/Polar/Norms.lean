/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.PhiStep
public import WaveTurbulence.Foundations.Spine.EvalBound
public import WaveTurbulence.Foundations.Spine.SNormOps
/-! # FL-POLAR: the pair-type norm invariant under the perturbation `g ↦ g + μ · polForm g`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

variable {w d : ℕ}

/-- `1` if the tree `j` meets exactly one of the two trees of the pair type `(j1, j2)`, else `0`. -/
def tch (j j1 j2 : Fin w) : ℕ := if (j1 = j ↔ j2 = j) then 0 else 1

/-- The total weight cost of the applications `os` at the pair type `(j1, j2)`. -/
def wcnt (os : List (Fin w)) (j1 j2 : Fin w) : ℕ := (os.map fun j => tch j j1 j2).sum

/-- The applications of a round list: each tree is applied twice. -/
def apps : List (Fin w) → List (Fin w)
  | [] => []
  | j :: js => j :: j :: apps js

/-- The norm invariant: derivative order `A`, weight `B + wcnt os`, bound `u`, all pair types, layers `≤ p`. -/
def Adm (p A B : ℕ) (os : List (Fin w)) (u : ℝ) (g : TProf d w) : Prop :=
  ∀ q ≤ p, ∀ j1 j2, ContDiff ℝ A (g q j1 j2) ∧
    SNormR A (B + wcnt os j1 j2) (g q j1 j2) ≤ ENNReal.ofReal u

theorem wcnt_nil (j1 j2 : Fin w) : wcnt [] j1 j2 = 0 := by simp [wcnt]

theorem wcnt_cons (j : Fin w) (os : List (Fin w)) (j1 j2 : Fin w) :
    wcnt (j :: os) j1 j2 = tch j j1 j2 + wcnt os j1 j2 := by simp [wcnt]

theorem typeCoeff_eq_zero_of_tch (σ : ℝ) (j j1 j2 : Fin w) (h : tch j j1 j2 = 0) :
    typeCoeff σ j j1 j2 = 0 := by
  unfold tch at h
  unfold typeCoeff
  by_cases hi : (j1 = j ↔ j2 = j)
  · by_cases h1 : j1 = j
    · have h2 : j2 = j := hi.mp h1
      simp [h1, h2]
    · have h2 : ¬ j2 = j := fun h2 => h1 (hi.mpr h2)
      simp [h1, h2]
  · simp [hi] at h

theorem tch_eq_one_of_coeff_ne (σ : ℝ) (j j1 j2 : Fin w) (h : typeCoeff σ j j1 j2 ≠ 0) :
    tch j j1 j2 = 1 := by
  by_cases hi : (j1 = j ↔ j2 = j)
  · exfalso
    exact h (typeCoeff_eq_zero_of_tch σ j j1 j2 (by unfold tch; simp [hi]))
  · unfold tch; simp [hi]

theorem abs_typeCoeff_le (σ : ℝ) (hσ : |σ| ≤ 1) (j j1 j2 : Fin w) : |typeCoeff σ j j1 j2| ≤ 1 := by
  unfold typeCoeff
  rw [abs_mul]
  have : |((if j1 = j then (1 : ℝ) else 0) - (if j2 = j then (1 : ℝ) else 0))| ≤ 1 := by
    split_ifs <;> norm_num
  calc _ ≤ 1 * 1 := mul_le_mul hσ this (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem Adm.mono_cons {p A B : ℕ} {j : Fin w} {os : List (Fin w)} {u : ℝ} {g : TProf d w}
    (h : Adm p A B (j :: os) u g) (hu : 0 ≤ u) : Adm p A B os u g := by
  intro q hq j1 j2
  obtain ⟨h1, h2⟩ := h q hq j1 j2
  refine ⟨h1, ?_⟩
  refine SNormR_mono_bound le_rfl ?_ _ h1 u hu h2
  rw [wcnt_cons]; omega

theorem contDiff_polForm (σ : ℝ) (j j1 j2 : Fin w) (i : Fin d) (A : ℕ) (f : Mom d → ℝ)
    (hf : ContDiff ℝ A f) :
    ContDiff ℝ A (fun x : Mom d => typeCoeff σ j j1 j2 * x i * f x) := by
  have hx : ContDiff ℝ A (fun x : Mom d => x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact (contDiff_const.mul hx).mul hf

theorem Adm.step {p A B : ℕ} {j : Fin w} {os : List (Fin w)} {u : ℝ} {g : TProf d w}
    (h : Adm p A B (j :: os) u g) (hu : 0 ≤ u) (σ : ℝ) (hσ : |σ| ≤ 1) (i : Fin d) (μ μ0 : ℝ)
    (hμ : |μ| ≤ μ0) :
    Adm p A B os ((1 + μ0 * ((2 : ℝ) ^ A * (d : ℝ) ^ A)) * u)
      (TProf.perturb g (polForm σ j i g) μ) := by
  have hd : 1 ≤ d := Fin.pos i
  have hμ0 : 0 ≤ μ0 := (abs_nonneg _).trans hμ
  have hE : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A := by positivity
  intro q hq j1 j2
  obtain ⟨hcd, hn⟩ := h q hq j1 j2
  have hu' : 0 ≤ (1 + μ0 * ((2 : ℝ) ^ A * (d : ℝ) ^ A)) * u := by positivity
  by_cases hc : typeCoeff σ j j1 j2 = 0
  · have heq : TProf.perturb g (polForm σ j i g) μ q j1 j2 = g q j1 j2 := by
      funext x
      simp [TProf.perturb, polForm, hc]
    rw [heq]
    refine ⟨hcd, ?_⟩
    have h1 := SNormR_mono_bound (A := A) (B := B + wcnt (j :: os) j1 j2) (A' := A)
      (B' := B + wcnt os j1 j2) le_rfl (by rw [wcnt_cons]; omega) _ hcd u hu hn
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hμ0 hE]
  · have ht := tch_eq_one_of_coeff_ne σ j j1 j2 hc
    have hw : B + wcnt (j :: os) j1 j2 = (B + wcnt os j1 j2) + 1 := by
      rw [wcnt_cons, ht]; omega
    rw [hw] at hn
    have hg1 : SNormR A (B + wcnt os j1 j2) (g q j1 j2) ≤ ENNReal.ofReal u :=
      SNormR_mono_bound le_rfl (Nat.le_succ _) _ hcd u hu hn
    have hform := SNormR_coord_mul_le (A := A) (B := B + wcnt os j1 j2) hd i (typeCoeff σ j j1 j2)
      (abs_typeCoeff_le σ hσ j j1 j2) (g q j1 j2) hcd u hu hn
    have hfc := contDiff_polForm σ j j1 j2 i A _ hcd
    refine ⟨hcd.add (contDiff_const.mul hfc), ?_⟩
    have hsum := SNormR_add_smul_le (A := A) (B := B + wcnt os j1 j2) (g q j1 j2)
      (fun x => typeCoeff σ j j1 j2 * x i * g q j1 j2 x) μ hcd hfc u ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) hu
      (by positivity) hg1 hform
    refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    have : |μ| * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) ≤ μ0 * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) :=
      mul_le_mul_of_nonneg_right hμ (by positivity)
    nlinarith

end WaveTurbulence.Flower.Polar
