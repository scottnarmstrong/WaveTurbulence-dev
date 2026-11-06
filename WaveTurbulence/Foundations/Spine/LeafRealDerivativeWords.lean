/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafInputDerivative
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeNorm
/-! Real coordinate words agree with the exact complex coordinate derivative convention. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open NormBridgeScratch

noncomputable def realWordD {d : ℕ} : List (Fin d) → (Mom d → ℝ) → Mom d → ℝ
  | [], H => H
  | j :: word, H => realPartialMom j (realWordD word H)

theorem contDiff_realWordD {d : ℕ} (word : List (Fin d)) (A : ℕ) (H : Mom d → ℝ)
    (hH : ContDiff ℝ (A + word.length : ℕ) H) : ContDiff ℝ A (realWordD word H) := by
  induction word generalizing A with
  | nil => exact hH
  | cons j word ih =>
    have hh : ContDiff ℝ ((A + 1) + word.length : ℕ) H := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hH
    exact contDiff_realPartialMom j _ (ih (A + 1) hh)

theorem ofReal_realWordD {d : ℕ} (word : List (Fin d)) (H : Mom d → ℝ)
    (hH : ContDiff ℝ word.length H) :
    (fun x => (realWordD word H x : ℂ)) = wordD word (fun x => (H x : ℂ)) := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    have hbase : ContDiff ℝ word.length H := hH.of_le (by exact_mod_cast Nat.le_succ word.length)
    have hh : ContDiff ℝ (1 + word.length : ℕ) H := by
      simpa only [List.length_cons, Nat.add_comm] using hH
    have hdiff := (contDiff_realWordD word 1 H hh).differentiable (by norm_num)
    funext x
    change (realPartialMom j (realWordD word H) x : ℂ) =
      partialMom j (wordD word (fun x => (H x : ℂ))) x
    rw [← ih hbase]
    exact (partialMom_ofReal j (realWordD word H) x (hdiff x)).symm

theorem SNormR_realWordD_bound {d A B : ℕ} (hd : 1 ≤ d) (word : List (Fin d))
    (H : Mom d → ℝ) (hc : ContDiff ℝ (A + word.length : ℕ) H)
    (C : ℝ) (hC : 0 ≤ C) (hb : SNormR (A + word.length) B H ≤ ENNReal.ofReal C) :
    SNormR A B (realWordD word H) ≤ ENNReal.ofReal ((d : ℝ) ^ (A + word.length) * C) := by
  have hcomplex := Complex.ofRealCLM.contDiff.comp hc
  have hh := SNorm_wordD_bound hd word (fun x => (H x : ℂ)) hcomplex C hC hb
  unfold SNormR
  rw [ofReal_realWordD word H (hc.of_le (by exact_mod_cast Nat.le_add_left word.length A))]
  exact hh

end WaveTurbulence.LGSpine
